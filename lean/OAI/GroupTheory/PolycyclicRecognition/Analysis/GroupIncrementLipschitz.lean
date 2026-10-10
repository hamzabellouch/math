import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Group.Basic

namespace OAI

/-! # Local Lipschitz control from coordinates of group increments -/

namespace PolycyclicRecognition

open Set Filter
open scoped Topology NNReal

theorem locallyLipschitz_of_group_increments
    {V W G : Type*} [PseudoMetricSpace V] [PseudoMetricSpace W]
    [Group G] [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]
    (f : V → G) (χ : G → W) (hf : Continuous f)
    (C : ℝ≥0) (U : Set G) (hU : U ∈ 𝓝 (1 : G))
    (hχ : ∀ z ∈ U, dist (1 : G) z ≤ C * dist (χ 1) (χ z))
    (hF : ∀ x : V, ∃ K : ℝ≥0, ∃ A ∈ 𝓝 (x, x),
      LipschitzOnWith K (fun p : V × V => χ ((f p.1)⁻¹ * f p.2)) A) :
    LocallyLipschitz f := by
  intro x
  obtain ⟨K, A, hA, hFA⟩ := hF x
  have hinc : Continuous (fun p : V × V => (f p.1)⁻¹ * f p.2) :=
    (hf.comp continuous_fst).inv.mul (hf.comp continuous_snd)
  have hpre : (fun p : V × V => (f p.1)⁻¹ * f p.2) ⁻¹' U ∈ 𝓝 (x, x) :=
    hinc.continuousAt.preimage_mem_nhds (by simpa only [inv_mul_cancel] using hU)
  obtain ⟨A₁, hA₁, A₂, hA₂, hprod⟩ := mem_nhds_prod_iff.mp (inter_mem hA hpre)
  refine ⟨C * K, A₁ ∩ A₂, inter_mem hA₁ hA₂, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro a ha b hb
  have hab := hprod (show (a, b) ∈ A₁ ×ˢ A₂ from ⟨ha.1, hb.2⟩)
  have haa := hprod (show (a, a) ∈ A₁ ×ˢ A₂ from ⟨ha.1, ha.2⟩)
  have hcoord := hFA.dist_le_mul (x := (a, a)) (y := (a, b)) haa.1 hab.1
  simp only [inv_mul_cancel, Prod.dist_eq, dist_self, max_eq_right dist_nonneg] at hcoord
  calc
    dist (f a) (f b) = dist (1 : G) ((f a)⁻¹ * f b) := by
      simpa only [mul_one, mul_inv_cancel_left] using
        dist_mul_left (f a) 1 ((f a)⁻¹ * f b)
    _ ≤ C * dist (χ 1) (χ ((f a)⁻¹ * f b)) := hχ _ hab.2
    _ ≤ C * ((K : ℝ) * dist a b) := mul_le_mul_of_nonneg_left hcoord C.coe_nonneg
    _ = ↑(C * K) * dist a b := by simp only [NNReal.coe_mul, mul_assoc]

end PolycyclicRecognition

end OAI
