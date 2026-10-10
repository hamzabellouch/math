import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnitaryMautner
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentFlow

namespace OAI

/-! # Contracting flows give explicit contracted elements

Polynomial factors from a nilpotent Jordan correction decay under a negative
real weight. This produces the actual sequence required by `contractedBy`.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

theorem tendsto_contracted_nilpotent_flow
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [Nontrivial V]
    (N : V →L[ℝ] V) {c : ℕ} (hN : N ^ (c + 1) = 0) (v : V) :
    Tendsto (fun t : ℝ => Real.exp (-t) • (NormedSpace.exp (t • N)) v) atTop (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ => t ^ c * Real.exp (-t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, neg_one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (c : ℝ) 1 zero_lt_one
  have hs : Tendsto (fun t : ℝ => 1 + t) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
  have hp' : Tendsto (fun t : ℝ => (1 + t) ^ c * Real.exp (-t)) atTop (𝓝 0) := by
    have he (t : ℝ) : (1 + t) ^ c * Real.exp (-t) =
        Real.exp 1 * ((1 + t) ^ c * Real.exp (-(1 + t))) := by
      rw [← mul_assoc, mul_comm (Real.exp 1), mul_assoc, ← Real.exp_add]
      congr 2
      ring
    simpa only [Function.comp_def, he, mul_zero] using (hp.comp hs).const_mul (Real.exp 1)
  apply squeeze_zero_norm' (Filter.eventually_atTop.2 ⟨0, fun t ht =>
    norm_contracted_nilpotent_flow_le N hN v ht⟩)
  simpa only [mul_assoc, mul_zero, zero_mul] using
    (hp'.const_mul (((c : ℝ) + 1) * (1 + ‖N‖) ^ c)).mul_const ‖v‖

theorem contractedBy_of_continuous_flow
    {G V : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup V] (H : Subgroup G)
    (Exp : V → G) (hExp : Continuous Exp) (hzero : Exp 0 = 1)
    (d : ℝ → H) (T : ℝ → V → V)
    (hconj : ∀ v t, 0 ≤ t → Exp v = (d t : G) * Exp (T t v) * (d t : G)⁻¹)
    (hT : ∀ v, Tendsto (fun t => T t v) atTop (𝓝 0)) (v : V) :
    Exp v ∈ contractedBy H := by
  refine ⟨fun n => d n, ?_⟩
  have he (n : ℕ) : (d n : G)⁻¹ * Exp v * d n = Exp (T n v) := by
    rw [hconj v n (Nat.cast_nonneg n)]
    group
  simp_rw [he]
  rw [← hzero]
  exact (hExp.tendsto 0).comp ((hT v).comp tendsto_natCast_atTop_atTop)

end PolycyclicRecognition

end

end OAI
