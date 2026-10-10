import OAI.Analysis.KadisonKastler.StateCommutatorAlgebra
import OAI.Analysis.KadisonKastler.WOTVectorLowerSemicontinuity
import Mathlib.Analysis.Convex.Topology

namespace OAI

/-! # Quantitative gaps from weakly closed state-central unitary orbits

This is the vector estimate in Haagerup, Acta Math. 158 (1987), Lemma 3.2.
The scalar orbit-hull hypothesis is the consequence of triviality of the
bicentralizer in Proposition 1.3.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def stateUnitaryOrbit (ξ : H) (a : Algebra M) (δ : ℝ) : Set (H →WOT[ℂ] H) :=
  {T | ∃ u : unitary (Algebra M), ‖vectorStateCommutator ξ u.val‖ ≤ δ ∧
    T = ContinuousLinearMapWOT.ofCLM (star u.val*a*u.val).val}

/-- WOT-closed convex hulls cannot cross a closed vector-distance ball
unless one of the generating conjugates already does. -/
theorem exists_unitary_gap_of_state_orbit_hull
    (ξ : H) (a : Algebra M) (δ r : ℝ) (hr : 0 ≤ r)
    (T : H →WOT[ℂ] H) (hT : T ∈ closedConvexHull ℝ (stateUnitaryOrbit ξ a δ))
    (hgap : r < ‖T ξ-a.val ξ‖) :
    ∃ u : unitary (Algebra M), ‖vectorStateCommutator ξ u.val‖ ≤ δ ∧
      r < ‖(u.val*a-a*u.val).val ξ‖ := by
  classical
  by_contra hn
  push Not at hn
  let C : Set (H →WOT[ℂ] H) := {S | S ξ ∈ Metric.closedBall (a.val ξ) r}
  have hC : IsClosed C := by
    have he : C = {S : H →WOT[ℂ] H | ‖S ξ-a.val ξ‖^2 ≤ r^2} := by
      ext S
      change dist (S ξ) (a.val ξ) ≤ r ↔ _
      rw [dist_eq_norm]
      exact (sq_le_sq₀ (norm_nonneg _) hr).symm
    rw [he]
    exact (wot_vector_sqDistance_lowerSemicontinuous ξ (a.val ξ)).isClosed_preimage _
  have hc : Convex ℝ C := by
    let ev : (H →WOT[ℂ] H) →ₗ[ℝ] H :=
      { toFun := fun S => S ξ
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (convex_closedBall (a.val ξ) r).linear_preimage ev
  have hsub : stateUnitaryOrbit ξ a δ ⊆ C := by
    rintro S ⟨u,hu,rfl⟩
    change dist ((star u.val*a*u.val).val ξ) (a.val ξ) ≤ r
    rw [dist_eq_norm]
    have he : u.val.val ((star u.val*a*u.val).val ξ-a.val ξ) =
        -(u.val*a-a*u.val).val ξ := by
      change u.val.val (((star u.val*a*u.val).val-a.val) ξ) = _
      rw [← mul_apply_eq_comp]
      have ha : u.val*(star u.val*a*u.val-a) = -(u.val*a-a*u.val) := by
        rw [mul_sub,← mul_assoc,← mul_assoc,u.property.2,one_mul]
        abel
      exact congrArg (fun b : Algebra M => b.val ξ) ha
    have heq := Unitary.norm_map (ambientAlgebraUnitary u)
      ((star u.val*a*u.val).val ξ-a.val ξ)
    change ‖u.val.val ((star u.val*a*u.val).val ξ-a.val ξ)‖ = _ at heq
    rw [he,norm_neg] at heq
    exact heq.symm.trans_le (hn u hu)
  have hm := closedConvexHull_min hsub hc hC hT
  change dist (T ξ) (a.val ξ) ≤ r at hm
  rw [dist_eq_norm] at hm
  exact hgap.not_ge hm

theorem exists_unitary_gap_of_scalar_state_orbit_hull
    (ξ : H) (a : Algebra M) (ha : vectorFunctional (M := M) ξ a=0)
    (haξ : a.val ξ≠0) (δ c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (z : ℂ) (hz : ContinuousLinearMapWOT.ofCLM (z • (1 : H →L[ℂ] H)) ∈
      closedConvexHull ℝ (stateUnitaryOrbit ξ a δ)) :
    ∃ u : unitary (Algebra M), ‖vectorStateCommutator ξ u.val‖ ≤ δ ∧
      c*‖a.val ξ‖ < ‖(u.val*a-a*u.val).val ξ‖ := by
  apply exists_unitary_gap_of_state_orbit_hull ξ a δ (c*‖a.val ξ‖)
    (mul_nonneg hc (norm_nonneg _)) _ hz
  have horth : inner ℂ (z • ξ) (a.val ξ)=0 := by
    rw [inner_smul_left]
    change starRingEnd ℂ z * vectorFunctional (M := M) ξ a=0
    rw [ha,mul_zero]
  have hs := norm_sub_sq (𝕜 := ℂ) (z • ξ) (a.val ξ)
  rw [horth,map_zero] at hs
  have hn : 0 < ‖a.val ξ‖ := norm_pos_iff.mpr haξ
  have hle : ‖a.val ξ‖ ≤ ‖z • ξ-a.val ξ‖ := by
    nlinarith [sq_nonneg ‖z • ξ‖,norm_nonneg (z • ξ-a.val ξ)]
  exact (mul_lt_of_lt_one_left hn hc1).trans_le hle

end

end KadisonKastler

end OAI
