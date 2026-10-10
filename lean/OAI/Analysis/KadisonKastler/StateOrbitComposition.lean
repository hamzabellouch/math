import OAI.Analysis.KadisonKastler.StateOrbitCompact

namespace OAI

/-! # Composition of approximate state-central orbit hulls

Composing a delta-central conjugation with an epsilon-central one costs
at most delta plus epsilon. Continuity and convexity extend this from
individual conjugates to their weakly closed convex hulls.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def wotUnitaryConjugation (u : unitary (Algebra M)) :
    (H →WOT[ℂ] H) →ₗ[ℝ] (H →WOT[ℂ] H) where
  toFun T := ContinuousLinearMapWOT.ofCLM (star u.val.val)*T*
    ContinuousLinearMapWOT.ofCLM u.val.val
  map_add' X Y := by simp only [mul_add,add_mul]
  map_smul' r X := by
    apply ContinuousLinearMapWOT.equiv.injective
    change star u.val.val*(r • X.toCLM)*u.val.val =
      r • (star u.val.val*X.toCLM*u.val.val)
    simp only [mul_smul_comm,smul_mul_assoc]

theorem wotUnitaryConjugation_continuous (u : unitary (Algebra M)) :
    Continuous (wotUnitaryConjugation u) := by
  change Continuous (fun T : H →WOT[ℂ] H =>
    ContinuousLinearMapWOT.ofCLM (star u.val.val)*T*
      ContinuousLinearMapWOT.ofCLM u.val.val)
  fun_prop

theorem stateOrbitHull_conjugate_mem
    (ξ : H) (a : Algebra M) (δ ε : ℝ) (u : unitary (Algebra M))
    (hu : ‖vectorStateCommutator ξ u.val‖ ≤ δ)
    {B : H →WOT[ℂ] H} (hB : B ∈ closedConvexHull ℝ (stateUnitaryOrbit ξ a ε)) :
    wotUnitaryConjugation u B ∈ closedConvexHull ℝ (stateUnitaryOrbit ξ a (δ+ε)) := by
  apply closedConvexHull_min ?_
    ((convex_closedConvexHull (𝕜 := ℝ)).linear_preimage (wotUnitaryConjugation u))
    (isClosed_closedConvexHull.preimage (wotUnitaryConjugation_continuous u)) hB
  rintro T ⟨v,hv,rfl⟩
  apply subset_closedConvexHull
  refine ⟨v*u,?_,?_⟩
  · have hm := vectorStateCommutator_mul_norm_le ξ v.val u.val
    have hn₁ := mul_le_of_le_one_right (norm_nonneg (vectorStateCommutator ξ v.val))
      (norm_unitary_le_one u)
    have hn₂ := mul_le_of_le_one_left (norm_nonneg (vectorStateCommutator ξ u.val))
      (norm_unitary_le_one v)
    change ‖vectorStateCommutator ξ (v.val*u.val)‖ ≤ δ+ε
    linarith
  · apply ContinuousLinearMapWOT.equiv.injective
    change star u.val.val*((star v.val*a*v.val).val)*u.val.val =
      (star (v.val*u.val)*a*(v.val*u.val)).val
    simp only [StarMemClass.coe_star,MulMemClass.coe_mul,star_mul,mul_assoc]

theorem stateOrbitHull_compose_subset
    (ξ : H) (a b : Algebra M) (δ ε : ℝ)
    (hb : ContinuousLinearMapWOT.ofCLM b.val ∈
      closedConvexHull ℝ (stateUnitaryOrbit ξ a ε)) :
    closedConvexHull ℝ (stateUnitaryOrbit ξ b δ) ⊆
      closedConvexHull ℝ (stateUnitaryOrbit ξ a (δ+ε)) := by
  apply closedConvexHull_min ?_ convex_closedConvexHull isClosed_closedConvexHull
  rintro T ⟨u,hu,rfl⟩
  have h := stateOrbitHull_conjugate_mem ξ a δ ε u hu hb
  have he : wotUnitaryConjugation u (ContinuousLinearMapWOT.ofCLM b.val) =
      ContinuousLinearMapWOT.ofCLM (star u.val*b*u.val).val := by
    apply ContinuousLinearMapWOT.equiv.injective
    rfl
  rw [he] at h
  exact h

theorem stateOrbitCore_compose_subset
    (ξ : H) (a b : Algebra M)
    (hb : ContinuousLinearMapWOT.ofCLM b.val ∈ stateOrbitCore ξ a) :
    stateOrbitCore ξ b ⊆ stateOrbitCore ξ a := by
  intro T hT δ hδ
  have h := stateOrbitHull_compose_subset ξ a b (δ/2) (δ/2)
    (hb (δ/2) (half_pos hδ)) (hT (δ/2) (half_pos hδ))
  simpa only [add_halves] using h

end

end KadisonKastler

end OAI
