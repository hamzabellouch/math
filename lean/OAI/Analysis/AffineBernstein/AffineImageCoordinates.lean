import Mathlib
import OAI.Analysis.AffineBernstein.AffineSupport
import OAI.Analysis.AffineBernstein.AffineFamily

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section AffineImageCoordinates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma continuousAffineEquiv_decomposition (A : E ≃ᴬ[ℝ] F) (x : E) :
    A x = A.toAffineEquiv.linear x + A 0 := by
  have h := A.toAffineEquiv.map_vadd (0:E) x
  simpa only [vadd_eq_add,zero_add,add_zero,ContinuousAffineEquiv.coe_coe] using h

lemma continuousAffineEquiv_inverse_decomposition (A : E ≃ᴬ[ℝ] F) (x : E) :
    A x = A.toAffineEquiv.linear (x-A.symm 0) := by
  have h := continuousAffineEquiv_decomposition A (A.symm 0)
  rw [ContinuousAffineEquiv.apply_symm_apply] at h
  rw [continuousAffineEquiv_decomposition A x, map_sub]
  have hh : A 0 = -A.toAffineEquiv.linear (A.symm 0) := by
    exact eq_neg_of_add_eq_zero_right h.symm
  rw [hh, sub_eq_add_neg]

/-- Rewrite the actual affine-image sequence in the exact pullback coordinates
used throughout the PDE support estimates. -/
theorem InAffineLimitFamily.epigraph_pullback_approximation {n k m : ℕ}
    {Ω : Set (Space n)} {u : Space n → ℝ} {C : Set (Space k × Space m)}
    (hf : InAffineLimitFamily (sourceEpigraph Ω u) C) :
    ∃ a : ℕ → Space n × ℝ, ∃ L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ),
      LocalDistanceConverges (fun j => affineEpigraphPullback Ω u (a j) (L j)) C := by
  obtain ⟨A,hA⟩ := hf.approximation
  let a := fun j => (A j).symm 0
  let L : ℕ → (Space k × Space m) ≃L[ℝ] (Space n × ℝ) :=
    fun index =>
      { (A index).toAffineEquiv.linear.symm with
        continuous_toFun := (A index).symm.toContinuousAffineMap.contLinear.continuous
        continuous_invFun := (A index).toContinuousAffineMap.contLinear.continuous }
  refine ⟨a,L,?_⟩
  have he j : affineEpigraphPullback Ω u (a j) (L j) = A j '' sourceEpigraph Ω u := by
    ext p
    constructor
    · intro hp
      refine ⟨a j + L j p,hp,?_⟩
      rw [continuousAffineEquiv_inverse_decomposition]
      change (A j).toAffineEquiv.linear ((a j + L j p)-a j) = p
      rw [add_sub_cancel_left]
      exact (A j).toAffineEquiv.linear.apply_symm_apply p
    · rintro ⟨x,hx,rfl⟩
      have hax : a j + L j (A j x) = x := by
        rw [continuousAffineEquiv_inverse_decomposition]
        change a j + (A j).toAffineEquiv.linear.symm ((A j).toAffineEquiv.linear (x-a j)) = x
        rw [(A j).toAffineEquiv.linear.symm_apply_apply,add_sub_cancel]
      simpa only [affineEpigraphPullback,sourceEpigraph,Set.mem_ofPred_eq,hax] using hx
  simpa only [he] using hA
end AffineImageCoordinates


end
end AffineBernstein
end

end OAI
