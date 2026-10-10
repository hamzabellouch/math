import OAI.Analysis.BoundedHochschild.CentralSupportNormalizedRows
import OAI.Analysis.BoundedHochschild.InfiniteRepresentedFamilies

namespace OAI

/-! The row exhausting a central support compresses the averaging operator
through the original projection corner. -/

noncomputable section

open Filter Topology

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M H K : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma centralSupportRow_compression_term
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    {p z : M} (hp : IsStarProjection p) (hz : IsStarProjection z) (hpz : p ≤ z)
    (S : Set (PartialIso M)) (hS : ∀ v ∈ S, v.final ≤ p ∧ v.initial ≤ z)
    (W : H →L[ℂ] K) (i : Option S) (ξ : H) :
    π (centralSupportRow z S i) (W ((σ (centralSupportRow z S i)).adjoint (σ z ξ))) =
      π (centralSupportRow z S i)
        (π p (W (σ p ((σ (centralSupportRow z S i)).adjoint ξ)))) := by
  cases i with
  | none =>
      have hright : (σ (1 - z)).adjoint.comp (σ z) = 0 := by
        rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star,
          hz.one_sub.isSelfAdjoint.star_eq]
        change σ (1 - z) * σ z = 0
        rw [← map_mul, hz.one_sub_mul_self, map_zero]
      have hleft : (π (1 - z)).comp (π p) = 0 := by
        change π (1 - z) * π p = 0
        rw [← map_mul, sub_mul, one_mul, (hp.le_iff_mul_eq_right hz).mp hpz,
          sub_self, map_zero]
      have hr := congrArg (fun A : H →L[ℂ] H => A ξ) hright
      have hl := congrArg (fun A : K →L[ℂ] K => A (W (σ p ((σ (1-z)).adjoint ξ)))) hleft
      change (σ (1 - z)).adjoint (σ z ξ) = 0 at hr
      change π (1 - z) (π p (W (σ p ((σ (1-z)).adjoint ξ)))) = 0 at hl
      change π (1 - z) (W ((σ (1-z)).adjoint (σ z ξ))) = _
      rw [hr, map_zero, map_zero]
      exact hl.symm
  | some v =>
      have hpv : p * (v.val : M) = v.val := by
        calc
          _ = p * (v.val.final * (v.val : M)) := by rw [v.val.final_mul]
          _ = v.val := by rw [← mul_assoc,
            (v.val.final_proj.le_iff_mul_eq_right hp).mp (hS v v.property).1,
            v.val.final_mul]
      have hvz : (v.val : M) * z = v.val := by
        calc
          _ = ((v.val : M) * v.val.initial) * z := by rw [v.val.mul_initial]
          _ = v.val := by rw [mul_assoc,
            (v.val.initial_proj.le_iff_mul_eq_left hz).mp (hS v v.property).2,
            v.val.mul_initial]
      have hvp : star (v.val : M) * p = star (v.val : M) := by
        simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hpv
      have hσ (a b c : M) (h : a * b = c) (η : H) : σ a (σ b η) = σ c η :=
        congrArg (fun A : H →L[ℂ] H => A η) ((map_mul σ a b).symm.trans (congrArg σ h))
      have hπ (a b c : M) (h : a * b = c) (η : K) : π a (π b η) = π c η :=
        congrArg (fun A : K →L[ℂ] K => A η) ((map_mul π a b).symm.trans (congrArg π h))
      have hs : (σ (star (v.val : M))).adjoint = σ (v.val : M) := by
        rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, star_star]
      simp only [centralSupportRow, hs, hσ _ _ _ hvz, hσ _ _ _ hpv, hπ _ _ _ hvp]

theorem centralSupportRow_compression_norm_le
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H))
    {p z : M} (hp : IsStarProjection p) (hz : IsStarProjection z) (hpz : p ≤ z)
    (S : Set (PartialIso M)) (hS : ∀ v ∈ S, v.final ≤ p ∧ v.initial ≤ z)
    (hm : ∀ s : Finset (Option S),
      ∑ i ∈ s, centralSupportRow z S i * star (centralSupportRow z S i) ≤ 1)
    (W : H →L[ℂ] K) :
    ‖(infiniteRepresentedRightAverage π σ (centralSupportRow z S) hm W).comp (σ z)‖ ≤
      ‖(π p).comp (W.comp (σ p))‖ := by
  have he : (infiniteRepresentedRightAverage π σ (centralSupportRow z S) hm W).comp (σ z) =
      infiniteRepresentedRightAverage π σ (centralSupportRow z S) hm
        ((π p).comp (W.comp (σ p))) := by
    ext ξ
    have h₁ := infiniteRepresentedRightAverage_hasSum π σ (centralSupportRow z S) hm W (σ z ξ)
    have h₂ := infiniteRepresentedRightAverage_hasSum π σ (centralSupportRow z S) hm
      ((π p).comp (W.comp (σ p))) ξ
    have hf := funext (fun i => centralSupportRow_compression_term π σ hp hz hpz S hS W i ξ)
    simp only [ContinuousLinearMap.comp_apply] at h₂ ⊢
    rw [hf] at h₁
    exact h₁.unique h₂
  rw [he]
  exact infiniteRepresentedRightAverage_norm_le π σ (centralSupportRow z S) hm _

end BoundedHochschild.KadisonRingrose

end

end OAI
