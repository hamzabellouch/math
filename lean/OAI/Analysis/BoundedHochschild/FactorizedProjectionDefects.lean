import OAI.Analysis.BoundedHochschild.RepresentedRightAverages

namespace OAI

/-! The right-module defect at a projection is an off-diagonal coefficient
of the fixed operator factorization. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M H K : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma factorized_projection_defect (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (L W : H →L[ℂ] K) (T : M →L[ℂ] M)
    (hT : ∀ a, σ (T a) = L.adjoint.comp ((π a).comp W))
    (a : M) {p f : M} (hp : IsStarProjection p) (hf : IsStarProjection f) (hfp : f ≤ p) :
    (σ (T a * p - T (a * p) * p)).comp (σ f) =
      (L.adjoint.comp (π a)).comp ((1 - π p).comp (W.comp (σ f))) := by
  have hpf : (σ p).comp (σ f) = σ f := by
    change σ p * σ f = σ f
    rw [← map_mul, (hf.le_iff_mul_eq_right hp).mp hfp]
  rw [map_sub, map_mul, map_mul, hT, hT, map_mul]
  ext ξ
  have hpf' := congrArg (fun A : H →L[ℂ] H => A ξ) hpf
  change σ p (σ f ξ) = σ f ξ at hpf'
  simp only [mul_apply_eq_comp, sub_apply, ContinuousLinearMap.comp_apply, map_sub, one_apply_eq_self,
    hpf']

end BoundedHochschild.KadisonRingrose

end

end OAI
