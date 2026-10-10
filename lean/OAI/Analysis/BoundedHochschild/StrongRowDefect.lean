import OAI.Analysis.BoundedHochschild.RowDefectCompletion
import OAI.Analysis.BoundedHochschild.WeakRepresentationAverages

namespace OAI

/-! The square-root defect of a strongly normalized row tends strongly to
zero. Its extra averaging term therefore disappears even if the left
representation is not normal. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M I H K : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [PartialOrder M] [StarOrderedRing M] in
lemma represented_norm_sq (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (d : M) (ξ : H) :
    ‖σ d ξ‖ ^ 2 = RCLike.re (inner ℂ ξ (σ (star d * d) ξ)) := by
  rw [map_mul, map_star]
  change _ = RCLike.re (inner ℂ ξ ((σ d).adjoint (σ d ξ)))
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq]

lemma rowDefect_strong_zero (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (hlim : ∀ ξ : H, Tendsto
      (fun s : Finset I => inner ℂ ξ (σ (∑ i ∈ s, m i * star (m i)) ξ))
      atTop (𝓝 (inner ℂ ξ ξ))) (ξ : H) :
    Tendsto (fun s : Finset I => σ (rowDefect m s) ξ) atTop (𝓝 0) := by
  have he (s : Finset I) : ‖σ (rowDefect m s) ξ‖ ^ 2 =
      ‖ξ‖ ^ 2 - RCLike.re (inner ℂ ξ (σ (∑ i ∈ s, m i * star (m i)) ξ)) := by
    have hd := rowDefect_mul_star m s (hm s)
    rw [(rowDefect_nonneg m s).isSelfAdjoint.star_eq] at hd
    rw [represented_norm_sq, (rowDefect_nonneg m s).isSelfAdjoint.star_eq, hd,
      map_sub, map_one]
    simp only [sub_apply, one_apply_eq_self, inner_sub_right, map_sub, inner_self_eq_norm_sq]
  have hs : Tendsto (fun s : Finset I => ‖σ (rowDefect m s) ξ‖ ^ 2)
      atTop (𝓝 0) := by
    simp_rw [he]
    have h := (tendsto_const_nhds (x := ‖ξ‖ ^ 2)).sub ((RCLike.continuous_re.tendsto _).comp (hlim ξ))
    simpa only [Function.comp_apply, inner_self_eq_norm_sq, sub_self] using h
  have hn : Tendsto (fun s : Finset I => ‖σ (rowDefect m s) ξ‖) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hs
    change Tendsto (fun s : Finset I => Real.sqrt (‖σ (rowDefect m s) ξ‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at h
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using hn)

lemma rowDefect_average_strong_zero (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (hlim : ∀ ξ : H, Tendsto
      (fun s : Finset I => inner ℂ ξ (σ (∑ i ∈ s, m i * star (m i)) ξ))
      atTop (𝓝 (inner ℂ ξ ξ))) (W : H →L[ℂ] K) (ξ : H) :
    Tendsto (fun s : Finset I =>
      π (rowDefect m s) (W ((σ (rowDefect m s)).adjoint ξ))) atTop (𝓝 0) := by
  have he (s : Finset I) : (σ (rowDefect m s)).adjoint = σ (rowDefect m s) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star,
      (rowDefect_nonneg m s).isSelfAdjoint.star_eq]
  simp_rw [he]
  have hn : Tendsto (fun s : Finset I => ‖W‖ * ‖σ (rowDefect m s) ξ‖)
      atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using (tendsto_const_nhds.mul
      ((rowDefect_strong_zero σ m hm hlim ξ).norm))
  refine squeeze_zero_norm (fun s => ?_) hn
  calc
    _ ≤ ‖π (rowDefect m s)‖ * ‖W (σ (rowDefect m s) ξ)‖ := (π _).le_opNorm _
    _ ≤ 1 * (‖W‖ * ‖σ (rowDefect m s) ξ‖) :=
      mul_le_mul ((NonUnitalStarAlgHom.norm_apply_le π.toNonUnitalStarAlgHom _).trans (rowDefect_norm_le m s (hm s)))
        (W.le_opNorm _) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end BoundedHochschild.KadisonRingrose

end

end OAI
