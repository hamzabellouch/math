import OAI.Analysis.CircleDomains.Reflection.PrincipalReflectionDefect
import OAI.Analysis.CircleDomains.Sobolev.PrincipalLocalizedDerivativeError
import OAI.Analysis.CircleDomains.Reflection.ReflectionWeightedL2

namespace OAI

/-! Reflection invariance and strong principal-derivative convergence give
an actual globally L2-small source error, with the exact conjugacy formula
on any prescribed finite-measure reflected source set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami FiniteTransfer

lemma planeL2_norm_star (f : PlaneL2) : ‖star f‖=‖f‖ := by
  rw [Lp.norm_def,Lp.norm_def]
  congr 1
  exact (eLpNorm_congr_ae (Lp.coeFn_star f)).trans eLpNorm_star

lemma planeL2_star_tendsto_zero {f : ℕ → PlaneL2} (h : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun n => star (f n)) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero,planeL2_norm_star]
  simpa only [norm_zero] using h.norm

namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma reflection_source_error (D : AnalyticReflectionData C) (i : I)
    {A : Set ℂ} (hA : MeasurableSet A) (hfin : volume A≠∞) :
    ∃q : ℕ → PlaneL2,Tendsto q atTop (𝓝 0) ∧ ∀n,∀ᵐz ∂volume,
      roundReflectionPlane (D.center i) (D.radius i) z∈A →
      q n z=star (partialZ (D.approximation.map (D.limitData.index n))
        (roundReflectionPlane (D.center i) (D.radius i) z))*
        star (roundReflectionWeight (D.center i) (D.radius i) z)*D.reflectionDefect i n z := by
  let R := roundReflectionPlane (D.center i) (D.radius i)
  have hR := roundReflectionPlane_quasiMeasurePreserving (D.center i) (D.radius_pos i).ne'
  let δ (n : ℕ) (z : ℂ) := star (D.reflectionDefect i n (R z))
  have hm (n : ℕ) : AEStronglyMeasurable (δ n) volume :=
    (Complex.continuous_conj.measurable.comp ((D.reflectionDefect_measurable i n).comp
      (roundReflectionPlane_measurable _ _))).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐz ∂volume,‖δ n z‖≤2*D.bound := by
    filter_upwards [] with z
    simpa only [δ,norm_star] using D.reflectionDefect_bound i n (R z)
  have ht : ∀ᵐz ∂volume,Tendsto (fun n => δ n z) atTop (𝓝 0) := by
    filter_upwards [hR.ae (D.reflectionDefect_tendsto i)] with z hz
    simpa only [star_zero] using hz.star
  obtain ⟨e,he,her⟩ := D.limitData.exists_localized_derivative_error hA hfin δ hm
    (mul_nonneg zero_le_two D.bound_nonneg) hb ht
  obtain ⟨q,hq,hqr⟩ := exists_strong_reflection_pullback (D.center i) (D.radius_pos i).ne'
    (fun n => star (e n)) (planeL2_star_tendsto_zero he)
  refine ⟨q,hq,?_⟩
  intro n
  filter_upwards [hqr n,hR.ae (Lp.coeFn_star (e n)),hR.ae (her n)] with z hqz hsz hez hzA
  rw [hqz,hsz]
  simp only [Pi.star_apply] at *
  rw [hez,indicator_of_mem hzA,star_mul]
  dsimp only [δ,R]
  rw [roundReflectionPlane_involutive (D.center i) (D.radius_pos i).ne' z,star_star]
  ring

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
