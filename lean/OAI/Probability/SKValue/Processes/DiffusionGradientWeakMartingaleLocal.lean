import Mathlib
import OAI.Probability.SKValue.Equations.CubicEnvelopeMean
import OAI.Probability.SKValue.Gaussian.ShiftedBrownianCoordinates

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators

lemma diffusion_gradient_weak_martingale_local
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) (a : ℝ≥0)
    {T K L Lu H : ℝ} {γ : ℝ → ℝ} {u : ℝ → ℝ → ℝ} {X W : ℝ → Ω → ℝ}
    {F : Ω → ℝ} (hT : 0<T) (hT1 : T≤1) (hLu : 0≤Lu) (hH : 0≤H)
    (h : GradientStripCore T γ u K L)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤Lu*(|s-t|+|x-y|))
    (hXM : ∀ t∈Icc (0 : ℝ) T,
      StronglyMeasurable[Filtration.natural B hBm (a+t.toNNReal)] (X t))
    (hWM : ∀ t∈Icc (0 : ℝ) T, AEStronglyMeasurable (W t) μ)
    (hW : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ ω,
      W t ω-W s ω=B (a+t.toNNReal) ω-B (a+s.toNNReal) ω)
    (hpaths : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Icc (0 : ℝ) T) ∧
      IntervalIntegrable (fun s ↦ γ s*u s (X s ω)) volume 0 T ∧
      ∀ t∈Icc (0 : ℝ) T, X t ω=W t ω+∫ s in (0 : ℝ)..t, γ s*u s (X s ω))
    (hFm : StronglyMeasurable[Filtration.natural B hBm a] F) (hFb : ∀ ω, |F ω|≤H) :
    (∫ ω, F ω*u T (X T ω) ∂μ)=(∫ ω, F ω*u 0 (X 0 ω) ∂μ) := by
  let ℱ := Filtration.natural B hBm
  have hFM : AEStronglyMeasurable F μ := (hFm.mono (ℱ.le a)).aestronglyMeasurable
  have hXM' (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : AEStronglyMeasurable (X t) μ :=
    ((hXM t ht).mono (ℱ.le _)).aestronglyMeasurable
  have hsp (t : ℝ) (ht : t∈Icc (0 : ℝ) T) (x y : ℝ) :
      |u t x-u t y|≤Lu*|x-y| := by
    simpa only [sub_self,abs_zero,zero_add] using hLip t ht t ht x y
  have hVi (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : Integrable (fun ω ↦ F ω*u t (X t ω)) μ := by
    apply Integrable.of_bound (hFM.mul ((h.smooth t ht).continuous.comp_aestronglyMeasurable (hXM' t ht))) H
    filter_upwards [] with ω
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (hFb ω) (h.bounded t ht _) (abs_nonneg _) hH).trans_eq (mul_one H)
  have hlim := weighted_pathGradientResidual_tendsto (Z:=shiftedBrownianCoordinates B a T)
    hT hT1 hLu hH h hLip hXM' hWM
    (fun N hN i ↦ shiftedBrownianCoordinates_hasLaw hB a hT hN i)
    (fun N hN i ω ↦ shiftedBrownianCoordinates_exact hT hN hW i ω) hpaths hFM hFb
  have hmean (N : ℕ) : (∫ ω, F ω*pathGradientResidual T N u (fun t ↦ X t ω)
      (fun t ↦ W t ω) ∂μ)=(∫ ω, F ω*u T (X T ω) ∂μ)-(∫ ω, F ω*u 0 (X 0 ω) ∂μ) := by
    have hδ : 0≤ stepSize T N := div_nonneg hT.le (Nat.cast_nonneg N)
    have htime (j : ℕ) (hj : j≤N) := mesh_time_mem_total hT.le hj
    let τ := fun j : ℕ ↦ a+(meshTime T N j).toNNReal
    have hτ (i : Fin N) : τ i≤τ (i+1) := by
      dsimp [τ]
      apply add_le_add le_rfl
      apply Real.toNNReal_mono
      dsimp [meshTime]
      push_cast
      nlinarith
    have hτdiff (i : Fin N) : (τ (i+1) : ℝ)-(τ i : ℝ)=stepSize T N := by
      dsimp only [τ]
      rw [NNReal.coe_add,NNReal.coe_add,Real.coe_toNNReal _ (htime (i+1) i.isLt).1,
        Real.coe_toNNReal _ (htime i i.isLt.le).1]
      dsimp [meshTime]
      push_cast
      ring
    have hWeq (i : Fin N) (ω : Ω) :
        W (meshTime T N (i+1)) ω-W (meshTime T N i) ω=B (τ (i+1)) ω-B (τ i) ω :=
      hW _ (htime i i.isLt.le) _ (htime (i+1) i.isLt) ω
    have hFm' (i : Fin N) : StronglyMeasurable[ℱ (τ i)] F :=
      hFm.mono (ℱ.mono (le_add_of_nonneg_right (by positivity)))
    have hDm (i : Fin N) : StronglyMeasurable[ℱ (τ i)]
        (fun ω ↦ F ω*deriv (u (meshTime T N i)) (X (meshTime T N i) ω)) :=
      (hFm' i).mul ((h.continuous_deriv (htime i i.isLt.le)).comp_stronglyMeasurable
        (hXM _ (htime i i.isLt.le)))
    have hD2m (i : Fin N) : StronglyMeasurable[ℱ (τ i)]
        (fun ω ↦ F ω*deriv (deriv (u (meshTime T N i))) (X (meshTime T N i) ω)) :=
      (hFm' i).mul ((h.continuous_second (htime i i.isLt.le)).comp_stronglyMeasurable
        (hXM _ (htime i i.isLt.le)))
    have hDi (i : Fin N) : Integrable
        (fun ω ↦ F ω*deriv (u (meshTime T N i)) (X (meshTime T N i) ω)) μ := by
      apply Integrable.of_bound ((hDm i).mono (ℱ.le _)).aestronglyMeasurable (H*Lu)
      filter_upwards [] with ω
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hFb ω) (GradientStripCore.deriv_bound hLu hsp (htime i i.isLt.le) _)
        (abs_nonneg _) hH
    have hD2i (i : Fin N) : Integrable
        (fun ω ↦ F ω*deriv (deriv (u (meshTime T N i))) (X (meshTime T N i) ω)) μ := by
      apply Integrable.of_bound ((hD2m i).mono (ℱ.le _)).aestronglyMeasurable (H*K)
      filter_upwards [] with ω
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hFb ω) (h.second_bound _ (htime i i.isLt.le) _) (abs_nonneg _) hH
    apply weighted_pathGradientResidual_integral (hVi T ⟨hT.le,le_rfl⟩) (hVi 0 ⟨le_rfl,hT.le⟩)
    · intro i
      simpa only [hWeq,mul_assoc] using
        brownian_predictable_increment_integrable hB hBm (hτ i) (hDm i) (hDi i)
    · intro i
      simpa only [hWeq,hτdiff,mul_assoc] using
        brownian_predictable_quadratic_integrable hB hBm (hτ i) (hD2m i) (hD2i i)
    · intro i
      simpa only [hWeq,mul_assoc] using brownian_predictable_increment_mean hB hBm (hτ i) (hDm i)
    · intro i
      simpa only [hWeq,hτdiff,mul_assoc] using
        brownian_predictable_quadratic_mean hB hBm (hτ i) (hD2m i)
  have hh : (∫ ω, F ω*u T (X T ω) ∂μ)-(∫ ω, F ω*u 0 (X 0 ω) ∂μ)=0 := by
    have hc : Tendsto (fun _ : ℕ ↦ (∫ ω, F ω*u T (X T ω) ∂μ)-
        (∫ ω, F ω*u 0 (X 0 ω) ∂μ)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [hmean] using hlim
    exact tendsto_nhds_unique tendsto_const_nhds hc
  exact sub_eq_zero.mp hh

end SKValue

end

end OAI
