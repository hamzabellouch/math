import Mathlib
import OAI.Analysis.CoulombIonization.Variational.WeightedVariance
import OAI.Analysis.CoulombIonization.FormDomain.WeakProduct

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

lemma mollified_lipschitz_derivative {k p : E → ℝ}
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k)
    {C : NNReal} (hp : LipschitzWith C p) (v x : E) :
    fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] p) x v =
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y => lineDeriv ℝ p y v)) x := by
  let L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)
  have hφ : ContDiff ℝ ∞ (fun y => k (x - y)) := hk.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport (fun y => k (x - y)) :=
    hkc.comp_homeomorph (Homeomorph.subLeft x)
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcφ hφ (by simp)
  have hdφ (y : E) : lineDeriv ℝ (fun y => k (x - y)) y (-v) =
      fderiv ℝ k (x - y) v := by
    have hh := (hk.differentiable (by simp) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    simpa [Function.comp_def] using (hh.hasLineDerivAt (-v)).lineDeriv
  have hw := hp.integral_lineDeriv_mul_eq hD hcφ v (μ := volume)
  simp only [hdφ] at hw
  have hid : Integrable (fun y => (L.precompL E) (fderiv ℝ k (x - y)) (p y)) :=
    ((hkc.fderiv ℝ).convolutionExists_left (L.precompL E)
      (hk.continuous_fderiv (by simp)) hp.continuous.locallyIntegrable x).integrable_swap
  rw [(hkc.hasFDerivAt_convolution_left L (hk.of_le (by simp))
      hp.continuous.locallyIntegrable x).fderiv,
    convolution_eq_swap, ContinuousLinearMap.integral_apply hid, convolution_eq_swap]
  simpa only [ContinuousLinearMap.precompL_apply, L, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul, mul_comm] using hw.symm

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
lemma convolution_bounded {k p : E → ℝ} (hk : Integrable k)
    (hk0 : ∀ x, 0 ≤ k x) (hk1 : (∫ x, k x) = 1)
    {B : ℝ} (hb : ∀ x, ‖p x‖ ≤ B) (x : E) :
    ‖(k ⋆[ContinuousLinearMap.lsmul ℝ ℝ] p) x‖ ≤ B := by
  change ‖∫ y, k y * p (x - y)‖ ≤ B
  calc
    _ ≤ ∫ y, k y * B := norm_integral_le_of_norm_le (hk.mul_const B)
      (Eventually.of_forall fun y => by
        rw [norm_mul, Real.norm_of_nonneg (hk0 y)]
        exact mul_le_mul_of_nonneg_left (hb _) (hk0 y))
    _ = B := by rw [integral_mul_const, hk1, one_mul]

lemma bounded_lipschitz_smooth_approx {p : E → ℝ} {C : NNReal}
    (hp : LipschitzWith C p) {B : ℝ} (hB : ∀ x, ‖p x‖ ≤ B) (v : E) :
    ∃ u : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ ∞ (u n)) ∧
      (∀ n x, ‖u n x‖ ≤ B) ∧
      (∀ n x, ‖lineDeriv ℝ (u n) x v‖ ≤ C * ‖v‖) ∧
      (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (p x))) ∧
      ∀ᵐ x, Tendsto (fun n => lineDeriv ℝ (u n) x v) atTop
        (𝓝 (lineDeriv ℝ p x v)) := by
  let k : ℕ → E → ℝ := fun n => (shrinkingBump n).normed volume
  let L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)
  let u : ℕ → E → ℝ := fun n => k n ⋆[L] p
  have hk (n : ℕ) : ContDiff ℝ ∞ (k n) := (shrinkingBump n).contDiff_normed
  have hkc (n : ℕ) : HasCompactSupport (k n) := (shrinkingBump n).hasCompactSupport_normed
  have hk0 (n : ℕ) : ∀ x, 0 ≤ k n x := (shrinkingBump n).nonneg_normed
  have hk1 (n : ℕ) : (∫ x, k n x) = 1 := (shrinkingBump n).integral_normed
  have hki (n : ℕ) : Integrable (k n) := (hk n).continuous.integrable_of_hasCompactSupport (hkc n)
  have hu (n : ℕ) : ContDiff ℝ ∞ (u n) :=
    (hkc n).contDiff_convolution_left L (hk n) hp.continuous.locallyIntegrable
  have hdu (n : ℕ) (x : E) : lineDeriv ℝ (u n) x v =
      (k n ⋆[L] (fun y => lineDeriv ℝ p y v)) x :=
    ((hu n).differentiable (by simp) x).lineDeriv_eq_fderiv.trans
      (mollified_lipschitz_derivative (hk n) (hkc n) hp v x)
  refine ⟨u, hu, fun n x => convolution_bounded (hki n) (hk0 n) (hk1 n) hB x, ?_, ?_, ?_⟩
  · intro n x
    rw [hdu]
    exact convolution_bounded (hki n) (hk0 n) (hk1 n)
      (fun _ => norm_lineDeriv_le_of_lipschitz ℝ hp) x
  · intro x
    exact ContDiffBump.convolution_tendsto_right_of_continuous shrinkingBump_tendsto
      hp.continuous x
  · simp_rw [hdu]
    exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      shrinkingBump_tendsto
      (Eventually.of_forall fun n => le_refl (2 * (shrinkingBump (E := E) n).rIn))
      (hp.locallyIntegrable_lineDeriv v)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
lemma integral_real_mul_tendsto {q : ℕ → E → ℝ} {p : E → ℝ} {f : E → ℂ}
    (hq : ∀ n, AEStronglyMeasurable (q n)) {B : ℝ}
    (hb : ∀ n x, ‖q n x‖ ≤ B)
    (ht : ∀ᵐ x, Tendsto (fun n => q n x) atTop (𝓝 (p x)))
    (hf : Integrable f) :
    Tendsto (fun n => ∫ x, (q n x : ℂ) * f x) atTop
      (𝓝 (∫ x, (p x : ℂ) * f x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => B * ‖f x‖)
  · intro n
    exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable (hq n)).mul
      hf.aestronglyMeasurable)
  · exact hf.norm.const_mul B
  · intro n
    exact Eventually.of_forall fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb n x) (norm_nonneg _)
  · filter_upwards [ht] with x hx
    exact (Complex.continuous_ofReal.tendsto _ |>.comp hx).mul tendsto_const_nhds

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
lemma smooth_lineDeriv_continuous {p : E → ℝ} (hp : ContDiff ℝ ∞ p) (v : E) :
    Continuous (fun x => lineDeriv ℝ p x v) := by
  have he : (fun x => lineDeriv ℝ p x v) = fun x => fderiv ℝ p x v := by
    funext x
    exact (hp.differentiable (by simp) x).lineDeriv_eq_fderiv
  rw [he]
  exact (hp.continuous_fderiv (by simp)).clm_apply continuous_const

lemma IsWeakDerivative.mul_lipschitz {f g : E → ℂ} {v : E}
    (hw : IsWeakDerivative v f g) (hf : MemLp f 2) (hg : MemLp g 2)
    {p : E → ℝ} {C : NNReal} (hp : LipschitzWith C p)
    (hb : ∃ B : ℝ, ∀ x, |p x| ≤ B) :
    IsWeakDerivative v (fun x => (p x : ℂ) * f x)
      (fun x => (p x : ℂ) * g x + Complex.ofReal (lineDeriv ℝ p x v) * f x) := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨u, hu, hub, hdub, hut, hdut⟩ := bounded_lipschitz_smooth_approx hp hB v
  intro φ hφ hcφ
  have hφ2 := test_memLp hφ hcφ
  have hdφ2 := test_deriv_memLp hφ hcφ v
  have i1 : Integrable (fun x => f x * Complex.ofReal (lineDeriv ℝ φ x v)) :=
    hf.integrable_mul hdφ2
  have i2 : Integrable (fun x => g x * (φ x : ℂ)) := hg.integrable_mul hφ2
  have i3 : Integrable (fun x => f x * (φ x : ℂ)) := hf.integrable_mul hφ2
  have t1 := integral_real_mul_tendsto (fun n => (hu n).continuous.aestronglyMeasurable)
    hub (Eventually.of_forall hut) i1
  have t2 := integral_real_mul_tendsto (fun n => (hu n).continuous.aestronglyMeasurable)
    hub (Eventually.of_forall hut) i2
  have t3 := integral_real_mul_tendsto
    (fun n => (smooth_lineDeriv_continuous (hu n) v).aestronglyMeasurable) hdub hdut i3
  have h1 (n : ℕ) : Integrable (fun x => (u n x : ℂ) * (g x * (φ x : ℂ))) :=
    i2.bdd_mul ((Complex.continuous_ofReal.comp (hu n).continuous).aestronglyMeasurable)
      (Eventually.of_forall fun x => by simpa using hub n x)
  have h2 (n : ℕ) : Integrable (fun x => Complex.ofReal (lineDeriv ℝ (u n) x v) *
      (f x * (φ x : ℂ))) :=
    i3.bdd_mul ((Complex.continuous_ofReal.comp
      (smooth_lineDeriv_continuous (hu n) v)).aestronglyMeasurable)
      (Eventually.of_forall fun x => by simpa using hdub n x)
  have he (n : ℕ) : (∫ x, (u n x : ℂ) * (f x * Complex.ofReal (lineDeriv ℝ φ x v))) =
      -((∫ x, (u n x : ℂ) * (g x * (φ x : ℂ))) +
        (∫ x, Complex.ofReal (lineDeriv ℝ (u n) x v) * (f x * (φ x : ℂ)))) := by
    have hh := hw.mul_smooth hf hg (hu n) φ hφ hcφ
    have ha : (fun x => ((u n x : ℂ) * g x +
        Complex.ofReal (lineDeriv ℝ (u n) x v) * f x) * (φ x : ℂ)) =
        fun x => (u n x : ℂ) * (g x * (φ x : ℂ)) +
          Complex.ofReal (lineDeriv ℝ (u n) x v) * (f x * (φ x : ℂ)) := by
      funext x; ring
    rw [ha, integral_add (h1 n) (h2 n)] at hh
    simpa only [mul_assoc] using hh
  have ht := tendsto_nhds_unique t1 (((t2.add t3).neg).congr (fun n => (he n).symm))
  have ih1 : Integrable (fun x => (p x : ℂ) * (g x * (φ x : ℂ))) :=
    i2.bdd_mul (Complex.continuous_ofReal.comp hp.continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using hB x)
  have ih2 : Integrable (fun x => Complex.ofReal (lineDeriv ℝ p x v) * (f x * (φ x : ℂ))) :=
    i3.bdd_mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (aestronglyMeasurable_lineDeriv hp.continuous volume))
      (Eventually.of_forall fun x => by
        simpa using (norm_lineDeriv_le_of_lipschitz ℝ hp (x₀ := x) (v := v)))
  have ha : (fun x => ((p x : ℂ) * g x + Complex.ofReal (lineDeriv ℝ p x v) * f x) *
      (φ x : ℂ)) = fun x => (p x : ℂ) * (g x * (φ x : ℂ)) +
        Complex.ofReal (lineDeriv ℝ p x v) * (f x * (φ x : ℂ)) := by
    funext x; ring
  rw [ha, integral_add ih1 ih2]
  simpa only [mul_assoc] using ht

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace

end

end OAI
