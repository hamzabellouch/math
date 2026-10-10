import OAI.Analysis.KadisonKastler.ResolventCyclicMultipliers
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! # Strong convergence of bounded spectral multipliers -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolventCyclic_integral_norm_sq (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (x : H) (v : ResolventCyclicL2 R hR x) :
    (∫ s, ‖v s‖ ^ 2 ∂resolventVectorMeasure R hR x) = ‖v‖ ^ 2 := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (L2.inner_def (𝕜 := ℂ) v v)
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) v v)] at h
  simpa only [inner_self_eq_norm_sq] using h.symm

theorem resolventScalarMultiplier_tendsto (R : H →L[ℂ] H) (hR : IsSelfAdjoint R) (x : H)
    (φn : ℕ → spectrum ℝ R → ℂ) (φ : spectrum ℝ R → ℂ)
    (hn : ∀ n, Measurable (φn n)) (hφ : Measurable φ)
    (hbn : ∀ n s, ‖φn n s‖ ≤ 1) (hb : ∀ s, ‖φ s‖ ≤ 1)
    (ht : ∀ᵐ s ∂resolventVectorMeasure R hR x, Tendsto (fun n => φn n s) atTop (𝓝 (φ s)))
    (v : ResolventCyclicL2 R hR x) :
    Tendsto (fun n => resolventScalarMultiplier R hR x (φn n) (hn n) 1 (hbn n) v) atTop
      (𝓝 (resolventScalarMultiplier R hR x φ hφ 1 hb v)) := by
  let μ := resolventVectorMeasure R hR x
  let F := fun n s => ‖(φn n s - φ s) * v s‖ ^ 2
  have hi : Integrable (fun s => 4 * ‖v s‖ ^ 2) μ :=
    ((Lp.memLp v).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul 4
  have hlim : Tendsto (fun n => ∫ s, F n s ∂μ) atTop (𝓝 0) := by
    have hm (n : ℕ) : AEStronglyMeasurable (F n) μ :=
      (((hn n).aestronglyMeasurable.sub hφ.aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable v)).norm.pow 2
    have hbd (n : ℕ) : ∀ᵐ s ∂μ, ‖F n s‖ ≤ 4 * ‖v s‖ ^ 2 := by
      apply Eventually.of_forall
      intro s
      have he : ‖(φn n s - φ s) * v s‖ ≤ 2 * ‖v s‖ := by
        rw [norm_mul]
        apply (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)).trans
        nlinarith [hbn n s, hb s, norm_nonneg (v s)]
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg ((φn n s - φ s) * v s), norm_nonneg (v s)]
    have hpt : ∀ᵐ s ∂μ, Tendsto (fun n => F n s) atTop (𝓝 0) := by
      filter_upwards [ht] with s hs
      have h := (((hs.sub_const (φ s)).mul_const (v s)).norm).pow 2
      simpa only [sub_self, zero_mul, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using h
    simpa only [integral_zero] using
      tendsto_integral_of_dominated_convergence (fun s => 4 * ‖v s‖ ^ 2) hm hi hbd hpt
  have he (n : ℕ) :
      ‖resolventScalarMultiplier R hR x (φn n) (hn n) 1 (hbn n) v -
        resolventScalarMultiplier R hR x φ hφ 1 hb v‖ ^ 2 = ∫ s, F n s ∂μ := by
    rw [← resolventCyclic_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [resolventScalarMultiplier_apply_ae R hR x (φn n) (hn n) 1 (hbn n) v,
      resolventScalarMultiplier_apply_ae R hR x φ hφ 1 hb v,
      Lp.coeFn_sub (resolventScalarMultiplier R hR x (φn n) (hn n) 1 (hbn n) v)
        (resolventScalarMultiplier R hR x φ hφ 1 hb v)] with s hn' hφ' hs
    rw [hs, Pi.sub_apply, hn', hφ', ← sub_mul]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq := hlim.congr (fun n => (he n).symm)
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hsqrt

end

end KadisonKastler

end OAI
