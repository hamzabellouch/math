import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousYSpace
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Measure.SeparableMeasure

namespace OAI

/-! # Weak subsequences in the actual homogeneous Hilbert space

Sequential Banach–Alaoglu and the real Riesz representation theorem apply
to the weighted Fourier L² completion. This prepares the quantitative local
observation form of the compact-error estimates.
-/

open Filter Topology Set
open scoped ENNReal

namespace DefocusingNLS

theorem homogeneousY_weak_subsequence (a k M : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (u : ℕ → HomogeneousY a k)
    (hu : ∀ n, ‖u n‖ ≤ M) :
    ∃ v : HomogeneousY a k, ‖v‖ ≤ M ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
        Tendsto (fun n => ℓ (u (φ n))) atTop (𝓝 (ℓ v)) := by
  let := homogeneousFourierMeasure_locallyFinite a k ha1 hk
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : MeasureTheory.IsSeparable (homogeneousFourierMeasure a k) := inferInstance
  let : SecondCountableTopology (HomogeneousY a k) := inferInstance
  let R := InnerProductSpace.toDual ℝ (HomogeneousY a k)
  let w : ℕ → WeakDual ℝ (HomogeneousY a k) := fun n => (R (u n)).toWeakDual
  have hw (n : ℕ) : w n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 M := by
    change R (u n) ∈ Metric.closedBall 0 M
    simpa only [Metric.mem_closedBall, dist_zero_right, R.norm_map] using hu n
  obtain ⟨v', hv', φ, hφ, ht⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ (HomogeneousY a k) 0 M) hw
  let v := R.symm v'.toStrongDual
  have hv : ‖v‖ ≤ M := by
    change ‖R.symm v'.toStrongDual‖ ≤ M
    rw [R.symm.norm_map]
    simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right] using hv'
  refine ⟨v, hv, φ, hφ, fun ℓ => ?_⟩
  have hreal (L : HomogeneousY a k →L[ℝ] ℝ) :
      Tendsto (fun n => L (u (φ n))) atTop (𝓝 (L v)) := by
    let x := R.symm L
    have hn (n : ℕ) : w (φ n) x = L (u (φ n)) := by
      change inner ℝ (u (φ n)) x = L (u (φ n))
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    have hvx : v' x = L v := by
      have he : R v = v'.toStrongDual := R.apply_symm_apply _
      change v'.toStrongDual x = L v
      rw [← he]
      change inner ℝ v x = L v
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    have h := (WeakDual.eval_continuous x).continuousAt.tendsto.comp ht
    simpa only [Function.comp_def, hn, hvx] using h
  have hre := hreal (Complex.reCLM.comp ℓ)
  have him := hreal (Complex.imCLM.comp ℓ)
  have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp hre).add
    ((Complex.continuous_ofReal.continuousAt.tendsto.comp him).mul_const Complex.I)
  simpa only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Function.comp_apply, Complex.re_add_im] using h

end DefocusingNLS

end OAI
