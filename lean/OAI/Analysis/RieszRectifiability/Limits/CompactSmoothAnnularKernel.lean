import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.SmoothAnnularWeights
import OAI.Analysis.RieszRectifiability.Kernel.CappedRieszKernel

namespace OAI

/-!
# Compactly supported smooth annular kernel tests

Annular cutoffs remove the Riesz singularity and give compact support. Agreement
with a capped kernel proves continuity, so pairing with a fixed normal produces
a compactly supported continuous scalar test for weak limits.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped CompactlySupported

def smoothAnnularKernel {d : ℕ} (n : ℕ) (a : Ambient d) (r R : ℝ)
    (hr : 0 < r) (hR : 0 < R) (x : Ambient d) : Ambient d :=
  smoothAnnularWeight a r R hr hR x • kernel n a x

theorem annularSmoothBallCutoff_translate {d : ℕ} (a : Ambient d)
    (r : ℝ) (hr : 0 < r) (x : Ambient d) :
    annularSmoothBallCutoff a r hr x =
      annularSmoothBallCutoff (0 : Ambient d) r hr (x - a) := by
  simp only [ContDiffBump.apply, annularSmoothBallCutoff, sub_zero]

theorem smoothAnnularWeight_translate {d : ℕ} (a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (x : Ambient d) :
    smoothAnnularWeight a r R hr hR x = smoothAnnularWeight 0 r R hr hR (x - a) := by
  simp only [smoothAnnularWeight, annularSmoothBallCutoff_translate a]

theorem smoothAnnularKernel_translate {d : ℕ} (n : ℕ) (a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R) (x : Ambient d) :
    smoothAnnularKernel n a r R hr hR x = smoothAnnularKernel n 0 r R hr hR (x - a) := by
  rw [smoothAnnularKernel, smoothAnnularKernel, smoothAnnularWeight_translate]
  congr 1
  simp only [kernel, zero_sub, neg_sub]

theorem smoothAnnularKernel_zero_near {d : ℕ} (n : ℕ) (a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (x : Ambient d) (hx : dist x a ≤ r) :
    smoothAnnularKernel n a r R hr (hr.trans_le hrR) x = 0 := by
  rw [smoothAnnularKernel, smoothAnnularWeight,
    (annularSmoothBallCutoff_basic a R (hr.trans_le hrR)).2.2.1 x (hx.trans hrR),
    (annularSmoothBallCutoff_basic a r hr).2.2.1 x hx, sub_self, zero_smul]

theorem smoothAnnularKernel_zero_far {d : ℕ} (n : ℕ) (a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (x : Ambient d) (hx : 2 * R ≤ dist x a) :
    smoothAnnularKernel n a r R hr (hr.trans_le hrR) x = 0 := by
  rw [smoothAnnularKernel, smoothAnnularWeight,
    (annularSmoothBallCutoff_basic a R (hr.trans_le hrR)).2.2.2 x hx,
    (annularSmoothBallCutoff_basic a r hr).2.2.2 x (by linarith), sub_self, zero_smul]

theorem smoothAnnularKernel_eq_capped {d : ℕ} (n : ℕ) (a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (x : Ambient d) :
    smoothAnnularKernel n a r R hr (hr.trans_le hrR) x =
      smoothAnnularWeight a r R hr (hr.trans_le hrR) x • cappedRieszKernel n r (a, x) := by
  by_cases hx : r ≤ dist a x
  · rw [cappedRieszKernel_eq_kernel n r (a, x) hx]
    rfl
  · have hd : dist x a ≤ r := by rw [dist_comm]; exact (lt_of_not_ge hx).le
    have hw : smoothAnnularWeight a r R hr (hr.trans_le hrR) x = 0 := by
      rw [smoothAnnularWeight,
        (annularSmoothBallCutoff_basic a R (hr.trans_le hrR)).2.2.1 x (hd.trans hrR),
        (annularSmoothBallCutoff_basic a r hr).2.2.1 x hd, sub_self]
    simp only [smoothAnnularKernel, hw, zero_smul]

theorem smoothAnnularKernel_continuous {d : ℕ} (n : ℕ) (a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    Continuous (smoothAnnularKernel n a r R hr (hr.trans_le hrR)) := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  have hw : Continuous (smoothAnnularWeight a r R hr (hr.trans_le hrR)) :=
    (annularSmoothBallCutoff a R (hr.trans_le hrR)).continuous.sub
      (annularSmoothBallCutoff a r hr).continuous
  have hk : Continuous (fun x : Ambient d => cappedRieszKernel n r (a, x)) :=
    (cappedRieszKernel_continuous n r hr).comp (continuous_const.prodMk continuous_id)
  have heq : smoothAnnularKernel n a r R hr (hr.trans_le hrR) =
      fun x => smoothAnnularWeight a r R hr (hr.trans_le hrR) x • cappedRieszKernel n r (a, x) := by
    funext x
    exact smoothAnnularKernel_eq_capped n a r R hr hrR x
  rw [heq]
  exact hw.smul hk

theorem smoothAnnularKernel_hasCompactSupport {d : ℕ} (n : ℕ) (a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R) :
    HasCompactSupport (smoothAnnularKernel n a r R hr hR) := by
  exact ((annularSmoothBallCutoff a R hR).hasCompactSupport.sub
    (annularSmoothBallCutoff a r hr).hasCompactSupport).smul_right

def scalarSmoothAnnularTest {d : ℕ} (n : ℕ) (e a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) : C_c(Ambient d, ℝ) :=
  ⟨⟨fun x => inner ℝ e (smoothAnnularKernel n a r R hr (hr.trans_le hrR) x),
    continuous_const.inner (smoothAnnularKernel_continuous n a r R hr hrR)⟩,
    (smoothAnnularKernel_hasCompactSupport n a r R hr (hr.trans_le hrR)).comp_left
      (g := fun v => inner ℝ e v) (by simp)⟩

end

end RieszRectifiability

end OAI
