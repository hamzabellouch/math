import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularKernel
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialIntegralRegularity

namespace OAI

/-! The regular spectral average preserves every finite order at the origin. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS

theorem homogeneousGlued_average_contDiffOn (d n : ℕ) (h R : ℝ) (hR : 0 < R)
    (f : ℝ → ℂ) (hf : ContDiffOn ℝ n f (Icc 0 R)) :
    ContDiffOn ℝ n (spectralRegularAverage d h f) (Icc 0 R) := by
  let S : Set (ℝ × ℝ) := Icc 0 R ×ˢ Icc 0 1
  let K : ℝ × ℝ → ℂ := fun p => (p.2 : ℂ) ^ d *
    Complex.exp (Complex.I * (h * p.1 ^ 2 * (p.2 ^ 2 - 1) / 4 : ℝ)) * f (p.1 * p.2)
  have hm : MapsTo (fun p : ℝ × ℝ => p.1 * p.2) S (Icc 0 R) := by
    intro p hp
    exact ⟨mul_nonneg hp.1.1 hp.2.1,
      (mul_le_of_le_one_right hp.1.1 hp.2.2).trans hp.1.2⟩
  have harg : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 * p.2) S := by fun_prop
  have hfc := hf.comp harg hm
  have ht : ContDiffOn ℝ n (fun p : ℝ × ℝ => (p.2 : ℂ)) S :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn contDiff_snd.contDiffOn
  have he0 : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => h * p.1 ^ 2 * (p.2 ^ 2 - 1) / 4) S := by fun_prop
  have he : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
      Complex.exp (Complex.I * (h * p.1 ^ 2 * (p.2 ^ 2 - 1) / 4 : ℝ))) S :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn he0)).cexp
  have hK : ContDiffOn ℝ n K S := ((ht.pow d).mul he).mul hfc
  have hi := radial_rectangle_integral_contDiffOn R hR n K hK
  apply hi.congr
  intro r _
  change (∫ t in (0 : ℝ)..1, K (r, t)) = ∫ t in Icc (0 : ℝ) 1, K (r, t)
  rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]

theorem homogeneousGlued_origin_smooth (d : ℕ) (R : ℝ) (hR : 0 < R)
    (A B : ℝ → ℂ) (cp cm : ℂ)
    (hA : ContDiffOn ℝ ∞ A (Icc 0 R)) (hB : ContDiffOn ℝ ∞ B (Icc 0 R))
    (F G : ℝ → ℂ) (hF : ContinuousOn F (Icc 0 R)) (hG : ContinuousOn G (Icc 0 R))
    (hdF : ∀ r ∈ Icc 0 R, HasDerivWithinAt F
      ((r : ℂ) * spectralRegularAverage d 1
        (fun t => A t * F t + B t * G t - cp * F t) r) (Icc 0 R) r)
    (hdG : ∀ r ∈ Icc 0 R, HasDerivWithinAt G
      ((r : ℂ) * spectralRegularAverage d (-1)
        (fun t => star (B t) * F t + star (A t) * G t - cm * G t) r) (Icc 0 R) r) :
    ContDiffOn ℝ ∞ F (Icc 0 R) ∧ ContDiffOn ℝ ∞ G (Icc 0 R) := by
  have hu := uniqueDiffOn_Icc hR
  have hn : ∀ n : ℕ, ContDiffOn ℝ n F (Icc 0 R) ∧ ContDiffOn ℝ n G (Icc 0 R) := by
    intro n
    induction n with
    | zero => simpa only [Nat.cast_zero, contDiffOn_zero] using And.intro hF hG
    | succ n ih =>
      have hAn : ContDiffOn ℝ n A (Icc 0 R) := hA.of_le (by simp)
      have hBn : ContDiffOn ℝ n B (Icc 0 R) := hB.of_le (by simp)
      have hAs := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hAn
      have hBs := (starL' ℝ : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hBn
      have hp := homogeneousGlued_average_contDiffOn d n 1 R hR
        (fun t => A t * F t + B t * G t - cp * F t)
        (((hAn.mul ih.1).add (hBn.mul ih.2)).sub (contDiffOn_const.mul ih.1))
      have hm := homogeneousGlued_average_contDiffOn d n (-1) R hR
        (fun t => star (B t) * F t + star (A t) * G t - cm * G t)
        (((hBs.mul ih.1).add (hAs.mul ih.2)).sub (contDiffOn_const.mul ih.2))
      have hr : ContDiffOn ℝ n (fun r : ℝ => (r : ℂ)) (Icc 0 R) :=
        Complex.ofRealCLM.contDiff.contDiffOn
      constructor
      · rw [Nat.cast_succ]
        apply (contDiffOn_succ_iff_derivWithin hu).2
        refine ⟨fun r hr => (hdF r hr).differentiableWithinAt, by simp, ?_⟩
        apply (hr.mul hp).congr
        intro r hr
        exact (hdF r hr).derivWithin (hu r hr)
      · rw [Nat.cast_succ]
        apply (contDiffOn_succ_iff_derivWithin hu).2
        refine ⟨fun r hr => (hdG r hr).differentiableWithinAt, by simp, ?_⟩
        apply (hr.mul hm).congr
        intro r hr
        exact (hdG r hr).derivWithin (hu r hr)
  exact ⟨contDiffOn_infty.mpr (fun n => (hn n).1),
    contDiffOn_infty.mpr (fun n => (hn n).2)⟩

end DefocusingNLS

end OAI
