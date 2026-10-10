import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalShellEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellGoodPoint

namespace OAI

/-! The normalized physical shell energy supplies bounded Cauchy data at
a point in the first half of the shell. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralPhysicalShell_good_point (R B M mu : ℝ) (hR : 0 < R) (hRB : R < B)
    (hmu : 0 ≤ mu) (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hbound : (∫ r in R..B, spectralPhysicalShellDensity f g r) ≤ M)
    (hrobin : ∀ r ∈ Icc R B,
      let q := spectralPhysicalLiouvillePair f g r
      mu*(‖q.1.1‖+‖q.2.1‖) ≤ 2*(‖q.1.2‖+‖q.2.2‖)) :
    ∃ r ∈ Icc R ((R+B)/2),
      let q := spectralPhysicalLiouvillePair f g r
      let A := 2*(1+(11/(2*R)+B/4)^2)*M/((R+B)/2-R)
      ‖q.1.2‖^2+‖q.2.2‖^2 ≤ A ∧
        mu^2*(‖q.1.1‖^2+‖q.2.1‖^2) ≤ 8*A := by
  let q := spectralPhysicalLiouvillePair f g
  have hq := spectralPhysicalLiouvillePair_continuous_shell R B hR f g hf hg
  have henergy := spectralPhysicalLiouvillePair_shell_integral R B M hR hRB.le f g hf hg hbound
  have hhR : R ≤ (R+B)/2 := by linarith
  have hhB : (R+B)/2 ≤ B := by linarith
  have hqE := (hq.fst.snd.norm.pow 2).add (hq.snd.snd.norm.pow 2)
  have hint : (∫ r in R..((R+B)/2), ‖(q r).1.2‖^2+‖(q r).2.2‖^2) ≤
      ∫ r in R..B, ‖(q r).1.2‖^2+‖(q r).2.2‖^2 :=
    intervalIntegral.integral_mono_interval le_rfl hhR hhB
      (Filter.Eventually.of_forall (fun _ => by positivity)) (hqE.intervalIntegrable_of_Icc hRB.le)
  exact spectral_shell_good_point R ((R+B)/2) (2*(1+(11/(2*R)+B/4)^2)*M) mu
    (by linarith) hmu q (hq.mono (Icc_subset_Icc le_rfl hhB))
    (fun r hr => hrobin r ⟨hr.1,hr.2.trans hhB⟩) (hint.trans henergy)

end DefocusingNLS

end OAI
