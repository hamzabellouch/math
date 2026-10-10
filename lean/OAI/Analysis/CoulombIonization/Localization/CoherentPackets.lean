import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TfDilation

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff FourierTransform

namespace CoulombAtom

def coherentPacket (g : Space → ℂ) (z p x : Space) : ℂ :=
  g (x-z) * Complex.exp ((inner ℝ p x : ℂ) * Complex.I)

def coherentOverlap (g u : Space → ℂ) (z p : Space) : ℂ :=
  ∫ x : Space, conj (coherentPacket g z p x) * u x

lemma coherentPacket_norm (g : Space → ℂ) (z p x : Space) :
    ‖coherentPacket g z p x‖ = ‖g (x-z)‖ := by
  simp [coherentPacket,Complex.norm_exp_ofReal_mul_I]

lemma coherentPacket_smooth {g : Space → ℂ} (hg : ContDiff ℝ ∞ g) (z p : Space) :
    ContDiff ℝ ∞ (coherentPacket g z p) := by
  apply (hg.comp (contDiff_id.sub contDiff_const)).mul
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp (innerSL ℝ p).contDiff).mul contDiff_const)

lemma coherentPacket_compact {g : Space → ℂ} (hg : HasCompactSupport g) (z p : Space) :
    HasCompactSupport (coherentPacket g z p) := by
  exact (hg.comp_homeomorph (Homeomorph.subRight z)).mul_right

lemma coherentOverlap_fourier (g u : Space → ℂ) (z ξ : Space) :
    coherentOverlap g u z ((2*Real.pi) • ξ) =
      𝓕 (fun x : Space => conj (g (x-z))*u x) ξ := by
  rw [Real.fourier_eq']
  unfold coherentOverlap coherentPacket
  apply integral_congr_ae
  filter_upwards [] with x
  have he : conj ((inner ℝ ((2*Real.pi) • ξ) x : ℂ)*Complex.I) =
      ((-2*Real.pi*inner ℝ x ξ : ℝ) : ℂ)*Complex.I := by
    simp only [inner_smul_left,conj_trivial,map_mul,Complex.conj_ofReal,Complex.conj_I,
      Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat,map_ofNat,real_inner_comm ξ x]
    ring
  rw [map_mul,← Complex.exp_conj,he]
  simp only [smul_eq_mul]
  ring

lemma coherentOverlap_plancherel {g u : Space → ℂ}
    (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u) (z : Space) :
    (∫ ξ : Space, ‖coherentOverlap g u z ((2*Real.pi) • ξ)‖^2) =
      ∫ x : Space, ‖g (x-z)‖^2 * ‖u x‖^2 := by
  have hc : HasCompactSupport (fun x : Space => conj (g (x-z))*u x) := hcu.mul_left
  have hd : ContDiff ℝ ∞ (fun x : Space => conj (g (x-z))*u x) :=
    (Complex.conjCLE.contDiff.comp (hg.comp (contDiff_id.sub contDiff_const))).mul hu
  have hp := SchwartzMap.integral_norm_sq_fourier (hc.toSchwartzMap hd)
  change (∫ ξ : Space, ‖𝓕 (fun x : Space => conj (g (x-z))*u x) ξ‖^2) =
    ∫ x : Space, ‖conj (g (x-z))*u x‖^2 at hp
  simpa only [coherentOverlap_fourier,norm_mul,Complex.norm_conj,mul_pow] using hp

lemma coherentOverlap_momentum {g u : Space → ℂ}
    (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u) (hcu : HasCompactSupport u) (z : Space) :
    ((2*Real.pi)^3)⁻¹ * (∫ p : Space, ‖coherentOverlap g u z p‖^2) =
      ∫ x : Space, ‖g (x-z)‖^2 * ‖u x‖^2 := by
  have hp := coherentOverlap_plancherel hg hu hcu z
  rw [Measure.integral_comp_smul_of_nonneg volume (fun p : Space => ‖coherentOverlap g u z p‖^2)
    (2*Real.pi) (hR := by positivity),space_finrank] at hp
  simpa only [zpow_neg,zpow_natCast,smul_eq_mul] using hp

end CoulombAtom

end

end OAI
