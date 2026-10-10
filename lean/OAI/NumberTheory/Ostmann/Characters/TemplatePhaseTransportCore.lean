import OAI.NumberTheory.Ostmann.Characters.TransferAlgebra
import OAI.NumberTheory.Ostmann.Supply.FiniteParseval

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Characters.Template

section Field
variable {F:Type*} [Field F]

theorem left_phase_fraction (P s v w HL HR D:F)
    (he:s*P=v*HR-w*HL) (hL:HL=0) (hP:P≠0) (hR:HR≠0) :
    v/(P*D)=s/(HR*D) := by
  rw [div_mul_eq_div_div,div_mul_eq_div_div,transfer_left_phase he hL hP hR]

theorem right_phase_fraction (P s v w HL HR D:F)
    (he:s*P=v*HR-w*HL) (hR:HR=0) (hP:P≠0) (hL:HL≠0) :
    -(w/(P*D))=s/(HL*D) := by
  rw [←neg_div,div_mul_eq_div_div,div_mul_eq_div_div,transfer_right_phase he hR hP hL]

theorem outside_phase_fraction (P s v w HL HR D:F)
    (he:s*P=v*HR-w*HL) (hP:P≠0) (hL:HL≠0) (hR:HR≠0) :
    v/(P*HL*D)-w/(P*HR*D)=s/(HL*HR*D) := by
  have hh := congrArg (fun x:F => x/D) (transfer_shared_phase he hP hL hR)
  simpa only [sub_div,div_div] using hh
end Field

def translatedAdditivePhase {p:ℕ} [Fact p.Prime] (a v D:ZMod p) : ℂ :=
  ZMod.stdAddChar (-(a*(v/D)))

theorem translatedAdditivePhase_left {p:ℕ} [Fact p.Prime]
    (a P s v w HL HR D:ZMod p) (he:s*P=v*HR-w*HL)
    (hL:HL=0) (hP:P≠0) (hR:HR≠0) :
    translatedAdditivePhase a v (P*D)=translatedAdditivePhase a s (HR*D) := by
  unfold translatedAdditivePhase
  rw [left_phase_fraction P s v w HL HR D he hL hP hR]

theorem translatedAdditivePhase_right {p:ℕ} [Fact p.Prime]
    (a P s v w HL HR D:ZMod p) (he:s*P=v*HR-w*HL)
    (hR:HR=0) (hP:P≠0) (hL:HL≠0) :
    conj (translatedAdditivePhase a w (P*D))=translatedAdditivePhase a s (HL*D) := by
  unfold translatedAdditivePhase
  rw [Supply.conj_stdAddChar]
  congr 1
  have hh := right_phase_fraction P s v w HL HR D he hR hP hL
  rw [←hh]
  ring

theorem translatedAdditivePhase_outside {p:ℕ} [Fact p.Prime]
    (a P s v w HL HR D:ZMod p) (he:s*P=v*HR-w*HL)
    (hP:P≠0) (hL:HL≠0) (hR:HR≠0) :
    translatedAdditivePhase a v (P*HL*D)*conj (translatedAdditivePhase a w (P*HR*D))=
      translatedAdditivePhase a s (HL*HR*D) := by
  unfold translatedAdditivePhase
  rw [Supply.conj_stdAddChar,←AddChar.map_add_eq_mul]
  congr 1
  have hh := outside_phase_fraction P s v w HL HR D he hP hL hR
  rw [←hh]
  ring

end Ostmann.Characters.Template

end

end OAI
