import OAI.NumberTheory.DirichletL.Detector.MellinGuarded
import OAI.NumberTheory.DirichletL.Detector.RowAnalytic
import OAI.NumberTheory.DirichletL.Detector.MellinBoundary

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein ProbeRow
attribute [local fun_prop] fullIdealWeight_continuous
local notation "O" => ActualEisensteinCubic.O
abbrev FullHighIndex := NonzeroFrequency×((Ideal O×Ideal O)×(Ideal O×Ideal O))

def initialHighMajorant (σ υ ξ : ℝ) (p : FullHighIndex) : ℝ :=
  ‖frequencyWeight (ξ:ℂ) p.1‖*highAbsoluteMajorant (σ:ℂ) (υ:ℂ) (ξ:ℂ) p.2

lemma initialHighMajorant_nonneg (σ υ ξ : ℝ) (p : FullHighIndex) :
    0≤ initialHighMajorant σ υ ξ p := mul_nonneg (norm_nonneg _) (highAbsoluteMajorant_nonneg _ _ _ _)

lemma initialHighMajorant_summable (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ) :
    Summable (initialHighMajorant σ υ ξ) := by
  exact (frequencyWeight_summable_norm (ξ:ℂ) hξ).mul_of_nonneg
    (highAbsoluteMajorant_summable (σ:ℂ) (υ:ℂ) (ξ:ℂ) hσ hυ (by simpa using (show (1/6:ℝ)<ξ by linarith)))
    (fun _=>norm_nonneg _) (highAbsoluteMajorant_nonneg _ _ _)

lemma frequencyWeight_norm_eq_of_re (z z' : ℂ) (h : z.re=z'.re) (H : NonzeroFrequency) :
    ‖frequencyWeight z H‖=‖frequencyWeight z' H‖ := by simp only [frequencyWeight_norm,h]

lemma highAbsoluteMajorant_eq_of_re (x w z x' w' z' : ℂ)
    (hx : x.re=x'.re) (hw : w.re=w'.re) (hz : z.re=z'.re)
    (p : (Ideal O×Ideal O)×(Ideal O×Ideal O)) :
    highAbsoluteMajorant x w z p=highAbsoluteMajorant x' w' z' p := by
  unfold highAbsoluteMajorant
  rw [fullIdealWeight_norm_eq_of_re (x-1/2) (x'-1/2) (by simp [hx]),
    fullIdealWeight_norm_eq_of_re (3*x-2) (3*x'-2) (by simp [hx]),
    fullIdealWeight_norm_eq_of_re (w-1) (w'-1) (by simp [hw]),
    fullIdealWeight_norm_eq_of_re (6*z) (6*z') (by simp [hz])]

def fullHighCoefficient (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (x w z : ℂ) (p : FullHighIndex) : ℂ :=
  mask p.1*frequencyWeight z p.1*
    markedIdealHighSummand S D η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2

lemma fullHighCoefficient_norm_le (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (hm : ∀H,‖mask H‖≤1) (x w z : ℂ)
    (σ υ ξ : ℝ) (hx : x.re=σ) (hw : w.re=υ) (hz : z.re=ξ) (p : FullHighIndex) :
    ‖fullHighCoefficient S D η mask x w z p‖≤ initialHighMajorant σ υ ξ p := by
  unfold fullHighCoefficient
  rw [norm_mul,norm_mul]
  have hb := (markedIdealHighSummand_norm_le S D η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2).trans
    (bareIdealHighSummand_norm_le η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
  calc
    _ ≤ (1*‖frequencyWeight z p.1‖)*highAbsoluteMajorant x w z p.2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hm _) (norm_nonneg _)) hb (norm_nonneg _) (by positivity)
    _ = initialHighMajorant σ υ ξ p := by
      rw [one_mul,frequencyWeight_norm_eq_of_re z (ξ:ℂ) hz,
        highAbsoluteMajorant_eq_of_re x w z (σ:ℂ) (υ:ℂ) (ξ:ℂ) hx hw hz]
      rfl

lemma fullHighCoefficient_continuous (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (p : FullHighIndex) :
    Continuous (fun q : (ℂ × ℂ) × ℂ => fullHighCoefficient S D η mask q.1.1 q.1.2 q.2 p) := by
  have hH : (elementNorm p.1.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (elementNorm_pos _ p.1.property).ne'
  unfold fullHighCoefficient frequencyWeight markedIdealHighSummand bareIdealHighSummand
  have hc : Continuous (fun q : (ℂ × ℂ) × ℂ => (elementNorm p.1.val:ℂ)^(-q.2)) :=
    continuous_snd.neg.const_cpow (Or.inl hH)
  have h1 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight (q.1.1+1/2) p.2.1.1) :=
    (fullIdealWeight_continuous _).comp (by fun_prop)
  have h2 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight (1+3*q.1.1) p.2.1.2) :=
    (fullIdealWeight_continuous _).comp (by fun_prop)
  have h3 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight q.1.2 p.2.2.1) :=
    (fullIdealWeight_continuous _).comp (by fun_prop)
  have h4 : Continuous (fun q : (ℂ × ℂ) × ℂ => fullIdealWeight (6*q.2) p.2.2.2) :=
    (fullIdealWeight_continuous _).comp (by fun_prop)
  exact (continuous_const.mul hc).mul
    (continuous_const.mul ((((continuous_const.mul h1).mul h2).mul h3).mul h4))

end SevenEighths.ProbePhysical
end

end OAI
