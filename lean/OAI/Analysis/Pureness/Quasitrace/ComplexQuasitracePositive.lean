import OAI.Analysis.Pureness.Quasitrace.CentralQuasitraceCompression
import OAI.Analysis.Pureness.Quasitrace.AdditiveQuasitraceTrace

namespace OAI
noncomputable section
namespace CuntzPureness.ComplexQuasitrace
open CuntzTrace
open scoped ComplexOrder ComplexStarModule NNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : ComplexQuasitrace D)

omit [PartialOrder D] [StarOrderedRing D] in
lemma map_sub_commuting_selfAdjoint (a b : selfAdjoint D) (h : Commute a.1 b.1) :
    T (a.1-b.1)=T a.1-T b.1 := by
  have : IsStarNormal b.1 := b.2.isStarNormal
  have hn : T (-b.1) = -T b.1 := by
    simpa only [neg_one_smul,neg_one_mul] using T.map_smul_of_normal (-1) b.1
  simpa only [sub_eq_add_neg,hn] using
    T.map_add_commuting_selfAdjoint a ⟨-b.1,b.2.neg⟩ h.neg_right

def toPositiveQuasitrace
    (hmono : Monotone (fun a : Positive D => (T a.1).re)) : PositiveQuasitrace D where
  toFun a := (T a.1).re
  nonneg a := (Complex.nonneg_iff.mp (T.nonneg a.1 a.2)).1
  map_zero := by change (T 0).re=0; rw [T.map_zero,Complex.zero_re]
  map_add_commute a b h := congrArg Complex.re
    (T.map_add_commuting_selfAdjoint ⟨a.1,a.2.isSelfAdjoint⟩ ⟨b.1,b.2.isSelfAdjoint⟩ h)
  map_smul r a := by
    have : IsStarNormal a.1 := a.2.isSelfAdjoint.isStarNormal
    have h := T.map_smul_of_normal (r:ℂ) a.1
    have h' : T ((r:ℝ) • a.1) = (r:ℂ)*T a.1 := by
      simpa only [Complex.coe_smul,Complex.real_smul] using h
    simpa only [Positive.smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero] using congrArg Complex.re h'
  polar x := congrArg Complex.re (T.polar x)
  monotone := hmono

lemma toPositiveQuasitrace_positive
    (hmono : Monotone (fun a : Positive D => (T a.1).re)) (a : Positive D) :
    ((T.toPositiveQuasitrace hmono a : ℝ) : ℂ)=T a.1 :=
  (Complex.eq_re_of_ofReal_le (T.nonneg a.1 a.2)).symm

theorem toPositiveQuasitrace_complexValue
    (hmono : Monotone (fun a : Positive D => (T a.1).re)) (x : D) :
    (T.toPositiveQuasitrace hmono).complexValue x=T x := by
  have hsa (a : selfAdjoint D) :
      (((T.toPositiveQuasitrace hmono).selfAdjointValue a : ℝ) : ℂ)=T a.1 := by
    have hp := CFC.posPart_nonneg a.1
    have hn := CFC.negPart_nonneg a.1
    have he := T.map_sub_commuting_selfAdjoint ⟨a.1⁺,hp.isSelfAdjoint⟩
      ⟨a.1⁻,hn.isSelfAdjoint⟩ (commute_negPart_right (commute_posPart_left (Commute.refl a.1)))
    rw [CFC.posPart_sub_negPart a.1 a.2] at he
    change (((T a.1⁺).re-(T a.1⁻).re : ℝ) : ℂ)=T a.1
    rw [Complex.ofReal_sub]
    have hpR := Complex.eq_re_of_ofReal_le (T.nonneg a.1⁺ hp)
    have hnR := Complex.eq_re_of_ofReal_le (T.nonneg a.1⁻ hn)
    rw [← hpR,← hnR]
    exact he.symm
  have he := T.real_add_I (ℜ x) (ℑ x)
  rw [realPart_add_I_smul_imaginaryPart] at he
  change (((T.toPositiveQuasitrace hmono).selfAdjointValue (ℜ x) : ℝ) : ℂ)+
    Complex.I*(((T.toPositiveQuasitrace hmono).selfAdjointValue (ℑ x) : ℝ) : ℂ)=T x
  rw [hsa,hsa]
  exact he.symm
end CuntzPureness.ComplexQuasitrace

end

end OAI
