import OAI.Probability.ClassicalON.AmplitudeModular

namespace OAI

universe uV

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ClassicalON

def signValue (t : Bool) : ℝ := if t then 1 else -1

def signLaw : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

instance signLaw_isProbability : IsProbabilityMeasure signLaw := by
  constructor
  norm_num [signLaw,Measure.count_apply_finite]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

variable {V : Type uV} [Fintype V]

def isingReference : Measure (V → Bool) := Measure.pi (fun _ => signLaw)

instance isingReference_isProbability : IsProbabilityMeasure (isingReference (V := V)) := by
  unfold isingReference; infer_instance

def isingU (t : Bool×Bool) : ℝ := (signValue t.1+signValue t.2)/2

def isingW (t : Bool×Bool) : ℝ := (signValue t.1-signValue t.2)/2

omit [Fintype V] in
theorem isingUW_moment (k l : ℕ) :
    0≤∫ t : Bool×Bool,isingU t^k*isingW t^l ∂signLaw.prod signLaw := by
  rw [integral_prod _ (compact_integrable (by fun_prop))]
  simp only [signLaw,integral_smul_measure,ENNReal.toReal_inv,ENNReal.toReal_ofNat,
    smul_eq_mul,integral_count,Fintype.sum_bool]
  simp only [isingU,isingW,signValue,Bool.false_eq_true,ite_false,ite_true]
  norm_num
  by_cases hk : k=0 <;> by_cases hl : l=0
  · subst k; subst l; norm_num
  · subst k
    simp only [pow_zero,one_mul,zero_pow hl]
    have h' : -1≤(-1 : ℝ)^l := by
      simpa only [abs_pow,abs_neg,abs_one,one_pow] using neg_abs_le ((-1 : ℝ)^l)
    nlinarith
  · subst l
    simp only [pow_zero,mul_one,zero_pow hk]
    have h' : -1≤(-1 : ℝ)^k := by
      simpa only [abs_pow,abs_neg,abs_one,one_pow] using neg_abs_le ((-1 : ℝ)^k)
    nlinarith
  · simp [zero_pow hk,zero_pow hl]

omit [Fintype V] in
theorem isingUW_product_moment (l : List Bool) :
    0≤∫ t : Bool×Bool,(l.map (fun b => if b then isingU t else isingW t)).prod
      ∂signLaw.prod signLaw := by
  have he (t : Bool×Bool) :
      (l.map (fun b => if b then isingU t else isingW t)).prod =
      isingU t^(l.count true)*isingW t^(l.count false) := by
    induction l with
    | nil => simp
    | cons b l ih => cases b <;> simp [ih,pow_succ] <;> ring
  simp_rw [he]
  exact isingUW_moment _ _

end ClassicalON

end

end OAI
