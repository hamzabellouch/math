import OAI.Combinatorics.PolynomialVacuum.Algebra.Table
import OAI.Combinatorics.PolynomialVacuum.Cylinder.ThreeSeams

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

 

def upTurn (h j : Spin) : ℤ := if h=.zero then charge j else if j=.zero then -charge h else charge h
def downTurn (h l : Spin) : ℤ := if h=.zero then -charge l else if l=.zero then charge h else -charge h
def occupied (h j : Spin) : ℕ := if h=.zero ∧ j=.zero then 0 else 1

noncomputable def anglePhase (a : ℤ) : ℂ := Complex.exp (Complex.I * (Real.pi : ℂ) * a / 24)

theorem anglePhase_three (a : ℤ) : anglePhase (3*a)=q^a := by
  rw [q,← Complex.exp_int_mul]
  unfold anglePhase
  congr 1
  push_cast
  ring

@[simp] theorem anglePhase_zero : anglePhase 0=1 := by simp [anglePhase]

 

noncomputable def honeycombPiece (out inp : Pair) (h : Spin) : ℂ :=
  if charge out.2=charge h+charge inp.2 ∧ charge inp.1=charge h+charge out.1 then
    xStar^(occupied h inp.2+occupied h out.1) *
    anglePhase (2*(upTurn h inp.2+downTurn h out.1)+5*(charge inp.1-charge out.2))
  else 0
noncomputable def honeycombEntry (out inp : Pair) : ℂ := ∑ h : Spin,honeycombPiece out inp h

lemma anglePhase_three_neg : anglePhase (-3)=q⁻¹ := by simpa using anglePhase_three (-1)
lemma anglePhase_three_pos : anglePhase 3=q := by simpa using anglePhase_three 1
lemma anglePhase_six_neg : anglePhase (-6)=(q⁻¹)^2 := by simpa [zpow_neg] using anglePhase_three (-2)
lemma anglePhase_six_pos : anglePhase 6=q^2 := by simpa using anglePhase_three 2
lemma anglePhase_nine_neg : anglePhase (-9)=(q⁻¹)^3 := by simpa [zpow_neg] using anglePhase_three (-3)
lemma anglePhase_nine_pos : anglePhase 9=q^3 := by simpa using anglePhase_three 3

 theorem honeycomb_entry_exact (out inp : Pair) :
    exchangeNumerator t 1 out inp=exchangeDenominator t 1*honeycombEntry out inp := by
  rw [exchangeNumerator_eq_table]
  rcases out with ⟨a,b⟩
  rcases inp with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [exchangeTable,honeycombEntry,sum_spin,honeycombPiece,charge,upTurn,downTurn,occupied,
      reduceCtorEq,ite_true,ite_false,
      and_true,and_false] <;>
    norm_num [anglePhase_three_neg,anglePhase_three_pos,anglePhase_six_neg,anglePhase_six_pos,
      anglePhase_nine_neg,anglePhase_nine_pos,exchangeDenominator,t,T,q_inv,xStar_polynomial] <;>
    ring_nf <;>
    simp only [q_pow_eight,q_pow_9,q_pow_10,q_pow_11,q_pow_12,q_pow_13,q_pow_14,q_pow_15,q_pow_16,
      q_pow_17,q_pow_18,q_pow_19,q_pow_20,q_pow_21,q_pow_22,q_pow_23,q_pow_24,q_pow_25,q_pow_26,q_pow_27,
      q_pow_28,q_pow_29,q_pow_30,q_pow_31,q_pow_32,q_pow_33,q_pow_34,q_pow_35,q_pow_36,q_pow_37,q_pow_38,
      q_pow_39,q_pow_40,q_pow_41,q_pow_42,q_pow_43,q_pow_45,q_pow_47,q_pow_49] <;> ring

end PolynomialVacuumAlgebra

end OAI
