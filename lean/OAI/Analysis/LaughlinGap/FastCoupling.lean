import Mathlib
import OAI.Analysis.LaughlinGap.RationalCreatedGram
import OAI.Analysis.LaughlinGap.RationalFourComputable

namespace OAI

/-! Fast Coupling. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

def chooseFast (n k : ℕ) : ℕ := n.descFactorial k / k.factorial
lemma chooseFast_eq (n k : ℕ) : chooseFast n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

def uFast (c z T p : ℕ) : ℚ :=
  if z ≤ T then ∑ h ∈ Finset.range (p+1),
    (-1:ℚ)^(z-h) * (chooseFast z h) * (chooseFast (T-z) (p-h)) * (c:ℚ)^(p-h) else 0

lemma uCoefficient_eq_fast (c z T p : ℕ) : uCoefficient c z T p = uFast c z T p := by
  simp only [uCoefficient,uFast,chooseFast_eq]

end LaughlinGap.Spin

namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def vFast (D T r p j k : ℕ) : ℚ :=
  if D ≤ T ∧ r ≤ j+k ∧ p+j+k=T then
    uFast 1 r (j+k) j * uFast 1 (D-r) (T-r) p else 0

lemma vCoefficient_eq_fast (D T r p j k : ℕ) : vCoefficient D T r p j k = vFast D T r p j k := by
  simp only [vCoefficient,vFast,uCoefficient_eq_fast]

def RationalRow.fourSumEval (r : RationalRow) (D s : ℕ) (i k : Fin 9) : ℚ :=
  ∑ p : Fin 8, if h : p.val ≤ r.t.val+i.val ∧ r.t.val+i.val-p.val < 9 then
    r.alpha p ⟨r.t.val+i.val-p.val,h.2⟩ *
      vFast D (r.t.val+i.val+k.val) s p.val (r.t.val+i.val-p.val) k.val *
        (2:ℚ)^((s+1)/2+p.val) else 0

def RationalRow.fourMatrixEval (r : RationalRow) (D u v : ℕ) : ℚ :=
  -(∑ i : Fin 9, ∑ k : Fin 9, fourRowFactor r.t.val D i.val k.val *
    r.fourSumEval D u i k * r.fourSumEval D v k i)

lemma RationalRow.fourMatrix_eq_eval (r : RationalRow) (D : ℕ) (u v : FourCopy D) :
    r.fourMatrix D u v = r.fourMatrixEval D u.val.val v.val.val := by
  simp only [RationalRow.fourMatrix_eq_fast,RationalRow.fourMatrixFast,RationalRow.fourMatrixEval,
    RationalRow.fourSumFast,RationalRow.fourSumEval,vCoefficient_eq_fast]

def fourTermEval (D r : ℕ) (a : FourTerm D) : ℚ :=
  vFast D D r (fourTermP a) (fourTermJ a) (fourTermK a) * (2:ℚ)^((r+1)/2) *
    ((fourTermX a:ℚ)-(fourTermY a:ℚ)) * (fourTermP a).factorial *
      (fourTermJ a).factorial * (fourTermK a).factorial / (2:ℚ)^D

lemma fourTermCoefficient_eq_eval (D r : ℕ) (a : FourTerm D) :
    fourTermCoefficient D r a = fourTermEval D r a := by
  simp only [fourTermCoefficient,fourTermEval,vCoefficient_eq_fast]

lemma fourColumn_eq_fiber {D : ℕ} (hD : D ≤ 23) (r : ℕ) (A : Finset (Fin 25))
    (s : Finset (FourTerm D)) (hs : ∀ a, (fourTermLabels hD a).toFinset=A ↔ a ∈ s) :
    fourColumn hD r A = ∑ a ∈ s, fourTermEval D r a * Occupation.wordSign (fourTermLabels hD a) := by
  simp only [fourColumn,hs,fourTermCoefficient_eq_eval,Finset.sum_ite_mem,Finset.univ_inter]

end LaughlinGap.RealOccupation

end

end OAI
