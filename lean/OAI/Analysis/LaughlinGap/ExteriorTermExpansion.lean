import Mathlib
import OAI.Analysis.LaughlinGap.FourTransfer
import OAI.Analysis.LaughlinGap.RationalExterior

namespace OAI

/-! Exterior Term Expansion. -/

noncomputable section


namespace LaughlinGap.Occupation
open scoped BigOperators

def pairLeft {n p : ℕ} (hp : p+1 < n) (i : Fin ((p+2)/2)) : Fin n :=
  ⟨i.val,by have := i.isLt; omega⟩
def pairRight {n p : ℕ} (hp : p+1 < n) (i : Fin ((p+2)/2)) : Fin n :=
  ⟨p+1-i.val,by omega⟩

lemma localPairStar_sum {n p : ℕ} (hp : p+1 < n) :
    localPairStar n p = ∑ i : Fin ((p+2)/2),
      (limitingExteriorPairCoefficient p i.val (p+1-i.val):ℂ) •
        (annihilation (pairRight hp i) * annihilation (pairLeft hp i)) := by
  classical
  symm
  unfold localPairStar pairAnnihilator
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← Fintype.sum_prod_type']
  apply Finset.sum_bij_ne_zero (fun i _ _ => (pairLeft hp i,pairRight hp i))
  · simp
  · intro i hi h0 j hj h0' e
    exact Fin.ext (congrArg (fun a : Fin n × Fin n => a.1.val) e)
  · intro a ha h0
    have hlt : a.1 < a.2 := by
      by_contra h
      exact h0 (by simp [h])
    have he : a.1.val+a.2.val=p+1 := by
      by_contra h
      exact h0 (by simp [limitingExteriorPairCoefficient,h])
    let i : Fin ((p+2)/2) := ⟨a.1.val,by have := a.1.isLt; have := a.2.isLt; omega⟩
    have e₁ : pairLeft hp i=a.1 := rfl
    have e₂ : pairRight hp i=a.2 := Fin.ext (by dsimp [pairRight,i]; omega)
    refine ⟨i,Finset.mem_univ _,?_,by rw [e₁,e₂]⟩
    have ey : p+1-i.val=a.2.val := by dsimp [i]; omega
    simpa only [e₁,e₂,ey,ite_eq_left hlt] using h0
  · intro i hi h0
    have ht : pairLeft hp i < pairRight hp i := by have := i.isLt; change i.val < p+1-i.val; omega
    change _ = if pairLeft hp i < pairRight hp i then _ else _
    rw [ite_eq_left ht]
    rfl

end LaughlinGap.Occupation

namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

lemma fourLocalHighestStar_terms {D : ℕ} (hD : D ≤ 23) (r : FourCopy D) :
    fourLocalHighestStar hD r = ∑ a : FourTerm D,
      (fourBodyCoefficientStar D D r.val.val (fourTermP a) (fourTermJ a) (fourTermK a) *
        limitingExteriorPairCoefficient (fourTermP a) (fourTermX a) (fourTermY a):ℂ) •
          Occupation.word (fourTermLabels hD a) := by
  classical
  rw [fourLocalHighestStar,← (orbitalTripleEquiv D).sum_comp]
  simp only [fourHighestRowsStar]
  conv_rhs => rw [Fintype.sum_sigma]; simp only [Fintype.sum_prod_type]
  rw [Fintype.sum_sigma] 
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro j hj
  rw [Occupation.localPairStar_sum (by change D-n.val+1 < 25; omega)]
  simp only [Finset.mul_sum, mul_smul_comm,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [fourTermP,fourTermJ,fourTermK,fourTermX,fourTermY,fourTermLabels,
    localTripleP,localTripleJ,localTripleK,orbitalTripleEquiv,Occupation.pairLeft,Occupation.pairRight,
    Occupation.word_cons,Occupation.word_nil,one_mul,mul_assoc]
  rfl

end LaughlinGap.RealOccupation

end

end OAI
