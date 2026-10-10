import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.Iterates

namespace OAI

section

noncomputable section
namespace OriginalJiangSu
open JiangSuConstruction
open scoped CStarAlgebra

lemma Multiplicities.zero_division {p q : ℕ} (hp : 0<p) (m : Multiplicities p q) :
    m.r+q*m.delta=m.k := by
  apply Nat.eq_of_mul_eq_mul_left hp
  calc p*(m.r+q*m.delta)=p*m.r+(p*q)*m.delta := by ring
       _=p*m.k := m.zero_reduced

lemma Multiplicities.one_division {p q : ℕ} (hq : 0<q) (m : Multiplicities p q) :
    m.s+p*m.gamma=m.l := by
  apply Nat.eq_of_mul_eq_mul_left hq
  calc q*(m.s+p*m.gamma)=q*m.s+(p*q)*m.gamma := by ring
       _=q*m.l := m.one_reduced

lemma Multiplicities.r_eq_mod {p q : ℕ} (hp : 0<p) (m : Multiplicities p q) :
    m.r=m.k%q := by
  rw [← m.zero_division hp,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt m.r_lt]

lemma Multiplicities.s_eq_mod {p q : ℕ} (hq : 0<q) (m : Multiplicities p q) :
    m.s=m.l%p := by
  rw [← m.one_division hq,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt m.s_lt]

lemma Multiplicities.delta_eq_div {p q : ℕ} (hp : 0<p) (hq : 0<q)
    (m : Multiplicities p q) : m.delta=m.k/q := by
  rw [← m.zero_division hp,Nat.add_mul_div_left _ _ hq,Nat.div_eq_of_lt m.r_lt]
  simp

lemma Multiplicities.gamma_eq_div {p q : ℕ} (hp : 0<p) (hq : 0<q)
    (m : Multiplicities p q) : m.gamma=m.l/p := by
  rw [← m.one_division hq,Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt m.s_lt]
  simp

lemma initial_dimensions : (pair 0).p=2 ∧ (pair 0).q=3 := ⟨rfl,rfl⟩
lemma successor_dimensions (n : ℕ) :
    (pair (n+1)).p=(pair n).p*(stageMultiplicities n).k ∧
    (pair (n+1)).q=(pair n).q*(stageMultiplicities n).l := ⟨rfl,rfl⟩

theorem original_block_counts (n : ℕ) :
    let p := (pair n).p
    let q := (pair n).q
    let m := stageMultiplicities n
    m.lower=m.l*(m.k%q) ∧ m.upper=m.k*(m.l%p) ∧
      m.middle=m.k*m.l-m.l*(m.k%q)-m.k*(m.l%p) ∧
      0 < m.lower ∧ 0 < m.upper ∧ 0 < m.middle := by
  dsimp only
  let m := stageMultiplicities n
  have hp : 0<(pair n).p := by have := (pair n).p_gt; omega
  have hq : 0<(pair n).q := by have := (pair n).q_gt; omega
  have hl : m.lower=m.l*(m.k%(pair n).q) := m.lower_eq.trans (congrArg (m.l*·) (m.r_eq_mod hp))
  have hu : m.upper=m.k*(m.l%(pair n).p) := m.upper_eq.trans (congrArg (m.k*·) (m.s_eq_mod hq))
  refine ⟨hl,hu,?_,m.lower_pos,m.upper_pos,m.middle_pos⟩
  change m.middle=m.k*m.l-m.l*(m.k%(pair n).q)-m.k*(m.l%(pair n).p)
  rw [←hl,←hu]
  have := m.total
  omega

theorem original_eigenvalues (n : ℕ) (t : Interval) :
    (∀ j : Fin (stageMultiplicities n).lower,
      (family (stageMultiplicities n) (Sum.inl j) t).val=t.val/2) ∧
    (∀ j : Fin (stageMultiplicities n).upper,
      (family (stageMultiplicities n) (Sum.inr (Sum.inl j)) t).val=(t.val+1)/2) ∧
    (∀ j : Fin (stageMultiplicities n).middle,
      (family (stageMultiplicities n) (Sum.inr (Sum.inr j)) t).val=1/2) :=
  ⟨fun _=>rfl,fun _=>rfl,fun _=>rfl⟩

theorem original_endpoint_fibres (n : ℕ) (f : Stage n) :
    (stageStep n f).val leftEndpoint ∈
      (leftAmplification (pair (n+1)).p (pair (n+1)).q).range ∧
    (stageStep n f).val rightEndpoint ∈
      (rightAmplification (pair (n+1)).p (pair (n+1)).q).range :=
  (stageStep n f).property

end OriginalJiangSu

end
end

end OAI
