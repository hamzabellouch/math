import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusBoundBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction

theorem divisorCost_le {N : ℕ} {B : ℝ} {l : ℕ} (h : History l)
    (hb : factorBound N B h) : divisorCost h≤4^(l+1)*(N+1) := by
  induction h with
  | leaf a => simp [divisorCost]
  | @node l a p u hp hm left right il ir =>
    have hu : u.length≤N := hb.2.2.2.1
    have hl := il hb.2.2.2.2.2.1
    have hr := ir hb.2.2.2.2.2.2
    have hpow : 1≤4^(l+1) := one_le_pow₀ (by norm_num)
    have hmul := Nat.mul_le_mul_right (N+1) hpow
    simp only [one_mul] at hmul
    simp only [divisorCost]
    rw [pow_succ]
    nlinarith

theorem testCost_le {N : ℕ} {B : ℝ} {l : ℕ} (h : History l)
    (hb : factorBound N B h) : testCost h≤8^(l+1)*(N+1) := by
  induction h with
  | leaf a =>
    have ha : a.small.length≤N := hb.2.1
    simp only [testCost]
    omega
  | @node l a p u hp hm left right il ir =>
    have ha : a.small.length≤N := hb.2.1
    have hu : u.length≤N := hb.2.2.2.1
    have hl := il hb.2.2.2.2.2.1
    have hr := ir hb.2.2.2.2.2.2
    have hf := History.frequencies_length (History.node a p u hp hm left right)
    have htwo : 2^(l+1)≤8^(l+1) := Nat.pow_le_pow_left (by norm_num : 2≤8) (l+1)
    have hpow : 1≤8^(l+1) := one_le_pow₀ (by norm_num)
    have hmul := Nat.mul_le_mul_right N hpow
    simp only [one_mul] at hmul
    change (History.node a p u hp hm left right).frequencies.length+a.small.length+1+
      3*u.length+testCost left+testCost right≤_
    rw [pow_succ] at hf ⊢
    nlinarith

def pairedCostCoefficient (l : ℕ) : ℕ :=
  2*l*4^(l+1)+2*8^(l+1)+1

lemma pairedCostCoefficient_pos (l : ℕ) : 0<pairedCostCoefficient l := by
  unfold pairedCostCoefficient
  omega

theorem pairedCost_le {N : ℕ} {B : ℝ} {l : ℕ} (h g : History l)
    (hh : factorBound N B h) (hg : factorBound N B g)
    (outside : List ℕ) (hout : outside.length≤N) :
    l*(divisorCost h+divisorCost g)+testCost h+testCost g+outside.length≤
      pairedCostCoefficient l*(N+1) := by
  have hd := Nat.add_le_add (divisorCost_le h hh) (divisorCost_le g hg)
  have hm := Nat.mul_le_mul_left l hd
  have ht := Nat.add_le_add (testCost_le h hh) (testCost_le g hg)
  unfold pairedCostCoefficient
  nlinarith

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
