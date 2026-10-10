import OAI.Combinatorics.ContingencyTables.Transport.ResidualEnumerationBounds
import OAI.Combinatorics.ContingencyTables.Transport.CacheBoxBounds

namespace OAI

/-! # One scale for all boxes in the rare exact correction -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts
open scoped BigOperators Classical
noncomputable section

attribute [local irreducible] profilePaddedMargins

def exactBoxScale {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) : ℕ :=
  2^(40*((dimensionAllowance (I := Fin m) (J := Fin n))^3*smallBinaryLength r c))

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "dim" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "bits" => smallBinaryLength r c

private lemma normalized_base_bound (b l s : ℕ) (hb : 1 ≤ b)
    (hl : l ≤ 2^b) (hs : s+1 ≤ 2^(4*b)) : l*s+1 ≤ 2^(6*b) := by
  have hm := Nat.mul_le_mul hl (show s ≤ 2^(4*b) by omega)
  have he : (2:ℕ)^b*2^(4*b)=2^(5*b) := by
    calc
      _ = 2^(b+4*b) := (pow_add 2 b (4*b)).symm
      _ = _ := congrArg (fun k : ℕ => (2:ℕ)^k) (by omega)
  rw [he] at hm
  have hp : 1 ≤ (2:ℕ)^(5*b) := one_le_pow₀ (by decide)
  calc
    _ ≤ 2*2^(5*b) := by omega
    _ = 2^(5*b+1) := by rw [pow_succ]; omega
    _ ≤ 2^(6*b) := Nat.pow_le_pow_right (by decide) (by omega)

lemma exactBoxScale_pos : 1 ≤ exactBoxScale r c := by
  exact one_le_pow₀ (by decide)

lemma normalized_profile_completion_count (v : ProfileCheckData)
    (hr : v.1.2.1=List.ofFn r) (hc : v.1.2.2=List.ofFn c) (h : ℕ) :
    gridStateCount (completionEnumerationData
      (canonicalCountInput (residualParameters ((v,dim^12),(dim,h)))).1.1) ≤
      exactBoxScale r c := by
  let R := profilePaddedMargins true (v,dim^12)
  let C := profilePaddedMargins false (v,dim^12)
  have hd : 1 ≤ dim := by unfold dimensionAllowance; omega
  have hb : 1 ≤ bits := hd.trans (smallBinaryLength_parameters r c).2.1
  have hdb : dim ≤ 2^bits := by
    have h1 : dim ≤ bits := (smallBinaryLength_parameters r c).2.1
    exact h1.trans (Nat.le_of_lt (Nat.lt_two_pow_self))
  have hR : R.length ≤ dim := by
    have ht := profilePaddedMargins_length true (v,dim^12)
    simp only [hr,ite_true,List.length_ofFn] at ht
    have hm : m ≤ dim := by unfold dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
    exact ht.trans hm
  have hC : C.length ≤ dim := by
    have ht := profilePaddedMargins_length false (v,dim^12)
    simp only [Bool.false_eq_true,ite_false,hc,List.length_ofFn] at ht
    have hn : n ≤ dim := by unfold dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
    exact ht.trans hn
  have hsum : R.sum+1 ≤ 2^(4*bits) := arbitrary_profile_margin_sum r c v hr hc
  have hbase : R.length*R.sum+1 ≤ 2^(6*bits) :=
    normalized_base_bound bits R.length R.sum hb (hR.trans hdb) hsum
  have hn := canonicalCompletion_count_le (residualParameters ((v,dim^12),(dim,h)))
  change _ ≤ (R.length*R.sum+1)^(R.length*C.length) at hn
  have hprod : R.length*C.length ≤ dim^2 := by simpa only [pow_two] using Nat.mul_le_mul hR hC
  have h23 : dim^2 ≤ dim^3 := Nat.pow_le_pow_right hd (by decide)
  calc
    _ ≤ (R.length*R.sum+1)^(R.length*C.length) := hn
    _ ≤ (2^(6*bits))^(dim^2) :=
      (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right (by positivity) hprod)
    _ = 2^((6*bits)*dim^2) := (pow_mul _ _ _).symm
    _ ≤ exactBoxScale r c := Nat.pow_le_pow_right (by decide) (by nlinarith)

lemma normalized_profile_dense_grid (v : ProfileCheckData)
    (hr : v.1.2.1=List.ofFn r) (hc : v.1.2.2=List.ofFn c) (h : ℕ) :
    let z := (canonicalCountInput (residualParameters ((v,dim^12),(dim,h)))).1
    (4*z.2.1^8)^tabulationDimension z ≤ exactBoxScale r c := by
  let z := (canonicalCountInput (residualParameters ((v,dim^12),(dim,h)))).1
  have hd : 1 ≤ dim := by unfold dimensionAllowance; omega
  have hb : 1 ≤ bits := hd.trans (smallBinaryLength_parameters r c).2.1
  have hr' := profilePaddedMargins_length true (v,dim^12)
  have hc' := profilePaddedMargins_length false (v,dim^12)
  simp only [hr,ite_true,List.length_ofFn] at hr'
  simp only [Bool.false_eq_true,ite_false,hc,List.length_ofFn] at hc'
  have hm : m ≤ dim := by unfold dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  have hn : n ≤ dim := by unfold dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  have hq : tabulationDimension z ≤ dim^2 := by
    unfold tabulationDimension z canonicalCountInput swapMargins residualParameters
    simp only [swapZeroList_length,List.length_tail]
    simpa only [pow_two] using Nat.mul_le_mul
      ((Nat.sub_le _ _).trans (hr'.trans hm)) ((Nat.sub_le _ _).trans (hc'.trans hn))
  have hbase : 4*dim^8 ≤ 2^(10*dim) := by
    have hdim : dim ≤ 2^dim := Nat.le_of_lt (Nat.lt_two_pow_self)
    calc
      _ ≤ 4*(2^dim)^8 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hdim 8)
      _ = 2^(dim*8+2) := by rw [←pow_mul,pow_add]; norm_num; ring
      _ ≤ 2^(10*dim) := Nat.pow_le_pow_right (by decide) (by omega)
  change (4*dim^8)^tabulationDimension z ≤ exactBoxScale r c
  calc
    _ ≤ (2^(10*dim))^(dim^2) :=
      (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right (by positivity) hq)
    _ = 2^((10*dim)*dim^2) := (pow_mul _ _ _).symm
    _ ≤ exactBoxScale r c := Nat.pow_le_pow_right (by decide) (by
      have hbits : dim^3 ≤ dim^3*bits := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (dim^3) hb
      nlinarith)

end
end ContingencyTables.SmallGraphProfiles

end OAI
