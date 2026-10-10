import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Grid

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryNarrowGrid
open Finset

def primeWindow (q r R : ℕ) : Finset ℕ :=
  (Finset.Ioc (q*2^r) (q*2^(r+R))).filter Nat.Prime

def primeBin (i : ℕ×ℕ) : Finset ℕ := (Finset.Ioc (lower i) (upper i)).filter Nat.Prime

def evenBinLength (X : ℕ) (i : ℕ×ℕ) : ℕ := 2*(X/(2*upper i))

lemma lower_ge_start (q r R : ℕ) {i : ℕ×ℕ} (hi : i∈grid q r R) :
    q*2^r≤lower i := by
  have hr := (mem_Ico.mp (mem_product.mp hi).1).1
  have hq := (mem_Ico.mp (mem_product.mp hi).2).1
  exact Nat.mul_le_mul hq (Nat.pow_le_pow_right (by norm_num) hr)

lemma prime_window_bins (q r R : ℕ) :
    primeWindow q r R=(grid q r R).biUnion primeBin := by
  ext p
  simp only [primeWindow,primeBin,mem_filter,Finset.mem_Ioc,Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨hlo,hhi⟩,hp⟩
    obtain ⟨i,hi,hl,hu⟩ := grid_cover q r R p hlo hhi
    exact ⟨i,hi,⟨hl,hu⟩,hp⟩
  · rintro ⟨i,hi,⟨hl,hu⟩,hp⟩
    exact ⟨⟨lt_of_le_of_lt (lower_ge_start q r R hi) hl,
      hu.trans (upper_le_endpoint q r R hi)⟩,hp⟩

lemma prime_bins_disjoint (q r R : ℕ) (hq : 0<q) :
    (grid q r R : Set (ℕ×ℕ)).PairwiseDisjoint primeBin := by
  intro i hi j hj hij
  exact (grid_disjoint q r R hq hi hj hij).mono (filter_subset _ _) (filter_subset _ _)

lemma bin_width (q r R : ℕ) {i : ℕ×ℕ} (hi : i∈grid q r R) {p : ℕ}
    (hp : p∈Finset.Ioc (lower i) (upper i)) : q*(upper i-p)≤p := by
  have hq := (mem_Ico.mp (mem_product.mp hi).2).1
  have hlo := (Finset.mem_Ioc.mp hp).1
  have hup := (Finset.mem_Ioc.mp hp).2
  have he : upper i=lower i+2^i.1 := by unfold upper lower; ring
  have hd : upper i-p≤2^i.1 := by omega
  calc
    _ ≤ q*2^i.1 := Nat.mul_le_mul_left q hd
    _ ≤ lower i := Nat.mul_le_mul_right _ hq
    _ ≤ p := hlo.le

theorem even_bin_cutoff (q r R X : ℕ) (hq : 0<q) {i : ℕ×ℕ}
    (hi : i∈grid q r R) {p : ℕ} (hp : p∈primeBin i) :
    X-(X/q+2*(q*2^(r+R)))≤p*evenBinLength X i ∧ p*evenBinLength X i≤X := by
  have hpI := (mem_filter.mp hp).1
  have hpU := (Finset.mem_Ioc.mp hpI).2
  have hu := upper_le_endpoint q r R hi
  have hl := grid_lower_pos q r R hq hi
  have hU : 0<upper i := hl.trans_le (lower_le_upper i)
  have hv : upper i*evenBinLength X i≤X := by
    unfold evenBinLength
    have hh := Nat.div_mul_le_self X (2*upper i)
    nlinarith
  have hprod : p*evenBinLength X i≤X :=
    (Nat.mul_le_mul_right _ hpU).trans hv
  have hsmall : (upper i-p)*evenBinLength X i≤X/q := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    have hh := Nat.mul_le_mul_right (evenBinLength X i) (bin_width q r R hi hpI)
    nlinarith
  have hround : X≤upper i*evenBinLength X i+2*upper i := by
    have hh := Nat.lt_mul_div_succ X (by omega : 0<2*upper i)
    unfold evenBinLength
    nlinarith
  have hsplit : upper i*evenBinLength X i=
      p*evenBinLength X i+(upper i-p)*evenBinLength X i := by
    rw [←Nat.add_mul,Nat.add_sub_of_le hpU]
  refine ⟨?_,hprod⟩
  rw [hsplit] at hround
  omega

lemma even_bin_length_pos (q r R X : ℕ) (hq : 0<q)
    (hX : 2*(q*2^(r+R))≤X) {i : ℕ×ℕ} (hi : i∈grid q r R) :
    0<evenBinLength X i := by
  have hu := upper_le_endpoint q r R hi
  have hl := grid_lower_pos q r R hq hi
  have hU : 0<upper i := hl.trans_le (lower_le_upper i)
  unfold evenBinLength
  exact Nat.mul_pos (by norm_num) (Nat.div_pos (by omega) (by omega))

end OrdinaryNarrowGrid

end

end OAI
