import Mathlib

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
open MeasureTheory
open MeasureTheory Complex
open Finset Filter

namespace OrdinaryNarrowGrid

def grid (q r R : ℕ) : Finset (ℕ × ℕ) := Ico r (r+R) ×ˢ Ico q (2*q)
def lower (i : ℕ × ℕ) : ℕ := i.2 * 2^i.1
def upper (i : ℕ × ℕ) : ℕ := (i.2+1)*2^i.1

lemma mesh_cover (q v a : ℕ) (hv : 0<v) (hl : q*v<a) (hu : a≤2*q*v) :
    ∃ j∈Ico q (2*q), j*v<a ∧ a≤(j+1)*v := by
  refine ⟨(a-1)/v,mem_Ico.mpr ⟨?_,?_⟩,?_,?_⟩
  · apply (Nat.le_div_iff_mul_le hv).mpr
    omega
  · apply (Nat.div_lt_iff_lt_mul hv).mpr
    omega
  · have h := Nat.div_mul_le_self (a-1) v
    omega
  · have h := Nat.lt_mul_div_succ (a-1) hv
    rw [Nat.mul_comm v] at h
    omega

lemma grid_cover (q r R a : ℕ) (hl : q*2^r<a) (hu : a≤q*2^(r+R)) :
    ∃ i∈grid q r R, lower i<a ∧ a≤upper i := by
  induction R with
  | zero => simp only [Nat.add_zero] at hu; omega
  | succ R ih =>
    by_cases mid : a≤q*2^(r+R)
    · obtain ⟨i,hi,hlo,hup⟩ := ih mid
      refine ⟨i,mem_product.mpr ⟨?_,(mem_product.mp hi).2⟩,hlo,hup⟩
      obtain ⟨hir,hiR⟩ := mem_Ico.mp (mem_product.mp hi).1
      exact mem_Ico.mpr ⟨hir,by omega⟩
    · have hv : 0<2^(r+R) := by positivity
      have hu' : a≤2*q*2^(r+R) := by
        rw [Nat.add_succ, pow_succ] at hu
        nlinarith
      obtain ⟨j,hj,hlo,hup⟩ := mesh_cover q (2^(r+R)) a hv (by omega) hu'
      exact ⟨(r+R,j),mem_product.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,hj⟩,hlo,hup⟩

lemma grid_lower_pos (q r R : ℕ) (hq : 0<q) {i : ℕ×ℕ} (hi : i∈grid q r R) :
    0<lower i := by
  have hj := (mem_Ico.mp (mem_product.mp hi).2).1
  exact Nat.mul_pos (lt_of_lt_of_le hq hj) (by positivity)

lemma lower_le_upper (i : ℕ×ℕ) : lower i≤upper i := by
  unfold lower upper
  exact Nat.mul_le_mul_right _ (by omega)

lemma upper_le_two_lower (q r R : ℕ) (hq : 0<q) {i : ℕ×ℕ} (hi : i∈grid q r R) :
    upper i≤2*lower i := by
  have hj := (mem_Ico.mp (mem_product.mp hi).2).1
  unfold lower upper
  have hp : 0<2^i.1 := by positivity
  nlinarith

lemma upper_le_endpoint (q r R : ℕ) {i : ℕ×ℕ} (hi : i∈grid q r R) :
    upper i≤q*2^(r+R) := by
  obtain ⟨hir,hiR⟩ := mem_Ico.mp (mem_product.mp hi).1
  obtain ⟨hjq,hjQ⟩ := mem_Ico.mp (mem_product.mp hi).2
  have hp : 2^(i.1+1)≤2^(r+R) := Nat.pow_le_pow_right (by omega) (by omega)
  unfold upper
  calc
    (i.2+1)*2^i.1 ≤ (2*q)*2^i.1 := Nat.mul_le_mul_right _ (by omega)
    _ = q*2^(i.1+1) := by rw [pow_succ]; ring
    _ ≤ q*2^(r+R) := Nat.mul_le_mul_left q hp

lemma interval_disjoint_of_le {a b c d : ℕ} (h : b≤c) : Disjoint (Ioc a b) (Ioc c d) := by
  apply disjoint_left.mpr
  intro n hn hm
  have hn' := (mem_Ioc.mp hn).2
  have hm' := (mem_Ioc.mp hm).1
  omega

lemma grid_disjoint (q r R : ℕ) (_hq : 0<q) :
    (grid q r R : Set (ℕ×ℕ)).PairwiseDisjoint (fun i => Ioc (lower i) (upper i)) := by
  intro i hi j hj hij
  have hii := mem_product.mp hi
  have hjj := mem_product.mp hj
  by_cases hr : i.1=j.1
  · have hne : i.2≠j.2 := by intro he; exact hij (Prod.ext hr he)
    rcases lt_or_gt_of_ne hne with h | h
    · apply interval_disjoint_of_le
      unfold upper lower
      rw [hr]
      exact Nat.mul_le_mul_right _ (by omega)
    · apply Disjoint.symm
      apply interval_disjoint_of_le
      unfold upper lower
      rw [hr]
      exact Nat.mul_le_mul_right _ (by omega)
  · have oriented : ∀ {i j : ℕ×ℕ}, i∈grid q r R → j∈grid q r R → i.1<j.1 →
        upper i≤lower j := by
      intro i j hi hj h
      have hik := (mem_Ico.mp (mem_product.mp hi).2).2
      have hjk := (mem_Ico.mp (mem_product.mp hj).2).1
      have hp : 2^(i.1+1)≤2^j.1 := Nat.pow_le_pow_right (by omega) (by omega)
      unfold upper lower
      calc
        (i.2+1)*2^i.1 ≤ (2*q)*2^i.1 := Nat.mul_le_mul_right _ (by omega)
        _ = q*2^(i.1+1) := by rw [pow_succ]; ring
        _ ≤ q*2^j.1 := Nat.mul_le_mul_left q hp
        _ ≤ j.2*2^j.1 := Nat.mul_le_mul_right _ hjk
    rcases lt_or_gt_of_ne hr with h | h
    · exact interval_disjoint_of_le (oriented hi hj h)
    · exact (interval_disjoint_of_le (oriented hj hi h)).symm

lemma grid_card (q r R : ℕ) : (grid q r R).card = R*q := by
  simp [grid, card_product, Nat.card_Ico, show 2*q-q=q by omega]

lemma relative_width (q r R : ℕ) (hq : 0<q) {i : ℕ×ℕ} (hi : i∈grid q r R) :
    ((upper i:ℝ)-(lower i:ℝ))^2/((lower i:ℝ)*(upper i:ℝ)) ≤ 1/(q:ℝ)^2 := by
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hj' : (q:ℝ) ≤ (i.2:ℝ) := by exact_mod_cast (mem_Ico.mp (mem_product.mp hi).2).1
  have hj0 : (0:ℝ) < (i.2:ℝ) := hq'.trans_le hj'
  have hv : (0:ℝ)<(2:ℝ)^i.1 := by positivity
  simp only [upper, lower, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
  have he : (((i.2:ℝ)+1)*(2:ℝ)^i.1-(i.2:ℝ)*(2:ℝ)^i.1)^2 /
      ((i.2:ℝ)*(2:ℝ)^i.1 * (((i.2:ℝ)+1)*(2:ℝ)^i.1)) =
      1/((i.2:ℝ)*((i.2:ℝ)+1)) := by
    field_simp
    ring
  rw [he]
  apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<(q:ℝ)^2)
  nlinarith [sq_nonneg ((i.2:ℝ)-q)]

end OrdinaryNarrowGrid

end

end OAI
