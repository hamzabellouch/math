import Mathlib
import OAI.Computability.DeterministicSum.WordArithmetic

namespace OAI

/-! Prime-power Newton interpolation, digit ranks and truncated filters. -/

namespace DeterministicThreeSum
namespace Newton
open scoped BigOperators
open Finset

variable {R : Type*} [CommRing R] {q d : ℕ}

def entry (node : Fin q → R) : Matrix (Fin q) (Fin q) R :=
  fun i j => ∏ k ∈ Iio j, (node i - node k)

lemma entry_zero (node : Fin q → R) {i j : Fin q} (hij : i < j) :
    entry node i j = 0 := by
  apply Finset.prod_eq_zero (mem_Iio.mpr hij)
  simp

lemma entry_lowerTriangular (node : Fin q → R) :
    (entry node).IsLowerTriangular := by
  intro i j hij
  exact entry_zero node hij

lemma entry_det_unit (node : Fin q → R)
    (hu : ∀ i j : Fin q, j < i → IsUnit (node i - node j)) :
    IsUnit (Matrix.det (entry node)) := by
  rw [Matrix.det_of_isLowerTriangular _ (entry_lowerTriangular node)]
  apply IsUnit.prod_iff.mpr
  intro i hi
  apply IsUnit.prod_iff.mpr
  intro j hj
  exact hu i j (mem_Iio.mp hj)

def tensor (A : Matrix (Fin q) (Fin q) R) :
    Matrix (Fin d → Fin q) (Fin d → Fin q) R :=
  fun i j => ∏ k, A (i k) (j k)

lemma tensor_mul (A B : Matrix (Fin q) (Fin q) R) :
    tensor (d := d) (A * B) = tensor A * tensor B := by
  classical
  ext i j
  simp only [tensor, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact Finset.prod_mul_distrib

lemma tensor_one : tensor (d := d) (1 : Matrix (Fin q) (Fin q) R) = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [tensor]
  · have hex : ∃ k, i k ≠ j k := Function.ne_iff.mp hij
    obtain ⟨k, hk⟩ := hex
    rw [Matrix.one_apply_ne hij]
    apply Finset.prod_eq_zero (mem_univ k)
    exact Matrix.one_apply_ne hk

noncomputable def coefficients (node : Fin q → R) (f : (Fin d → Fin q) → R) :
    (Fin d → Fin q) → R :=
  (tensor ((entry node)⁻¹)).mulVec f

lemma interpolate (node : Fin q → R)
    (hu : ∀ i j : Fin q, j < i → IsUnit (node i - node j))
    (f : (Fin d → Fin q) → R) :
    (tensor (entry node)).mulVec (coefficients node f) = f := by
  classical
  unfold coefficients
  rw [Matrix.mulVec_mulVec, ← tensor_mul,
    Matrix.mul_nonsing_inv _ (entry_det_unit node hu), tensor_one, Matrix.one_mulVec]

def degree (j : Fin d → Fin q) : ℕ := ∑ k, (j k).val

lemma exists_coordinate_lt {i j : Fin d → Fin q} (h : degree i < degree j) :
    ∃ k, i k < j k := by
  by_contra! hn
  have hle : degree j ≤ degree i := Finset.sum_le_sum (fun k _ => hn k)
  omega

lemma tensor_entry_zero (node : Fin q → R) {i j : Fin d → Fin q}
    (h : degree i < degree j) : tensor (entry node) i j = 0 := by
  obtain ⟨k, hk⟩ := exists_coordinate_lt h
  exact Finset.prod_eq_zero (mem_univ k) (entry_zero node hk)

noncomputable def basisPolynomial (node : Fin q → R) (j : Fin d → Fin q) :
    MvPolynomial (Fin d) R :=
  ∏ k, ∏ a ∈ Iio (j k), (MvPolynomial.X k - MvPolynomial.C (node a))

lemma eval_basisPolynomial (node : Fin q → R) (i j : Fin d → Fin q) :
    MvPolynomial.eval (node ∘ i) (basisPolynomial node j) =
      tensor (entry node) i j := by
  simp [basisPolynomial, tensor, entry]

noncomputable def truncatedPolynomial (node : Fin q → R)
    (f : (Fin d → Fin q) → R) (Δ : ℕ) : MvPolynomial (Fin d) R :=
  ∑ j ∈ (univ.filter (fun j : Fin d → Fin q => degree j ≤ Δ)),
    MvPolynomial.C (coefficients node f j) * basisPolynomial node j

theorem truncated_agreement (node : Fin q → R)
    (hu : ∀ i j : Fin q, j < i → IsUnit (node i - node j))
    (f : (Fin d → Fin q) → R) (Δ : ℕ) (i : Fin d → Fin q)
    (hi : degree i ≤ Δ) :
    MvPolynomial.eval (node ∘ i) (truncatedPolynomial node f Δ) = f i := by
  classical
  have hinterp := congrFun (interpolate node hu f) i
  rw [Matrix.mulVec, dotProduct] at hinterp
  calc
    MvPolynomial.eval (node ∘ i) (truncatedPolynomial node f Δ) =
        ∑ j ∈ univ.filter (fun j : Fin d → Fin q => degree j ≤ Δ),
          tensor (entry node) i j * coefficients node f j := by
      simp [truncatedPolynomial, eval_basisPolynomial, mul_comm]
    _ = ∑ j, tensor (entry node) i j * coefficients node f j := by
      apply Finset.sum_subset (filter_subset _ _)
      intro j hj hnot
      have hdeg : Δ < degree j := by simpa using hnot
      rw [tensor_entry_zero node (lt_of_le_of_lt hi hdeg), zero_mul]
    _ = f i := hinterp

lemma basisPolynomial_degree (node : Fin q → R) (j : Fin d → Fin q) :
    (basisPolynomial node j).totalDegree ≤ degree j := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := hR
    have hz : basisPolynomial node j = 0 := Subsingleton.elim _ _
    rw [hz, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  have := hR
  unfold basisPolynomial degree
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ a ∈ Iio (j k), (MvPolynomial.X k - MvPolynomial.C (node a)).totalDegree ≤
        ∑ _a ∈ Iio (j k), 1 := by
      apply Finset.sum_le_sum
      intro a ha
      rw [sub_eq_add_neg, ← MvPolynomial.C_neg]
      simpa using MvPolynomial.totalDegree_add
        (MvPolynomial.X k : MvPolynomial (Fin d) R) (MvPolynomial.C (-node a))
    _ = (j k).val := by simp

lemma truncatedPolynomial_degree (node : Fin q → R)
    (f : (Fin d → Fin q) → R) (Δ : ℕ) :
    (truncatedPolynomial node f Δ).totalDegree ≤ Δ := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (basisPolynomial_degree node j).trans (mem_filter.mp hj).2

lemma coefficients_unique (node : Fin q → R)
    (hu : ∀ i j : Fin q, j < i → IsUnit (node i - node j))
    (f : (Fin d → Fin q) → R) (c : (Fin d → Fin q) → R)
    (hc : (tensor (entry node)).mulVec c = f) : c = coefficients node f := by
  classical
  rw [coefficients, ← hc, Matrix.mulVec_mulVec, ← tensor_mul,
    Matrix.nonsing_inv_mul _ (entry_det_unit node hu), tensor_one, Matrix.one_mulVec]

lemma small_difference_unit {p e a b : ℕ} (hp : p.Prime) (he : 0 < e)
    (ha : a < p) (hb : b < p) (hab : a ≠ b) :
    IsUnit ((a : ZMod (p ^ e)) - (b : ZMod (p ^ e))) := by
  have hposunit : ∀ {u v : ℕ}, v < u → u < p →
      IsUnit ((u : ZMod (p ^ e)) - (v : ZMod (p ^ e))) := by
    intro u v hvu hup
    have hdpos : 0 < u - v := Nat.sub_pos_of_lt hvu
    have hdlt : u - v < p := lt_of_le_of_lt (Nat.sub_le u v) hup
    have hunit := (ZMod.isUnit_natCast_iff_not_dvd_pow hp he).mpr
      (Nat.not_dvd_of_pos_of_lt hdpos hdlt)
    simpa only [Nat.cast_sub (le_of_lt hvu)] using hunit
  rcases lt_or_gt_of_ne hab with hab | hab
  · simpa only [neg_sub] using (hposunit hab hb).neg
  · exact hposunit hab ha

lemma primePower_node_units {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hq : q < p) (order : Equiv.Perm (Fin q)) :
    ∀ i j : Fin q, j < i →
      IsUnit (((order i).val : ZMod (p ^ e)) - ((order j).val : ZMod (p ^ e))) := by
  intro i j hji
  apply small_difference_unit hp he
  · exact (order i).isLt.trans hq
  · exact (order j).isLt.trans hq
  · intro heq
    have hij := order.injective (Fin.ext heq)
    exact (ne_of_gt hji) hij

theorem primePower_truncated_agreement {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hq : q < p) (order : Equiv.Perm (Fin q))
    (f : (Fin d → Fin q) → ZMod (p ^ e)) (Δ : ℕ) (i : Fin d → Fin q)
    (hi : degree i ≤ Δ) :
    MvPolynomial.eval (fun k => ((order (i k)).val : ZMod (p ^ e)))
      (truncatedPolynomial (fun j => ((order j).val : ZMod (p ^ e))) f Δ) = f i := by
  exact truncated_agreement _ (primePower_node_units hp he hq order) f Δ i hi

end Newton
end DeterministicThreeSum

namespace DeterministicThreeSum
namespace Digits
open scoped BigOperators
open Finset

def rank (b m z : ℕ) : ℕ :=
  if z < m - 1 then b - (m - 1) + z
  else if z < b then z - (m - 1)
  else z

def node (b m r : ℕ) : ℕ :=
  if r < b - (m - 1) then m - 1 + r
  else if r < b then r - (b - (m - 1))
  else r

lemma node_rank {b m : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b) (z : ℕ) :
    node b m (rank b m z) = z := by
  unfold rank node
  split_ifs <;> omega

lemma rank_node {b m : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b) (r : ℕ) :
    rank b m (node b m r) = r := by
  unfold rank node
  split_ifs <;> omega

lemma rank_lt {b m z : ℕ} (hm : 1 ≤ m) (_hmb : m ≤ b)
    (hz : z < b + m - 1) : rank b m z < b + m - 1 := by
  unfold rank
  split_ifs <;> omega

lemma node_lt {b m r : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b)
    (hr : r < b + m - 1) : node b m r < b + m - 1 := by
  unfold node
  split_ifs <;> omega

def order {b m : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b) :
    Equiv.Perm (Fin (b + m - 1)) where
  toFun r := ⟨node b m r.val, node_lt hm hmb r.isLt⟩
  invFun z := ⟨rank b m z.val, rank_lt hm hmb z.isLt⟩
  left_inv r := Fin.ext (rank_node hm hmb r.val)
  right_inv z := Fin.ext (node_rank hm hmb z.val)

@[simp] lemma order_val {b m : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b)
    (r : Fin (b + m - 1)) : (order hm hmb r).val = node b m r.val := rfl

@[simp] lemma order_symm_val {b m : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b)
    (z : Fin (b + m - 1)) : ((order hm hmb).symm z).val = rank b m z.val := rfl

variable {d : ℕ}

def value (b : ℕ) (z : Fin d → ℕ) : ℕ := ∑ i, z i * b ^ i.val

lemma value_add (b : ℕ) (x y : Fin d → ℕ) :
    value b (fun i => x i + y i) = value b x + value b y := by
  simp [value, add_mul, Finset.sum_add_distrib]

lemma value_succ (b : ℕ) (z : Fin (d+1) → ℕ) :
    value b z = z 0 + b * value b (fun i => z i.succ) := by
  simp only [value, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma value_lt_pow {b : ℕ} (z : Fin d → Fin b) :
    value b (fun i => (z i).val) < b ^ d := by
  induction d with
  | zero => simp [value]
  | succ d ih =>
    rw [value_succ, pow_succ]
    have ht := ih (fun i => z i.succ)
    have hz := (z 0).isLt
    nlinarith [Nat.mul_le_mul_left b (Nat.succ_le_iff.mpr ht)]

lemma value_injective {b : ℕ} :
    Function.Injective (fun z : Fin d → Fin b => value b (fun i => (z i).val)) := by
  induction d with
  | zero => intro x y h; exact Subsingleton.elim _ _
  | succ d ih =>
    intro x y hxy
    dsimp only at hxy
    rw [value_succ, value_succ] at hxy
    have hmod := congrArg (fun v => v % b) hxy
    have hhead : (x 0).val = (y 0).val := by
      simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (x 0).isLt,
        Nat.mod_eq_of_lt (y 0).isLt] using hmod
    have htail : value b (fun i => (x i.succ).val) =
        value b (fun i => (y i.succ).val) := by
      rw [hhead] at hxy
      have hb : 0 < b := (Nat.zero_le (x 0).val).trans_lt (x 0).isLt
      exact Nat.eq_of_mul_eq_mul_left hb (Nat.add_left_cancel hxy)
    have hind := ih htail
    funext i
    refine Fin.cases (Fin.ext hhead) (fun j => congrFun hind j) i

def sumIndex {b m : ℕ} (x : Fin d → Fin m) (y : Fin d → Fin b) :
    Fin d → Fin (b + m - 1) := fun i =>
  ⟨(x i).val + (y i).val, by have hx := (x i).isLt; have hy := (y i).isLt; omega⟩

def rankTuple {b m : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b)
    (x : Fin d → Fin m) (y : Fin d → Fin b) : Fin d → Fin (b + m - 1) :=
  fun i => (order hm hmb).symm (sumIndex x y i)

@[simp] lemma node_rankTuple {b m : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b)
    (x : Fin d → Fin m) (y : Fin d → Fin b) (i : Fin d) :
    (order hm hmb (rankTuple hm hmb x y i)).val = (x i).val + (y i).val := by
  simp [rankTuple, sumIndex]

def cutoff (b d : ℕ) : ℕ := ((b + 3) * d) / 2

end Digits
end DeterministicThreeSum

namespace DeterministicThreeSum
namespace Filter
open scoped BigOperators
open Finset

variable {p e b m d J : ℕ}

def table (hm : 1 ≤ m) (hmb : m ≤ b) (hJ : 0 < J)
    (h : Fin d → ℕ) (f : Fin J → ZMod (p ^ e))
    (r : Fin d → Fin (b + m - 1)) : ZMod (p ^ e) :=
  f ⟨Digits.value b (fun i => h i + (Digits.order hm hmb (r i)).val) % J,
    Nat.mod_lt _ hJ⟩

noncomputable def polynomial (hm : 1 ≤ m) (hmb : m ≤ b) (hJ : 0 < J)
    (h : Fin d → ℕ) (f : Fin J → ZMod (p ^ e)) : MvPolynomial (Fin d) (ZMod (p ^ e)) :=
  Newton.truncatedPolynomial (fun j => ((Digits.order hm hmb j).val : ZMod (p ^ e)))
    (table hm hmb hJ h f) (Digits.cutoff b d)

def exceptionalTuples (hm : 1 ≤ m) (hmb : m ≤ b) (x : Fin d → Fin m) :
    Finset (Fin d → Fin b) :=
  univ.filter (fun y => Digits.cutoff b d < Newton.degree (Digits.rankTuple hm hmb x y))

def exceptionalResidues (hm : 1 ≤ m) (hmb : m ≤ b) (x : Fin d → Fin m) : Finset ℕ :=
  (exceptionalTuples hm hmb x).image (fun y => Digits.value b (fun i => (y i).val))

lemma exceptionalResidues_subset (hm : 1 ≤ m) (hmb : m ≤ b) (x : Fin d → Fin m) :
    exceptionalResidues hm hmb x ⊆ range (b ^ d) := by
  intro v hv
  obtain ⟨y, _, rfl⟩ := mem_image.mp hv
  exact mem_range.mpr (Digits.value_lt_pow y)

lemma exceptional_card (hm : 1 ≤ m) (hmb : m ≤ b) (x : Fin d → Fin m) :
    (exceptionalResidues hm hmb x).card = (exceptionalTuples hm hmb x).card := by
  exact Finset.card_image_of_injective _ Digits.value_injective

lemma rank_sum_le_of_not_exceptional (hm : 1 ≤ m) (hmb : m ≤ b)
    (x : Fin d → Fin m) (y : Fin d → Fin b)
    (hy : Digits.value b (fun i => (y i).val) ∉ exceptionalResidues hm hmb x) :
    Newton.degree (Digits.rankTuple hm hmb x y) ≤ Digits.cutoff b d := by
  by_contra! hdeg
  apply hy
  exact mem_image.mpr ⟨y, mem_filter.mpr ⟨mem_univ y, hdeg⟩, rfl⟩

theorem agreement (hp : p.Prime) (he : 0 < e) (hq : b + m - 1 < p)
    (hm : 1 ≤ m) (hmb : m ≤ b) (hJ : 0 < J)
    (h : Fin d → ℕ) (f : Fin J → ZMod (p ^ e))
    (x : Fin d → Fin m) (y : Fin d → Fin b)
    (hy : Digits.value b (fun i => (y i).val) ∉ exceptionalResidues hm hmb x) :
    MvPolynomial.eval (fun i => ((x i).val : ZMod (p ^ e)) + ((y i).val : ZMod (p ^ e)))
      (polynomial hm hmb hJ h f) =
    f ⟨(Digits.value b (fun i => h i + (x i).val) +
        Digits.value b (fun i => (y i).val)) % J, Nat.mod_lt _ hJ⟩ := by
  have hrank := rank_sum_le_of_not_exceptional hm hmb x y hy
  have hagree := Newton.primePower_truncated_agreement hp he hq (Digits.order hm hmb)
    (table hm hmb hJ h f) (Digits.cutoff b d) (Digits.rankTuple hm hmb x y) hrank
  simp only [Digits.node_rankTuple, Nat.cast_add] at hagree
  rw [show Digits.value b (fun i => h i + (x i).val) +
        Digits.value b (fun i => (y i).val) =
      Digits.value b (fun i => h i + ((x i).val + (y i).val)) by
        rw [← Digits.value_add]; congr 1; funext i; omega]
  simpa only [polynomial, table, Digits.node_rankTuple] using hagree

lemma polynomial_degree (hm : 1 ≤ m) (hmb : m ≤ b) (hJ : 0 < J)
    (h : Fin d → ℕ) (f : Fin J → ZMod (p ^ e)) :
    (polynomial hm hmb hJ h f).totalDegree ≤ Digits.cutoff b d :=
  Newton.truncatedPolynomial_degree _ _ _

end Filter
end DeterministicThreeSum

end OAI
