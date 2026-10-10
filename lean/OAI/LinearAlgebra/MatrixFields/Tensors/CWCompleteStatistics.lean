import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.ComplexRectangularASI
import OAI.LinearAlgebra.MatrixFields.Construction.ExactStatisticWords
import OAI.LinearAlgebra.MatrixFields.Construction.JointMaskedAssignment

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.FieldCoefficientExtraction

variable {F X Y Z : Type*}

theorem coeff_triple [CommSemiring F] (a b c : Polynomial F) (d : ℕ) :
    (a * b * c).coeff d =
      ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        (if j.val ≤ d - i.val then a.coeff (d - i.val - j.val) else 0) *
          b.coeff j.val * c.coeff i.val := by
  classical
  rw [show a * b * c = c * (b * a) by ring]
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (if j ≤ d - i.val then a.coeff (d - i.val - j) else 0) *
      b.coeff j * c.coeff i.val) (d + 1)]
  symm
  calc
    (∑ j ∈ Finset.range (d + 1),
        (if j ≤ d - i.val then a.coeff (d - i.val - j) else 0) *
          b.coeff j * c.coeff i.val) =
        ∑ j ∈ Finset.range (d - i.val + 1),
          (if j ≤ d - i.val then a.coeff (d - i.val - j) else 0) *
            b.coeff j * c.coeff i.val := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j hj hjnot
      have h : ¬ j ≤ d - i.val := by
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using hjnot
      simp [h]
    _ = ∑ j ∈ Finset.range (d - i.val + 1),
        c.coeff i.val * (b.coeff j * a.coeff (d - i.val - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
      ring

theorem rankAtMost_coeff [CommSemiring F]
    {P : Tensor (Polynomial F) X Y Z} {r : ℕ}
    (hP : Tensor.RankAtMost P r) (d : ℕ) :
    Tensor.RankAtMost (fun x y z => (P x y z).coeff d) ((d + 1) ^ 2 * r) := by
  classical
  rcases hP with ⟨a, b, c, rfl⟩
  let aa : (Fin r × Fin (d + 1) × Fin (d + 1)) → X → F :=
    fun v x => if v.2.2.val ≤ d - v.2.1.val then
      (a v.1 x).coeff (d - v.2.1.val - v.2.2.val) else 0
  let bb : (Fin r × Fin (d + 1) × Fin (d + 1)) → Y → F :=
    fun v y => (b v.1 y).coeff v.2.2.val
  let cc : (Fin r × Fin (d + 1) × Fin (d + 1)) → Z → F :=
    fun v z => (c v.1 z).coeff v.2.1.val
  have heq : (fun x y z => (∑ j, Tensor.rankOne (a j) (b j) (c j) x y z).coeff d) =
      fun x y z => ∑ v, Tensor.rankOne (aa v) (bb v) (cc v) x y z := by
    funext x y z
    simp only [Polynomial.finsetSum_coeff, Tensor.rankOne, Fintype.sum_prod_type,
      coeff_triple, aa, bb, cc]
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using Tensor.rankAtMost_sum_rankOne aa bb cc

theorem rank_power [Field F] {T : Tensor F X Y Z} {r d D : ℕ}
    (A : Tensor.PolynomialApproximation T r d D) (n : ℕ) :
    Tensor.RankAtMost (Tensor.power T n) ((d * n + 1) ^ 2 * r ^ n) := by
  have h := rankAtMost_coeff (A.power n).rank_bound (d * n)
  have heq : (fun x y z => ((A.power n).polynomial x y z).coeff (d * n)) =
      Tensor.power T n := by
    funext x y z
    exact (A.power n).leading x y z
  rw [heq] at h
  exact h

end MatrixMultiplication.FieldCoefficientExtraction

end




noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation Polynomial

namespace MatrixMultiplication.FieldCW

section Integral

variable (F : Type*) [CommRing F] (q : ℕ)

def zeroForm (x : Fin (q + 2)) : F := if x.val = 0 then 1 else 0

def interiorForm (i : Fin q) (x : Fin (q + 2)) : F :=
  if x.val = i.val + 1 then 1 else 0

def lastForm (x : Fin (q + 2)) : F := if x.val = q + 1 then 1 else 0

def interiorSum (x : Fin (q + 2)) : F := ∑ i, interiorForm F q i x

def tensor : Tensor F (Fin (q + 2)) (Fin (q + 2)) (Fin (q + 2)) :=
  fun x y z =>
    (∑ i : Fin q,
      (zeroForm F q x * interiorForm F q i y * interiorForm F q i z +
      interiorForm F q i x * zeroForm F q y * interiorForm F q i z +
      interiorForm F q i x * interiorForm F q i y * zeroForm F q z)) +
    lastForm F q x * zeroForm F q y * zeroForm F q z +
    zeroForm F q x * lastForm F q y * zeroForm F q z +
    zeroForm F q x * zeroForm F q y * lastForm F q z

theorem interior_pair_sum (x y : Fin (q + 2)) :
    (∑ i : Fin q, interiorForm F q i x * interiorForm F q i y) =
      if x = y ∧ 1 ≤ x.val ∧ x.val ≤ q then 1 else 0 := by
  classical
  by_cases hx : 1 ≤ x.val ∧ x.val ≤ q
  · let i : Fin q := ⟨x.val - 1, by omega⟩
    rw [Finset.sum_eq_single i]
    · simp [interiorForm, i, Nat.sub_add_cancel hx.1, hx.1, hx.2,
        Fin.ext_iff, eq_comm]
    · intro j hj hji
      have hne : x.val ≠ j.val + 1 := by
        intro h
        apply hji
        apply Fin.ext
        dsimp [i]
        omega
      simp [interiorForm, hne]
    · simp
  · have hsum : (∑ i : Fin q, interiorForm F q i x * interiorForm F q i y) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hne : x.val ≠ i.val + 1 := by
        intro h
        apply hx
        have := i.isLt
        omega
      simp [interiorForm, hne]
    rw [hsum, ite_eq_right]
    intro h
    exact hx ⟨h.2.1, h.2.2⟩

theorem tensor_zero_side (x y z : Fin (q + 2)) (hx : x.val = 0) :
    tensor F q x y z =
      if (y.val = 0 ∧ z.val = q + 1) ∨
          (y.val = q + 1 ∧ z.val = 0) ∨
          (1 ≤ y.val ∧ y.val ≤ q ∧ y = z) then 1 else 0 := by
  have hx0 : zeroForm F q x = 1 := by simp [zeroForm, hx]
  have hxlast : lastForm F q x = 0 := by simp [lastForm, hx]
  have hxmid (i : Fin q) : interiorForm F q i x = 0 := by
    simp [interiorForm, hx]
  simp only [tensor, hx0, hxlast, hxmid, one_mul, zero_mul, add_zero]
  rw [interior_pair_sum]
  by_cases hy0 : y.val = 0
  · simp [zeroForm, lastForm, hy0]
  · by_cases hylast : y.val = q + 1
    · have hyinter : ¬ y.val ≤ q := by omega
      simp [zeroForm, lastForm, hylast]
    · have hylo : 1 ≤ y.val := by omega
      have hyhi : y.val ≤ q := by have := y.isLt; omega
      simp [zeroForm, lastForm, hy0, hylast, hylo, hyhi]

theorem tensor_cyclic (x y z : Fin (q + 2)) :
    tensor F q x y z = tensor F q y z x := by
  unfold tensor
  have hsum :
      (∑ i : Fin q,
        (zeroForm F q x * interiorForm F q i y * interiorForm F q i z +
        interiorForm F q i x * zeroForm F q y * interiorForm F q i z +
        interiorForm F q i x * interiorForm F q i y * zeroForm F q z)) =
      ∑ i : Fin q,
        (zeroForm F q y * interiorForm F q i z * interiorForm F q i x +
        interiorForm F q i y * zeroForm F q z * interiorForm F q i x +
        interiorForm F q i y * interiorForm F q i z * zeroForm F q x) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  ring

def form (e : ℕ) (u v : F) : Polynomial F := C u + X ^ e * C v

def left : Option (Option (Fin q)) → Fin (q + 2) → Polynomial F
  | some (some i), x => X * form F 1 (zeroForm F q x) (interiorForm F q i x)
  | some none, x => -form F 2 (zeroForm F q x) (interiorSum F q x)
  | none, x => (1 - C (q : F) * X) * form F 3 (zeroForm F q x) (lastForm F q x)

def other : Option (Option (Fin q)) → Fin (q + 2) → Polynomial F
  | some (some i), x => form F 1 (zeroForm F q x) (interiorForm F q i x)
  | some none, x => form F 2 (zeroForm F q x) (interiorSum F q x)
  | none, x => form F 3 (zeroForm F q x) (lastForm F q x)

def polynomial : Tensor (Polynomial F) (Fin (q + 2)) (Fin (q + 2)) (Fin (q + 2)) :=
  fun x y z => ∑ i, Tensor.rankOne (left F q i) (other F q i) (other F q i) x y z

theorem rank_bound : Tensor.RankAtMost (polynomial F q) (q + 2) := by
  unfold polynomial
  simpa only [Fintype.card_option, Fintype.card_fin, Nat.add_assoc,
    Nat.reduceAdd] using
    Tensor.rankAtMost_sum_rankOne (left F q) (other F q) (other F q)

theorem polynomial_apply (x y z : Fin (q + 2)) :
    polynomial F q x y z =
      (∑ i : Fin q, X * form F 1 (zeroForm F q x) (interiorForm F q i x) *
        form F 1 (zeroForm F q y) (interiorForm F q i y) *
        form F 1 (zeroForm F q z) (interiorForm F q i z)) -
      form F 2 (zeroForm F q x) (interiorSum F q x) *
        form F 2 (zeroForm F q y) (interiorSum F q y) *
        form F 2 (zeroForm F q z) (interiorSum F q z) +
      (1 - C (q : F) * X) * form F 3 (zeroForm F q x) (lastForm F q x) *
        form F 3 (zeroForm F q y) (lastForm F q y) *
        form F 3 (zeroForm F q z) (lastForm F q z) := by
  simp only [polynomial, Fintype.sum_option, Tensor.rankOne, left, other]
  ring

private theorem coeff_mul_two (a b : Polynomial F) :
    (a * b).coeff 2 = a.coeff 0 * b.coeff 2 + a.coeff 1 * b.coeff 1 +
      a.coeff 2 * b.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, add_assoc]

private theorem coeff_mul_three (a b : Polynomial F) :
    (a * b).coeff 3 = a.coeff 0 * b.coeff 3 + a.coeff 1 * b.coeff 2 +
      a.coeff 2 * b.coeff 1 + a.coeff 3 * b.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, add_assoc]

theorem vanishes (x y z : Fin (q + 2)) (k : ℕ) (hk : k < 3) :
    (polynomial F q x y z).coeff k = 0 := by
  interval_cases k <;>
    simp [polynomial_apply, Polynomial.mul_coeff_zero,
      Polynomial.mul_coeff_one, coeff_mul_two, form, Polynomial.coeff_add,
      Polynomial.coeff_sub, interiorSum,
      Polynomial.coeff_one, Polynomial.coeff_X,
      Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum] <;>
    simp only [mul_assoc, mul_comm] <;> ring_nf
  simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_comm]
  ring

theorem leading (x y z : Fin (q + 2)) :
    (polynomial F q x y z).coeff 3 = tensor F q x y z := by
  simp [polynomial_apply, Polynomial.mul_coeff_zero,
    Polynomial.mul_coeff_one, coeff_mul_two, coeff_mul_three, form,
    Polynomial.coeff_add, Polynomial.coeff_sub,
    tensor, Polynomial.coeff_one, Polynomial.coeff_X,
    Finset.sum_add_distrib]
  simp only [mul_assoc, mul_comm, mul_left_comm]
  ring_nf
  simp only [Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm]
  ring

def degreeBound : ℕ := Finset.univ.sup fun xyz :
    Fin (q + 2) × Fin (q + 2) × Fin (q + 2) =>
      (polynomial F q xyz.1 xyz.2.1 xyz.2.2).natDegree

theorem degree_bound (x y z : Fin (q + 2)) :
    (polynomial F q x y z).degree ≤ degreeBound F q := by
  let f : (Fin (q + 2) × Fin (q + 2) × Fin (q + 2)) → ℕ :=
    fun xyz => (polynomial F q xyz.1 xyz.2.1 xyz.2.2).natDegree
  have h := Finset.le_sup (s := Finset.univ) (f := f) (b := (x, y, z))
    (Finset.mem_univ (x, y, z))
  exact Polynomial.degree_le_of_natDegree_le h

end Integral

variable (F : Type*) [Field F] (q : ℕ)

def approximation : Tensor.PolynomialApproximation (tensor F q) (q + 2) 3
    (degreeBound F q) where
  polynomial := polynomial F q
  rank_bound := rank_bound F q
  vanishes := vanishes F q
  leading := leading F q
  degree_bound := degree_bound F q

theorem rank_power (n : ℕ) :
    Tensor.RankAtMost (Tensor.power (tensor F q) n) ((3 * n + 1) ^ 2 * (q + 2) ^ n) :=
  FieldCoefficientExtraction.rank_power (approximation F q) n

end MatrixMultiplication.FieldCW

end




namespace MatrixMultiplication.CWLeafRestrictions

open MatrixMultiplication.Foundation

def lastLabel (q : ℕ) : Fin (q + 2) := ⟨q + 1, by omega⟩

def complement (q : ℕ) : Fin (q + 2) ≃ Fin (q + 2) :=
  Equiv.swap 0 (lastLabel q)

@[simp] theorem complement_zero (q : ℕ) : complement q 0 = lastLabel q := by
  simp [complement]

@[simp] theorem complement_last (q : ℕ) : complement q (lastLabel q) = 0 := by
  simp [complement]

@[simp] theorem complement_involution (q : ℕ) (x : Fin (q + 2)) :
    complement q (complement q x) = x := by
  simp [complement]

theorem complement_interior (q : ℕ) (x : Fin (q + 2))
    (hx0 : x.val ≠ 0) (hxlast : x.val ≠ q + 1) : complement q x = x := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact hx0 (congrArg Fin.val h)
  · intro h
    exact hxlast (congrArg Fin.val h)

theorem zero_support_iff (q : ℕ) (y z : Fin (q + 2)) :
    ((y.val = 0 ∧ z.val = q + 1) ∨
      (y.val = q + 1 ∧ z.val = 0) ∨
      (1 ≤ y.val ∧ y.val ≤ q ∧ y = z)) ↔ complement q y = z := by
  by_cases hy0 : y.val = 0
  · have hy : y = 0 := Fin.ext hy0
    subst y
    rw [complement_zero]
    constructor
    · rintro (⟨_, hz⟩ | ⟨hy, _⟩ | ⟨hy, _⟩)
      · exact Fin.ext hz.symm
      · have : (0 : ℕ) = q + 1 := hy
        omega
      · have : 1 ≤ (0 : ℕ) := hy
        omega
    · intro h
      exact Or.inl ⟨rfl, (congrArg Fin.val h).symm⟩
  · by_cases hylast : y.val = q + 1
    · have hy : y = lastLabel q := Fin.ext hylast
      subst y
      rw [complement_last]
      constructor
      · rintro (⟨hy, _⟩ | ⟨_, hz⟩ | ⟨_, hy, _⟩)
        · have : q + 1 = 0 := hy
          omega
        · exact Fin.ext hz.symm
        · have : q + 1 ≤ q := hy
          omega
      · intro h
        exact Or.inr (Or.inl ⟨rfl, (congrArg Fin.val h).symm⟩)
    · have hlo : 1 ≤ y.val := by omega
      have hhi : y.val ≤ q := by have := y.isLt; omega
      rw [complement_interior q y hy0 hylast]
      simp [hy0, hylast, hlo, hhi]

theorem tensor_zero_matching (F : Type*) [CommRing F] (q : ℕ)
    (y z : Fin (q + 2)) :
    FieldCW.tensor F q 0 y (complement q z) = if y = z then 1 else 0 := by
  rw [FieldCW.tensor_zero_side F q 0 y (complement q z) rfl]
  simp only [zero_support_iff, Equiv.apply_eq_iff_eq]

theorem tensor_middle_zero_matching (F : Type*) [CommRing F] (q : ℕ)
    (x z : Fin (q + 2)) :
    FieldCW.tensor F q x 0 (complement q z) = if x = z then 1 else 0 := by
  rw [FieldCW.tensor_cyclic F q x 0 (complement q z)]
  have h := tensor_zero_matching F q (complement q z) (complement q x)
  simpa only [complement_involution, Equiv.apply_eq_iff_eq, eq_comm] using h

theorem tensor_last_zero_matching (F : Type*) [CommRing F] (q : ℕ)
    (x y : Fin (q + 2)) :
    FieldCW.tensor F q x (complement q y) 0 = if x = y then 1 else 0 := by
  rw [FieldCW.tensor_cyclic F q x (complement q y) 0,
    FieldCW.tensor_cyclic F q (complement q y) 0 x]
  exact tensor_zero_matching F q x y

theorem zeroX_leaf (F : Type*) [CommRing F] (q n : ℕ)
    (p : (Fin n → Fin (q + 2)) → Prop) [DecidablePred p] :
    Tensor.pullback (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin (q + 2)))
      (fun y : Unit × {w // p w} => y.2.val)
      (fun z : {w // p w} × Unit => fun i => complement q (z.1.val i))
      (Tensor.power (FieldCW.tensor F q) n) =
      Tensor.matrixCoefficients Unit Unit {w // p w} :=
  LeafVolumes.matchingPower_matrixCoefficients (FieldCW.tensor F q) 0
    (complement q) (tensor_zero_matching F q) n p

theorem zeroY_leaf (F : Type*) [CommRing F] (q n : ℕ)
    (p : (Fin n → Fin (q + 2)) → Prop) [DecidablePred p] :
    Tensor.pullback (fun x : {w // p w} × Unit => x.1.val)
      (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin (q + 2)))
      (fun z : Unit × {w // p w} => fun i => complement q (z.2.val i))
      (Tensor.power (FieldCW.tensor F q) n) =
      Tensor.matrixCoefficients {w // p w} Unit Unit := by
  funext x y z
  simp only [Tensor.pullback, Tensor.power, tensor_middle_zero_matching,
    Fintype.prod_boole, ← funext_iff, Tensor.matrixCoefficients]
  simp [Subtype.ext_iff, eq_comm]

theorem zeroZ_leaf (F : Type*) [CommRing F] (q n : ℕ)
    (p : (Fin n → Fin (q + 2)) → Prop) [DecidablePred p] :
    Tensor.pullback (fun x : Unit × {w // p w} => x.2.val)
      (fun y : {w // p w} × Unit => fun i => complement q (y.1.val i))
      (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin (q + 2)))
      (Tensor.power (FieldCW.tensor F q) n) =
      Tensor.matrixCoefficients Unit {w // p w} Unit := by
  funext x y z
  simp only [Tensor.pullback, Tensor.power, tensor_last_zero_matching,
    Fintype.prod_boole, ← funext_iff, Tensor.matrixCoefficients]
  simp [Subtype.ext_iff]

end MatrixMultiplication.CWLeafRestrictions





namespace MatrixMultiplication.CWLeafStatistics

open MatrixMultiplication.Foundation

def weight (x : Fin 7) : ℕ := if x.val = 0 then 0 else if x.val = 6 then 2 else 1

def pairStatistic (x : Fin 7 × Fin 7) : Fin 6 :=
  if weight x.1 + weight x.2 = 0 then 0
  else if weight x.1 + weight x.2 = 1 then 1
  else if weight x.1 + weight x.2 = 2 then
    if weight x.1 = 1 ∧ weight x.2 = 1 then 2 else 3
  else if weight x.1 + weight x.2 = 3 then 4 else 5

theorem statistic_weight : ∀ x : Fin 7 × Fin 7,
    AllFieldParameters.statisticWeight (pairStatistic x) = weight x.1 + weight x.2 := by
  decide +kernel

theorem pair_multiplicity : ∀ i : Fin 6,
    Fintype.card {x : Fin 7 × Fin 7 // pairStatistic x = i} =
      AllFieldParameters.multiplicity i := by
  decide +kernel

theorem complement_weight : ∀ x : Fin 7,
    weight (CWLeafRestrictions.complement 5 x) + weight x = 2 := by
  decide +kernel

theorem complement_statistic : ∀ x : Fin 7 × Fin 7,
    pairStatistic (CWLeafRestrictions.complement 5 x.1,
      CWLeafRestrictions.complement 5 x.2) =
      AllFieldParameters.kappa (pairStatistic x) := by
  decide +kernel

theorem ordered_pair_multiplicity (i j : Fin 6) :
    Fintype.card {x : (Fin 7 × Fin 7) × (Fin 7 × Fin 7) //
      pairStatistic x.1 = i ∧ pairStatistic x.2 = j} =
      AllFieldParameters.multiplicity i * AllFieldParameters.multiplicity j := by
  let e : {x : (Fin 7 × Fin 7) × (Fin 7 × Fin 7) //
      pairStatistic x.1 = i ∧ pairStatistic x.2 = j} ≃
      {x : Fin 7 × Fin 7 // pairStatistic x = i} ×
        {x : Fin 7 × Fin 7 // pairStatistic x = j} :=
    { toFun := fun x => (⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩)
      invFun := fun x => ⟨(x.1.val, x.2.val), x.1.property, x.2.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  rw [Fintype.card_congr e, Fintype.card_prod, pair_multiplicity, pair_multiplicity]

end MatrixMultiplication.CWLeafStatistics





noncomputable section

namespace MatrixMultiplication.CWCompatibilityTransfer

open MatrixMultiplication.Foundation CWLeafRestrictions InheritedMasks
open scoped BigOperators

def wordWeight {n : ℕ} (w : Fin n → Fin 7) : ℕ := ∑ i, CWLeafStatistics.weight (w i)

def wordComplement {n : ℕ} (w : Fin n → Fin 7) : Fin n → Fin 7 :=
  fun i => complement 5 (w i)

@[simp] theorem wordComplement_involution {n : ℕ} (w : Fin n → Fin 7) :
    wordComplement (wordComplement w) = w := by
  funext i
  exact complement_involution 5 (w i)

theorem weight_eq_zero_iff : ∀ x : Fin 7, CWLeafStatistics.weight x = 0 ↔ x = 0 := by
  decide +kernel

theorem wordWeight_zero {n : ℕ} (w : Fin n → Fin 7) (h : wordWeight w = 0) :
    ∀ i, w i = 0 := by
  intro i
  have hle : CWLeafStatistics.weight (w i) ≤ wordWeight w := by
    unfold wordWeight
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (CWLeafStatistics.weight (w j)))
      (Finset.mem_univ i)
  apply (weight_eq_zero_iff (w i)).mp
  omega

theorem site_nonzero {F : Type*} [CommRing F] {n : ℕ}
    (x y z : Fin n → Fin 7)
    (h : Tensor.power (FieldCW.tensor F 5) n x y z ≠ 0) (i : Fin n) :
    FieldCW.tensor F 5 (x i) (y i) (z i) ≠ 0 := by
  intro hi
  apply h
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

theorem zeroX_word_match {F : Type*} [CommRing F] {n : ℕ}
    (x y z : Fin n → Fin 7)
    (h : Tensor.power (FieldCW.tensor F 5) n x y z ≠ 0)
    (hx : wordWeight x = 0) : z = wordComplement y := by
  funext i
  have hi := site_nonzero x y z h i
  rw [wordWeight_zero x hx i] at hi
  have heq : FieldCW.tensor F 5 0 (y i) (z i) =
      if y i = complement 5 (z i) then 1 else 0 := by
    simpa only [complement_involution] using
      tensor_zero_matching F 5 (y i) (complement 5 (z i))
  have hyz : y i = complement 5 (z i) := by
    by_contra hn
    rw [heq, ite_eq_right hn] at hi
    exact hi rfl
  have hh := congrArg (complement 5) hyz
  simpa only [wordComplement, complement_involution] using hh.symm

theorem zeroY_word_match {F : Type*} [CommRing F] {n : ℕ}
    (x y z : Fin n → Fin 7)
    (h : Tensor.power (FieldCW.tensor F 5) n x y z ≠ 0)
    (hy : wordWeight y = 0) : z = wordComplement x := by
  funext i
  have hi := site_nonzero x y z h i
  rw [wordWeight_zero y hy i] at hi
  have heq : FieldCW.tensor F 5 (x i) 0 (z i) =
      if x i = complement 5 (z i) then 1 else 0 := by
    simpa only [complement_involution] using
      tensor_middle_zero_matching F 5 (x i) (complement 5 (z i))
  have hxz : x i = complement 5 (z i) := by
    by_contra hn
    rw [heq, ite_eq_right hn] at hi
    exact hi rfl
  have hh := congrArg (complement 5) hxz
  simpa only [wordComplement, complement_involution] using hh.symm

theorem zeroZ_word_match {F : Type*} [CommRing F] {n : ℕ}
    (x y z : Fin n → Fin 7)
    (h : Tensor.power (FieldCW.tensor F 5) n x y z ≠ 0)
    (hz : wordWeight z = 0) : y = wordComplement x := by
  funext i
  have hi := site_nonzero x y z h i
  rw [wordWeight_zero z hz i] at hi
  have heq : FieldCW.tensor F 5 (x i) (y i) 0 =
      if x i = complement 5 (y i) then 1 else 0 := by
    simpa only [complement_involution] using
      tensor_last_zero_matching F 5 (x i) (complement 5 (y i))
  have hxy : x i = complement 5 (y i) := by
    by_contra hn
    rw [heq, ite_eq_right hn] at hi
    exact hi rfl
  have hh := congrArg (complement 5) hxy
  simpa only [wordComplement, complement_involution] using hh.symm

theorem transfer_window {P A : Type*} [Fintype P] [DecidableEq P]
    [Fintype A] [DecidableEq A] {n : ℕ}
    (statistic : (Fin n → Fin 7) → A) (κ : A ≃ A)
    (hstatistic : ∀ w, statistic (wordComplement w) = κ (statistic w))
    (x y : P → (Fin n → Fin 7)) (hmatch : ∀ i, y i = wordComplement (x i))
    (ν : A → ℝ) (η : ℝ)
    (hx : typeWindow ν η (fun i => statistic (x i))) :
    typeWindow (ν ∘ κ.symm) η (fun i => statistic (y i)) := by
  have heq : (fun i => statistic (y i)) = κ ∘ (fun i => statistic (x i)) := by
    funext i
    rw [hmatch i, hstatistic]
    rfl
  rw [heq]
  exact (typeWindow_equiv ν η (fun i => statistic (x i)) κ).mpr hx

end MatrixMultiplication.CWCompatibilityTransfer






namespace MatrixMultiplication.CWStrands

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {F : Type*} [CommRing F]

theorem site_weight_support (x y z : Fin 7)
    (h : FieldCW.tensor F 5 x y z ≠ 0) :
    CWLeafStatistics.weight x + CWLeafStatistics.weight y + CWLeafStatistics.weight z = 2 := by
  have hzero (a b : Fin 7) (hh : FieldCW.tensor F 5 0 a b ≠ 0) :
      CWLeafStatistics.weight a + CWLeafStatistics.weight b = 2 := by
    have he := CWLeafRestrictions.tensor_zero_matching F 5 a
      (CWLeafRestrictions.complement 5 b)
    simp only [CWLeafRestrictions.complement_involution] at he
    by_cases hm : a = CWLeafRestrictions.complement 5 b
    · subst a
      exact CWLeafStatistics.complement_weight b
    · rw [ite_eq_right hm] at he
      exact False.elim (hh he)
  by_cases hx : x = 0
  · subst x
    simpa [CWLeafStatistics.weight] using hzero y z h
  by_cases hy : y = 0
  · subst y
    have hh : FieldCW.tensor F 5 0 z x ≠ 0 := by
      rwa [← FieldCW.tensor_cyclic]
    have hw := hzero z x hh
    simp only [CWLeafStatistics.weight, Fin.val_zero, ite_eq_left, add_zero] at *
    omega
  by_cases hz : z = 0
  · subst z
    have hh : FieldCW.tensor F 5 0 x y ≠ 0 := by
      rwa [FieldCW.tensor_cyclic]
    have hw := hzero x y hh
    simpa [CWLeafStatistics.weight] using hw
  have hx0 : x.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hx
  have hy0 : y.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hy
  have hz0 : z.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hz
  apply False.elim (h _)
  simp only [FieldCW.tensor, FieldCW.zeroForm, hx0, hy0, hz0, ite_false,
    zero_mul, mul_zero, add_zero, Finset.sum_const_zero]

def weight {P : Type*} [Fintype P] (w : P → Fin 7) : ℕ :=
  ∑ i, CWLeafStatistics.weight (w i)

def strand (P : Type*) [Fintype P] : Tensor F (P → Fin 7) (P → Fin 7) (P → Fin 7) :=
  fun x y z => ∏ i, FieldCW.tensor F 5 (x i) (y i) (z i)

theorem strand_support {P : Type*} [Fintype P]
    (x y z : P → Fin 7) (h : strand (F := F) P x y z ≠ 0) :
    weight x + weight y + weight z = 2 * Fintype.card P := by
  have hi (i : P) : FieldCW.tensor F 5 (x i) (y i) (z i) ≠ 0 := by
    intro he
    exact h (Finset.prod_eq_zero (Finset.mem_univ i) he)
  calc
    weight x + weight y + weight z =
        ∑ i, (CWLeafStatistics.weight (x i) + CWLeafStatistics.weight (y i) +
          CWLeafStatistics.weight (z i)) := by simp [weight, Finset.sum_add_distrib]
    _ = ∑ _i : P, 2 := Finset.sum_congr rfl (fun i _ => site_weight_support _ _ _ (hi i))
    _ = 2 * Fintype.card P := by simp [Nat.mul_comm]

def shapeTensor (P : Type*) [Fintype P] (g : Fin 3 → ℕ) :
    Tensor F (P → Fin 7) (P → Fin 7) (P → Fin 7) :=
  fun x y z => if weight x = g 0 ∧ weight y = g 1 ∧ weight z = g 2
    then strand P x y z else 0

theorem shapeTensor_support {P : Type*} [Fintype P]
    (g : Fin 3 → ℕ) (x y z : P → Fin 7)
    (h : shapeTensor (F := F) P g x y z ≠ 0) :
    weight x = g 0 ∧ weight y = g 1 ∧ weight z = g 2 := by
  classical
  by_contra hn
  exact h (ite_eq_right hn)

theorem weight_sum_elim {P Q : Type*} [Fintype P] [Fintype Q]
    (x : P → Fin 7) (y : Q → Fin 7) :
    weight (Sum.elim x y) = weight x + weight y := by
  simp [weight, Fintype.sum_sum_type]

theorem strand_sum_elim {P Q : Type*} [Fintype P] [Fintype Q]
    (x : (P → Fin 7) × (Q → Fin 7))
    (y : (P → Fin 7) × (Q → Fin 7))
    (z : (P → Fin 7) × (Q → Fin 7)) :
    strand (F := F) (P ⊕ Q) (Sum.elim x.1 x.2) (Sum.elim y.1 y.2) (Sum.elim z.1 z.2) =
      Tensor.product (strand P) (strand Q) x y z := by
  simp [strand, Tensor.product, Fintype.prod_sum_type]

theorem shape_split {P Q : Type*} [Fintype P] [Fintype Q]
    (u v : Fin 3 → ℕ)
    (x : (P → Fin 7) × (Q → Fin 7))
    (y : (P → Fin 7) × (Q → Fin 7))
    (z : (P → Fin 7) × (Q → Fin 7)) :
    (if weight x.1 = u 0 ∧ weight y.1 = u 1 ∧ weight z.1 = u 2 then
      shapeTensor (F := F) (P ⊕ Q) (u + v) (Sum.elim x.1 x.2) (Sum.elim y.1 y.2)
        (Sum.elim z.1 z.2) else 0) =
      Tensor.product (shapeTensor P u) (shapeTensor Q v) x y z := by
  classical
  simp only [shapeTensor, weight_sum_elim, Pi.add_apply, strand_sum_elim,
    Tensor.product]
  by_cases hx : weight x.1 = u 0
  · by_cases hy : weight y.1 = u 1
    · by_cases hz : weight z.1 = u 2
      · simp [hx, hy, hz, mul_ite]
      · simp [hz]
    · simp [hy]
  · simp [hx]

theorem shape_split_sub {P Q : Type*} [Fintype P] [Fintype Q]
    (g u : Fin 3 → ℕ) (hu : ∀ s, u s ≤ g s)
    (x : (P → Fin 7) × (Q → Fin 7))
    (y : (P → Fin 7) × (Q → Fin 7))
    (z : (P → Fin 7) × (Q → Fin 7)) :
    (if weight x.1 = u 0 ∧ weight y.1 = u 1 ∧ weight z.1 = u 2 then
      shapeTensor (F := F) (P ⊕ Q) g (Sum.elim x.1 x.2) (Sum.elim y.1 y.2)
        (Sum.elim z.1 z.2) else 0) =
      Tensor.product (shapeTensor P u) (shapeTensor Q (g - u)) x y z := by
  have hg : u + (g - u) = g := by
    funext s
    exact Nat.add_sub_of_le (hu s)
  simpa only [hg] using shape_split u (g - u) x y z

def splitMatrix {P Q : Type*} [Fintype P] (u : ℕ) :
    ((P → Fin 7) × (Q → Fin 7)) → ((P ⊕ Q) → Fin 7) → F := by
  classical
  exact fun x w => if w = Sum.elim x.1 x.2 ∧ weight x.1 = u then 1 else 0

theorem shape_split_restrict {P Q : Type*} [Fintype P] [Fintype Q]
    [DecidableEq P] [DecidableEq Q] (u v : Fin 3 → ℕ) :
    Tensor.restrict (splitMatrix (F := F) (u 0)) (splitMatrix (u 1)) (splitMatrix (u 2))
      (shapeTensor (P ⊕ Q) (u + v)) =
      Tensor.product (shapeTensor P u) (shapeTensor Q v) := by
  classical
  funext x y z
  have hcollapse : Tensor.restrict (splitMatrix (F := F) (u 0))
      (splitMatrix (u 1)) (splitMatrix (u 2)) (shapeTensor (P ⊕ Q) (u + v)) x y z =
      if weight x.1 = u 0 ∧ weight y.1 = u 1 ∧ weight z.1 = u 2 then
        shapeTensor (P ⊕ Q) (u + v) (Sum.elim x.1 x.2) (Sum.elim y.1 y.2)
          (Sum.elim z.1 z.2) else 0 := by
    simp [Tensor.restrict, splitMatrix, ite_and, ite_mul, mul_ite]
    split_ifs <;> simp_all
  rw [hcollapse]
  exact shape_split u v x y z

end MatrixMultiplication.CWStrands






namespace MatrixMultiplication.CWCoarseIndices

open MatrixMultiplication.Foundation CWStrands
open scoped BigOperators

theorem label_weight_le_two : ∀ x : Fin 7, CWLeafStatistics.weight x ≤ 2 := by
  decide +kernel

theorem weight_le {P : Type*} [Fintype P] (w : P → Fin 7) :
    weight w ≤ 2 * Fintype.card P := by
  calc
    weight w ≤ ∑ _i : P, 2 := Finset.sum_le_sum fun i _ => label_weight_le_two (w i)
    _ = _ := by simp [Nat.mul_comm]

def coarseIndex {P : Type*} [Fintype P] (hP : Fintype.card P ≤ 8)
    (w : P → Fin 7) : Fin 17 := ⟨weight w, by have := weight_le w; omega⟩

theorem strand_coarse_support {F P : Type*} [CommRing F] [Fintype P]
    (hP : Fintype.card P ≤ 8) (x y z : P → Fin 7)
    (h : strand (F := F) P x y z ≠ 0) :
    (coarseIndex hP x).val + (coarseIndex hP y).val + (coarseIndex hP z).val =
      2 * Fintype.card P := strand_support x y z h

theorem split_coarse_support {F P Q : Type*} [CommRing F] [Fintype P] [Fintype Q]
    (hP : Fintype.card P ≤ 8) (g : Fin 3 → ℕ)
    (x : (P → Fin 7) × (Q → Fin 7))
    (y : (P → Fin 7) × (Q → Fin 7))
    (z : (P → Fin 7) × (Q → Fin 7))
    (h : shapeTensor (F := F) (P ⊕ Q) g (Sum.elim x.1 x.2)
      (Sum.elim y.1 y.2) (Sum.elim z.1 z.2) ≠ 0) :
    ((coarseIndex hP x.1).val + (coarseIndex hP y.1).val +
        (coarseIndex hP z.1).val = 2 * Fintype.card P) ∧
      (coarseIndex hP x.1).val ≤ g 0 ∧ (coarseIndex hP y.1).val ≤ g 1 ∧
        (coarseIndex hP z.1).val ≤ g 2 := by
  have hshape := shapeTensor_support g _ _ _ h
  have ht : strand (F := F) (P ⊕ Q) (Sum.elim x.1 x.2)
      (Sum.elim y.1 y.2) (Sum.elim z.1 z.2) ≠ 0 := by
    simpa only [shapeTensor, ite_eq_left hshape] using h
  rw [strand_sum_elim, Tensor.product] at ht
  have hl : strand (F := F) P x.1 y.1 z.1 ≠ 0 := by
    intro he
    exact ht (by rw [he, zero_mul])
  refine ⟨strand_coarse_support hP x.1 y.1 z.1 hl, ?_, ?_, ?_⟩
  · have hs := hshape.1
    rw [weight_sum_elim] at hs
    exact hs ▸ Nat.le_add_right (weight x.1) (weight x.2)
  · have hs := hshape.2.1
    rw [weight_sum_elim] at hs
    exact hs ▸ Nat.le_add_right (weight y.1) (weight y.2)
  · have hs := hshape.2.2
    rw [weight_sum_elim] at hs
    exact hs ▸ Nat.le_add_right (weight z.1) (weight z.2)

end MatrixMultiplication.CWCoarseIndices






namespace MatrixMultiplication.JointCanonicalCW

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization
open CWStrands HistorySymmetry InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H F : Type*} [Fintype H] [DecidableEq H] [CommRing F]
    (counts : H → Shape → ℕ) (leftLength rightLength : H → ℕ)
    (parentShape : H → Fin 3 → ℕ)
    (hleft : ∀ h, leftLength h ≤ 8)

abbrev Left (h : H) := Fin (leftLength h) → Fin 7
abbrev Right (h : H) := Fin (rightLength h) → Fin 7

def shapeNat (u : Shape) : Fin 3 → ℕ := fun s => (shapeSide s u).val

def parentTensor (h : H) : Tensor F
    (Left leftLength h × Right rightLength h)
    (Left leftLength h × Right rightLength h)
    (Left leftLength h × Right rightLength h) :=
  fun x y z => shapeTensor (Fin (leftLength h) ⊕ Fin (rightLength h)) (parentShape h)
    (Sum.elim x.1 x.2) (Sum.elim y.1 y.2) (Sum.elim z.1 z.2)

def coarse (_s : Fin 3) (h : H) (w : Left leftLength h × Right rightLength h) : Fin 17 :=
  CWCoarseIndices.coarseIndex (by simpa using hleft h) w.1

def leftTensor (c : ClassKey (H := H)) :
    Tensor F (Left leftLength c.1) (Left leftLength c.1) (Left leftLength c.1) :=
  shapeTensor (Fin (leftLength c.1)) (shapeNat c.2)

def rightTensor (c : ClassKey (H := H)) :
    Tensor F (Right rightLength c.1) (Right rightLength c.1) (Right rightLength c.1) :=
  shapeTensor (Fin (rightLength c.1)) (parentShape c.1 - shapeNat c.2)

omit [Fintype H] [DecidableEq H] in
theorem block_eq_product (h : H) (u : Shape)
    (hu : ∀ s, shapeNat u s ≤ parentShape h s) :
    block (Left leftLength) (Right rightLength)
      (parentTensor leftLength rightLength parentShape)
      (coarse leftLength rightLength hleft) (h, u) =
      Tensor.product (leftTensor (F := F) leftLength (h, u))
        (rightTensor rightLength parentShape (h, u)) := by
  have hadd : shapeNat u + (parentShape h - shapeNat u) = parentShape h := by
    funext s
    exact Nat.add_sub_of_le (hu s)
  funext x y z
  have hs := shape_split (F := F) (P := Fin (leftLength h))
    (Q := Fin (rightLength h)) (shapeNat u) (parentShape h - shapeNat u) x y z
  rw [hadd] at hs
  simpa [block, parentTensor, coarse, CWCoarseIndices.coarseIndex,
    Fin.ext_iff, leftTensor, rightTensor, shapeNat, shapeSide,
    Fin.isValue, ↓reduceIte] using hs

omit [DecidableEq H] in
theorem canonicalBase_eq_children
    (hsupport : ∀ h u, 0 < counts h u → ∀ s, shapeNat u s ≤ parentShape h s) :
    canonicalBase counts (Left leftLength) (Right rightLength)
      (parentTensor leftLength rightLength parentShape)
      (coarse leftLength rightLength hleft) =
      pairClassProduct (leftTensor (F := F) leftLength)
        (rightTensor rightLength parentShape) := by
  funext x y z
  unfold canonicalBase
  have hf : (∏ c : ClassKey (H := H), ∏ j : ClassPositions counts c,
      block (Left leftLength) (Right rightLength)
        (parentTensor leftLength rightLength parentShape)
        (coarse leftLength rightLength hleft) c
        (x.left c j, x.right c j) (y.left c j, y.right c j) (z.left c j, z.right c j)) =
      ∏ c : ClassKey (H := H), ∏ j : ClassPositions counts c,
        (leftTensor (F := F) leftLength c (x.left c j) (y.left c j) (z.left c j) *
          rightTensor rightLength parentShape c (x.right c j) (y.right c j) (z.right c j)) := by
    apply Finset.prod_congr rfl
    intro c _
    apply Finset.prod_congr rfl
    intro j _
    have hc : 0 < counts c.1 c.2 := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
    rw [block_eq_product leftLength rightLength parentShape hleft c.1 c.2
      (hsupport c.1 c.2 hc)]
    rfl
  rw [hf]
  simp only [pairClassProduct, classProduct, Finset.prod_mul_distrib]

abbrev RawStrands := ∀ h, Positions counts h →
  ((Fin (leftLength h) ⊕ Fin (rightLength h)) → Fin 7)

def rawParentSource : Tensor F (RawStrands counts leftLength rightLength)
    (RawStrands counts leftLength rightLength) (RawStrands counts leftLength rightLength) :=
  classProduct (fun h => shapeTensor (Fin (leftLength h) ⊕ Fin (rightLength h)) (parentShape h))

def joinWords (w : RawPairs counts (Left leftLength) (Right rightLength)) :
    RawStrands counts leftLength rightLength :=
  fun h i => Sum.elim (w h i).1 (w h i).2

def joinMatrix : RawPairs counts (Left leftLength) (Right rightLength) →
    RawStrands counts leftLength rightLength → F :=
  fun w v => if v = joinWords counts leftLength rightLength w then 1 else 0

theorem parentTensor_restrict :
    Tensor.restrict (joinMatrix (F := F) counts leftLength rightLength)
      (joinMatrix counts leftLength rightLength) (joinMatrix counts leftLength rightLength)
      (rawParentSource counts leftLength rightLength parentShape) =
      sourceTensor counts (Left leftLength) (Right rightLength)
        (parentTensor leftLength rightLength parentShape) := by
  classical
  funext x y z
  simp [Tensor.restrict, joinMatrix, rawParentSource, sourceTensor,
    classProduct, joinWords, parentTensor, ite_mul, mul_ite]

end MatrixMultiplication.JointCanonicalCW






namespace MatrixMultiplication.CWShapeLeaves

open MatrixMultiplication.Foundation CWStrands CWLeafRestrictions
open scoped BigOperators

theorem complement_word_weight {P : Type*} [Fintype P] (w : P → Fin 7) :
    weight (fun i => complement 5 (w i)) + weight w = 2 * Fintype.card P := by
  calc
    weight (fun i => complement 5 (w i)) + weight w =
        ∑ i, (CWLeafStatistics.weight (complement 5 (w i)) + CWLeafStatistics.weight (w i)) := by
      simp [weight, Finset.sum_add_distrib]
    _ = ∑ _i : P, 2 := Finset.sum_congr rfl (fun i _ => CWLeafStatistics.complement_weight (w i))
    _ = 2 * Fintype.card P := by simp [Nat.mul_comm]

theorem zeroX_shape_leaf (F : Type*) [CommRing F] (n a b : ℕ)
    (hab : a + b = 2 * n)
    (p : (Fin n → Fin 7) → Prop) [DecidablePred p]
    (hp : ∀ w, p w → weight w = a) :
    Tensor.pullback (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin 7))
      (fun y : Unit × {w // p w} => y.2.val)
      (fun z : {w // p w} × Unit => fun i => complement 5 (z.1.val i))
      (shapeTensor (F := F) (Fin n) (Matrix.vecCons (0) (Matrix.vecCons (a) (Matrix.vecCons (b) Matrix.vecEmpty)))) =
      Tensor.matrixCoefficients Unit Unit {w // p w} := by
  funext x y z
  have hy : weight y.2.val = a := hp _ y.2.property
  have hz : weight (fun i => complement 5 (z.1.val i)) = b := by
    have hw := complement_word_weight z.1.val
    have hzw : weight z.1.val = a := hp _ z.1.property
    simp only [Fintype.card_fin] at hw
    omega
  have hzero : weight (fun _ : Fin n => (0 : Fin 7)) = 0 := by
    simp [weight, CWLeafStatistics.weight]
  have hleaf := congrFun (congrFun (congrFun (zeroX_leaf F 5 n p) x) y) z
  simpa [Tensor.pullback, shapeTensor, hzero, hy, hz, strand, Tensor.power] using hleaf

theorem zeroY_shape_leaf (F : Type*) [CommRing F] (n a b : ℕ)
    (hab : a + b = 2 * n)
    (p : (Fin n → Fin 7) → Prop) [DecidablePred p]
    (hp : ∀ w, p w → weight w = a) :
    Tensor.pullback (fun x : {w // p w} × Unit => x.1.val)
      (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin 7))
      (fun z : Unit × {w // p w} => fun i => complement 5 (z.2.val i))
      (shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (0) (Matrix.vecCons (b) Matrix.vecEmpty)))) =
      Tensor.matrixCoefficients {w // p w} Unit Unit := by
  funext x y z
  have hx : weight x.1.val = a := hp _ x.1.property
  have hz : weight (fun i => complement 5 (z.2.val i)) = b := by
    have hw := complement_word_weight z.2.val
    have hzw : weight z.2.val = a := hp _ z.2.property
    simp only [Fintype.card_fin] at hw
    omega
  have hzero : weight (fun _ : Fin n => (0 : Fin 7)) = 0 := by
    simp [weight, CWLeafStatistics.weight]
  have hleaf := congrFun (congrFun (congrFun (zeroY_leaf F 5 n p) x) y) z
  simpa [Tensor.pullback, shapeTensor, hzero, hx, hz, strand, Tensor.power] using hleaf

theorem zeroZ_shape_leaf (F : Type*) [CommRing F] (n a b : ℕ)
    (hab : a + b = 2 * n)
    (p : (Fin n → Fin 7) → Prop) [DecidablePred p]
    (hp : ∀ w, p w → weight w = a) :
    Tensor.pullback (fun x : Unit × {w // p w} => x.2.val)
      (fun y : {w // p w} × Unit => fun i => complement 5 (y.1.val i))
      (fun _ : Unit × Unit => fun _ : Fin n => (0 : Fin 7))
      (shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (b) (Matrix.vecCons (0) Matrix.vecEmpty)))) =
      Tensor.matrixCoefficients Unit {w // p w} Unit := by
  funext x y z
  have hx : weight x.2.val = a := hp _ x.2.property
  have hy : weight (fun i => complement 5 (y.1.val i)) = b := by
    have hw := complement_word_weight y.1.val
    have hyw : weight y.1.val = a := hp _ y.1.property
    simp only [Fintype.card_fin] at hw
    omega
  have hzero : weight (fun _ : Fin n => (0 : Fin 7)) = 0 := by
    simp [weight, CWLeafStatistics.weight]
  have hleaf := congrFun (congrFun (congrFun (zeroZ_leaf F 5 n p) x) y) z
  simpa [Tensor.pullback, shapeTensor, hzero, hx, hy, strand, Tensor.power] using hleaf

end MatrixMultiplication.CWShapeLeaves






namespace MatrixMultiplication.CWWindowedLeaves

open MatrixMultiplication.Foundation CWStrands CWShapeLeaves CWLeafRestrictions InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

abbrev Raw (n : ℕ) := Fin n → Fin 7
abbrev Alphabet (n a : ℕ) := {w : Raw n // weight w = a}

def complementWord {n : ℕ} (w : Raw n) : Raw n := fun i => complement 5 (w i)
def zeroWord (n : ℕ) : Raw n := fun _ => 0

variable (F : Type*) [CommRing F]

theorem zeroX_local (n a b : ℕ) (hab : a + b = 2 * n)
    (u v : Alphabet n a) :
    shapeTensor (F := F) (Fin n) (Matrix.vecCons (0) (Matrix.vecCons (a) (Matrix.vecCons (b) Matrix.vecEmpty))) (zeroWord n) u.val (complementWord v.val) =
      if u = v then 1 else 0 := by
  unfold zeroWord complementWord
  have h := zeroX_shape_leaf F n a b hab (fun w => weight w = a) (fun _ h => h)
  have hh := congrFun (congrFun (congrFun h ((), ())) ((), u)) (v, ())
  simpa only [Tensor.pullback, Tensor.matrixCoefficients,
    true_and, and_true] using hh

theorem zeroY_local (n a b : ℕ) (hab : a + b = 2 * n)
    (u v : Alphabet n a) :
    shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (0) (Matrix.vecCons (b) Matrix.vecEmpty))) u.val (zeroWord n) (complementWord v.val) =
      if u = v then 1 else 0 := by
  unfold zeroWord complementWord
  have h := zeroY_shape_leaf F n a b hab (fun w => weight w = a) (fun _ h => h)
  have hh := congrFun (congrFun (congrFun h (u, ())) ((), ())) ((), v)
  have huv : (v = u) ↔ (u = v) := eq_comm
  simpa only [Tensor.pullback, Tensor.matrixCoefficients,
    true_and, and_true, huv] using hh

theorem zeroZ_local (n a b : ℕ) (hab : a + b = 2 * n)
    (u v : Alphabet n a) :
    shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (b) (Matrix.vecCons (0) Matrix.vecEmpty))) u.val (complementWord v.val) (zeroWord n) =
      if u = v then 1 else 0 := by
  unfold zeroWord complementWord
  have h := zeroZ_shape_leaf F n a b hab (fun w => weight w = a) (fun _ h => h)
  have hh := congrFun (congrFun (congrFun h ((), u)) (v, ())) ((), ())
  simpa only [Tensor.pullback, Tensor.matrixCoefficients,
    true_and, and_true] using hh

section Classes

variable (n a b m : ℕ) (hab : a + b = 2 * n)
    (p : (Fin m → Alphabet n a) → Prop) [DecidablePred p]

def rawSelected (w : {w : Fin m → Alphabet n a // p w}) : Fin m → Raw n :=
  fun i => (w.val i).val

def complementarySelected (w : {w : Fin m → Alphabet n a // p w}) : Fin m → Raw n :=
  fun i => complementWord (w.val i).val

include hab

omit [DecidablePred p] in
theorem zeroX_class :
    Tensor.pullback (fun _ : Unit × Unit => fun _ : Fin m => zeroWord n)
      (fun y : Unit × {w // p w} => rawSelected n a m p y.2)
      (fun z : {w // p w} × Unit => complementarySelected n a m p z.1)
      (Tensor.power (shapeTensor (F := F) (Fin n) (Matrix.vecCons (0) (Matrix.vecCons (a) (Matrix.vecCons (b) Matrix.vecEmpty)))) m) =
      Tensor.matrixCoefficients Unit Unit {w // p w} := by
  funext x y z
  simp only [Tensor.pullback, Tensor.power, rawSelected, complementarySelected,
    zeroX_local F n a b hab, Fintype.prod_boole, ← funext_iff, Tensor.matrixCoefficients]
  simp [Subtype.ext_iff]

omit [DecidablePred p] in
theorem zeroY_class :
    Tensor.pullback (fun x : {w // p w} × Unit => rawSelected n a m p x.1)
      (fun _ : Unit × Unit => fun _ : Fin m => zeroWord n)
      (fun z : Unit × {w // p w} => complementarySelected n a m p z.2)
      (Tensor.power (shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (0) (Matrix.vecCons (b) Matrix.vecEmpty)))) m) =
      Tensor.matrixCoefficients {w // p w} Unit Unit := by
  funext x y z
  simp only [Tensor.pullback, Tensor.power, rawSelected, complementarySelected,
    zeroY_local F n a b hab, Fintype.prod_boole, ← funext_iff, Tensor.matrixCoefficients]
  simp [Subtype.ext_iff, eq_comm]

omit [DecidablePred p] in
theorem zeroZ_class :
    Tensor.pullback (fun x : Unit × {w // p w} => rawSelected n a m p x.2)
      (fun y : {w // p w} × Unit => complementarySelected n a m p y.1)
      (fun _ : Unit × Unit => fun _ : Fin m => zeroWord n)
      (Tensor.power (shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (b) (Matrix.vecCons (0) Matrix.vecEmpty)))) m) =
      Tensor.matrixCoefficients Unit {w // p w} Unit := by
  funext x y z
  simp only [Tensor.pullback, Tensor.power, rawSelected, complementarySelected,
    zeroZ_local F n a b hab, Fintype.prod_boole, ← funext_iff, Tensor.matrixCoefficients]
  simp [Subtype.ext_iff]

omit [DecidablePred p] in
theorem zeroX_masked
    (keepX keepY keepZ : (Fin m → Raw n) → Prop)
    (hx : keepX (fun _ => zeroWord n))
    (hy : ∀ w, keepY (rawSelected n a m p w))
    (hz : ∀ w, keepZ (complementarySelected n a m p w)) :
    Tensor.pullback (fun _ : Unit × Unit => fun _ : Fin m => zeroWord n)
      (fun y : Unit × {w // p w} => rawSelected n a m p y.2)
      (fun z : {w // p w} × Unit => complementarySelected n a m p z.1)
      (ExactRecovery.delete (Tensor.power (shapeTensor (F := F) (Fin n) (Matrix.vecCons (0) (Matrix.vecCons (a) (Matrix.vecCons (b) Matrix.vecEmpty)))) m)
        keepX keepY keepZ) = Tensor.matrixCoefficients Unit Unit {w // p w} := by
  have h := zeroX_class F n a b m hab p
  funext x y z
  simpa only [Tensor.pullback, ExactRecovery.delete, hx, hy, hz, and_self, ite_true] using
    congrFun (congrFun (congrFun h x) y) z

omit [DecidablePred p] in
theorem zeroY_masked
    (keepX keepY keepZ : (Fin m → Raw n) → Prop)
    (hx : ∀ w, keepX (rawSelected n a m p w))
    (hy : keepY (fun _ => zeroWord n))
    (hz : ∀ w, keepZ (complementarySelected n a m p w)) :
    Tensor.pullback (fun x : {w // p w} × Unit => rawSelected n a m p x.1)
      (fun _ : Unit × Unit => fun _ : Fin m => zeroWord n)
      (fun z : Unit × {w // p w} => complementarySelected n a m p z.2)
      (ExactRecovery.delete (Tensor.power (shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (0) (Matrix.vecCons (b) Matrix.vecEmpty)))) m)
        keepX keepY keepZ) = Tensor.matrixCoefficients {w // p w} Unit Unit := by
  have h := zeroY_class F n a b m hab p
  funext x y z
  simpa only [Tensor.pullback, ExactRecovery.delete, hx, hy, hz, and_self, ite_true] using
    congrFun (congrFun (congrFun h x) y) z

omit [DecidablePred p] in
theorem zeroZ_masked
    (keepX keepY keepZ : (Fin m → Raw n) → Prop)
    (hx : ∀ w, keepX (rawSelected n a m p w))
    (hy : ∀ w, keepY (complementarySelected n a m p w))
    (hz : keepZ (fun _ => zeroWord n)) :
    Tensor.pullback (fun x : Unit × {w // p w} => rawSelected n a m p x.2)
      (fun y : {w // p w} × Unit => complementarySelected n a m p y.1)
      (fun _ : Unit × Unit => fun _ : Fin m => zeroWord n)
      (ExactRecovery.delete (Tensor.power (shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (b) (Matrix.vecCons (0) Matrix.vecEmpty)))) m)
        keepX keepY keepZ) = Tensor.matrixCoefficients Unit {w // p w} Unit := by
  have h := zeroZ_class F n a b m hab p
  funext x y z
  simpa only [Tensor.pullback, ExactRecovery.delete, hx, hy, hz, and_self, ite_true] using
    congrFun (congrFun (congrFun h x) y) z

omit [DecidablePred p] in
theorem zeroX_restriction
    (keepX keepY keepZ : (Fin m → Raw n) → Prop)
    (hx : keepX (fun _ => zeroWord n))
    (hy : ∀ w, keepY (rawSelected n a m p w))
    (hz : ∀ w, keepZ (complementarySelected n a m p w)) :
    ∃ (A : (Unit × Unit) → (Fin m → Raw n) → F)
      (B : (Unit × {w // p w}) → (Fin m → Raw n) → F)
      (C : ({w // p w} × Unit) → (Fin m → Raw n) → F),
      Tensor.restrict A B C
        (ExactRecovery.delete (Tensor.power (shapeTensor (F := F) (Fin n) (Matrix.vecCons (0) (Matrix.vecCons (a) (Matrix.vecCons (b) Matrix.vecEmpty)))) m)
          keepX keepY keepZ) = Tensor.matrixCoefficients Unit Unit {w // p w} := by
  refine ⟨(fun _ v => if v = (fun _ => zeroWord n) then 1 else 0),
    (fun y v => if v = rawSelected n a m p y.2 then 1 else 0),
    (fun z v => if v = complementarySelected n a m p z.1 then 1 else 0), ?_⟩
  rw [← Tensor.pullback_eq_restrict]
  exact zeroX_masked F n a b m hab p keepX keepY keepZ hx hy hz

omit [DecidablePred p] in
theorem zeroY_restriction
    (keepX keepY keepZ : (Fin m → Raw n) → Prop)
    (hx : ∀ w, keepX (rawSelected n a m p w))
    (hy : keepY (fun _ => zeroWord n))
    (hz : ∀ w, keepZ (complementarySelected n a m p w)) :
    ∃ (A : ({w // p w} × Unit) → (Fin m → Raw n) → F)
      (B : (Unit × Unit) → (Fin m → Raw n) → F)
      (C : (Unit × {w // p w}) → (Fin m → Raw n) → F),
      Tensor.restrict A B C
        (ExactRecovery.delete (Tensor.power (shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (0) (Matrix.vecCons (b) Matrix.vecEmpty)))) m)
          keepX keepY keepZ) = Tensor.matrixCoefficients {w // p w} Unit Unit := by
  refine ⟨(fun x v => if v = rawSelected n a m p x.1 then 1 else 0),
    (fun _ v => if v = (fun _ => zeroWord n) then 1 else 0),
    (fun z v => if v = complementarySelected n a m p z.2 then 1 else 0), ?_⟩
  rw [← Tensor.pullback_eq_restrict]
  exact zeroY_masked F n a b m hab p keepX keepY keepZ hx hy hz

omit [DecidablePred p] in
theorem zeroZ_restriction
    (keepX keepY keepZ : (Fin m → Raw n) → Prop)
    (hx : ∀ w, keepX (rawSelected n a m p w))
    (hy : ∀ w, keepY (complementarySelected n a m p w))
    (hz : keepZ (fun _ => zeroWord n)) :
    ∃ (A : (Unit × {w // p w}) → (Fin m → Raw n) → F)
      (B : ({w // p w} × Unit) → (Fin m → Raw n) → F)
      (C : (Unit × Unit) → (Fin m → Raw n) → F),
      Tensor.restrict A B C
        (ExactRecovery.delete (Tensor.power (shapeTensor (F := F) (Fin n) (Matrix.vecCons (a) (Matrix.vecCons (b) (Matrix.vecCons (0) Matrix.vecEmpty)))) m)
          keepX keepY keepZ) = Tensor.matrixCoefficients Unit {w // p w} Unit := by
  refine ⟨(fun x v => if v = rawSelected n a m p x.2 then 1 else 0),
    (fun y v => if v = complementarySelected n a m p y.1 then 1 else 0),
    (fun _ v => if v = (fun _ => zeroWord n) then 1 else 0), ?_⟩
  rw [← Tensor.pullback_eq_restrict]
  exact zeroZ_masked F n a b m hab p keepX keepY keepZ hx hy hz

end Classes

section ExactWindows

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem exact_selected_window (n a : ℕ) (statistic : Raw n → A)
    (counts : A → ℕ) (ν : A → ℝ) (η : ℝ)
    (happrox : ∀ s, |(counts s : ℝ) / (∑ s, counts s : ℕ) - ν s| ≤ η)
    (w : ExactStatisticWords.Words (fun u : Alphabet n a => statistic u.val) counts) :
    typeWindow ν η (fun i => statistic (w.val i).val) :=
  ExactStatisticWords.typeWindow_of_counts _ counts w ν η happrox

theorem exact_complementary_window (n a : ℕ) (statistic : Raw n → A)
    (κ : A ≃ A)
    (hstatistic : ∀ u : Alphabet n a, statistic (complementWord u.val) = κ (statistic u.val))
    (counts : A → ℕ) (ν : A → ℝ) (η : ℝ)
    (happrox : ∀ s, |(counts s : ℝ) / (∑ s, counts s : ℕ) - ν s| ≤ η)
    (w : ExactStatisticWords.Words (fun u : Alphabet n a => statistic u.val) counts) :
    typeWindow (ν ∘ κ.symm) η (fun i => statistic (complementWord (w.val i).val)) := by
  have heq : (fun i => statistic (complementWord (w.val i).val)) =
      κ ∘ (fun i => statistic (w.val i).val) := by
    funext i
    exact hstatistic (w.val i)
  rw [heq]
  exact (typeWindow_equiv ν η _ κ).mpr
    (exact_selected_window n a statistic counts ν η happrox w)

omit [Fintype A] in
theorem zero_window (n m : ℕ) (hm : 0 < m) (statistic : Raw n → A)
    (ν : A → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hν : ∀ s, ν s = if statistic (zeroWord n) = s then 1 else 0) :
    typeWindow ν η (fun _ : Fin m => statistic (zeroWord n)) := by
  intro s
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  by_cases hs : statistic (zeroWord n) = s <;>
    simpa [empiricalLaw, wordPopulation, hν s, hs, hm'] using hη

end ExactWindows

end MatrixMultiplication.CWWindowedLeaves






namespace MatrixMultiplication.CWCompleteStatistics

open CWWindowedLeaves CWLeafStatistics CWStrands AllFieldParameters
open scoped BigOperators

attribute [local instance] Classical.propDecidable

def pairEquiv : Raw 2 ≃ (Fin 7 × Fin 7) where
  toFun w := (w 0, w 1)
  invFun u := (Matrix.vecCons (u.1) (Matrix.vecCons (u.2) Matrix.vecEmpty))
  left_inv w := by funext i; fin_cases i <;> rfl
  right_inv u := by cases u; rfl

def orderedEquiv : Raw 4 ≃ ((Fin 7 × Fin 7) × (Fin 7 × Fin 7)) where
  toFun w := ((w 0, w 1), (w 2, w 3))
  invFun u := (Matrix.vecCons (u.1.1) (Matrix.vecCons (u.1.2) (Matrix.vecCons (u.2.1) (Matrix.vecCons (u.2.2) Matrix.vecEmpty))))
  left_inv w := by funext i; fin_cases i <;> rfl
  right_inv u := by cases u with | mk u v => cases u; cases v; rfl

def twoStatistic (w : Raw 2) : Fin 6 := pairStatistic (pairEquiv w)
def fourStatistic (w : Raw 4) : Fin 6 × Fin 6 :=
  (pairStatistic (orderedEquiv w).1, pairStatistic (orderedEquiv w).2)

def complementStatistic : Fin 6 ≃ Fin 6 :=
  { toFun := kappa
    invFun := kappa
    left_inv := kappa_involution
    right_inv := kappa_involution }

def orderedComplementStatistic : (Fin 6 × Fin 6) ≃ (Fin 6 × Fin 6) :=
  Equiv.prodCongr complementStatistic complementStatistic

theorem two_weight (w : Raw 2) :
    CWStrands.weight w = statisticWeight (twoStatistic w) := by
  rw [twoStatistic, statistic_weight]
  simp [CWStrands.weight, pairEquiv, Fin.sum_univ_succ]

theorem four_weight (w : Raw 4) :
    CWStrands.weight w = statisticWeight (fourStatistic w).1 +
      statisticWeight (fourStatistic w).2 := by
  simp only [fourStatistic, statistic_weight]
  simp [CWStrands.weight, orderedEquiv, Fin.sum_univ_succ, Nat.add_assoc]

theorem two_multiplicity (s : Fin 6) :
    Fintype.card {w : Raw 2 // twoStatistic w = s} = AllFieldParameters.multiplicity s := by
  let e : {w : Raw 2 // twoStatistic w = s} ≃
      {u : Fin 7 × Fin 7 // pairStatistic u = s} :=
    { toFun := fun w => ⟨pairEquiv w.val, w.property⟩
      invFun := fun u => ⟨pairEquiv.symm u.val, by simpa [twoStatistic] using u.property⟩
      left_inv := by intro w; apply Subtype.ext; simp
      right_inv := by intro u; apply Subtype.ext; simp }
  rw [Fintype.card_congr e, pair_multiplicity]

theorem four_multiplicity (s : Fin 6 × Fin 6) :
    Fintype.card {w : Raw 4 // fourStatistic w = s} =
      AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2 := by
  let e : {w : Raw 4 // fourStatistic w = s} ≃
      {u : (Fin 7 × Fin 7) × (Fin 7 × Fin 7) //
        pairStatistic u.1 = s.1 ∧ pairStatistic u.2 = s.2} :=
    { toFun := fun w => ⟨orderedEquiv w.val,
        congrArg Prod.fst w.property, congrArg Prod.snd w.property⟩
      invFun := fun u => ⟨orderedEquiv.symm u.val, by
        apply Prod.ext
        · simpa [fourStatistic] using u.property.1
        · simpa [fourStatistic] using u.property.2⟩
      left_inv := by intro w; apply Subtype.ext; simp
      right_inv := by intro u; apply Subtype.ext; simp }
  rw [Fintype.card_congr e, ordered_pair_multiplicity]

theorem two_complement (w : Raw 2) :
    twoStatistic (complementWord w) = complementStatistic (twoStatistic w) := by
  exact complement_statistic (pairEquiv w)

theorem four_complement (w : Raw 4) :
    fourStatistic (complementWord w) = orderedComplementStatistic (fourStatistic w) := by
  apply Prod.ext
  · exact complement_statistic (orderedEquiv w).1
  · exact complement_statistic (orderedEquiv w).2

theorem two_fixedWeight_multiplicity (a : ℕ) (s : Fin 6) (hs : statisticWeight s = a) :
    Fintype.card {w : Alphabet 2 a // twoStatistic w.val = s} =
      AllFieldParameters.multiplicity s := by
  rw [ExactStatisticWords.card_fixedWeight_fiber twoStatistic CWStrands.weight
    statisticWeight two_weight a s hs, two_multiplicity]

theorem four_fixedWeight_multiplicity (a : ℕ) (s : Fin 6 × Fin 6)
    (hs : statisticWeight s.1 + statisticWeight s.2 = a) :
    Fintype.card {w : Alphabet 4 a // fourStatistic w.val = s} =
      AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2 := by
  rw [ExactStatisticWords.card_fixedWeight_fiber fourStatistic CWStrands.weight
    (fun s => statisticWeight s.1 + statisticWeight s.2) four_weight a s hs,
    four_multiplicity]

end MatrixMultiplication.CWCompleteStatistics

end
end

end MatrixAllFields

end OAI
