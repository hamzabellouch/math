import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexEntropyContinuity
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionProductLaws

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*} [∀ i, Fintype (A i)]

def independentProduct (p : ∀ i, FiniteLaw (A i)) : FiniteLaw (∀ i, A i) := by
  classical
  exact
    { mass := fun x => ∏ i, (p i).mass (x i)
      nonneg := fun x => Finset.prod_nonneg fun i _ => (p i).nonneg (x i)
      total := by rw [← Fintype.prod_sum]; simp only [(p _).total, Finset.prod_const_one] }

@[simp] theorem independentProduct_mass (p : ∀ i, FiniteLaw (A i)) (x : ∀ i, A i) :
    (independentProduct p).mass x = ∏ i, (p i).mass (x i) := rfl

theorem entropyTerm_prod {J : Type*} [DecidableEq J] (s : Finset J) (f : J → ℝ) :
    entropyTerm (∏ i ∈ s, f i) =
      ∑ i ∈ s, ∏ j ∈ s, if j = i then entropyTerm (f j) else f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, entropyTerm_mul, Finset.sum_insert ha]
    have hrest : (∏ j ∈ s, if j = a then entropyTerm (f j) else f j) =
        ∏ j ∈ s, f j := by
      apply Finset.prod_congr rfl
      intro j hj
      have hja : j ≠ a := by rintro rfl; exact ha hj
      simp only [hja, ite_false]
    rw [Finset.prod_insert ha, ite_eq_left rfl, hrest, ih]
    rw [Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · ring
    · apply Finset.sum_congr rfl
      intro i hi
      have hai : a ≠ i := by rintro rfl; exact ha hi
      rw [Finset.prod_insert ha, ite_eq_right hai]

theorem independentProduct_entropy (p : ∀ i, FiniteLaw (A i)) :
    finiteEntropy (independentProduct p).mass =
      ∑ i, finiteEntropy (p i).mass := by
  classical
  simp only [finiteEntropy, independentProduct_mass, entropyTerm_prod]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fintype.prod_sum (fun j (a : A j) =>
    if j = i then entropyTerm ((p j).mass a) else (p j).mass a)]
  calc
    (∏ j, ∑ a : A j, if j = i then entropyTerm ((p j).mass a) else (p j).mass a) =
        ∏ j, if j = i then (∑ a : A j, entropyTerm ((p j).mass a)) else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hji : j = i <;> simp only [hji, ite_true, ite_false, (p j).total]
    _ = _ := Fintype.prod_ite_eq' i _

omit [∀ index, Fintype (A index)] in
private theorem prod_update_eval
    (f : ∀ i, A i → ℝ) (i : I) (g : A i → ℝ) (x : ∀ i, A i) :
    (∏ j, Function.update f i g j (x j)) =
      g (x i) * ∏ j ∈ Finset.univ.erase i, f j (x j) := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => Function.update f i g j (x j)) (Finset.mem_univ i)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem independentProduct_coordinate_expectation
    (p : ∀ i, FiniteLaw (A i)) (i : I) (g : A i → ℝ) :
    (∑ x, (independentProduct p).mass x * g (x i)) =
      ∑ a, (p i).mass a * g a := by
  classical
  let f : ∀ j, A j → ℝ := fun j => (p j).mass
  let k : ∀ j, A j → ℝ := Function.update f i (fun a => (p i).mass a * g a)
  calc
    (∑ x, (independentProduct p).mass x * g (x i)) =
        ∑ x : ∀ j, A j, ∏ j, k j (x j) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [independentProduct_mass]
      dsimp only [k]
      rw [prod_update_eval]
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => (p j).mass (x j)) (Finset.mem_univ i)]
      dsimp only [f]
      ring
    _ = ∏ j, ∑ a, k j a := (Fintype.prod_sum (κ := A) k).symm
    _ = ∏ j, if j = i then (∑ a, (p i).mass a * g a) else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp [k]
      · simp [k, hji, f, (p j).total]
    _ = _ := by simp

theorem independentProduct_coordinate_mass
    (p : ∀ i, FiniteLaw (A i)) (i : I) (a : A i) :
    ((independentProduct p).map (fun x => x i)).mass a = (p i).mass a := by
  classical
  rw [FiniteLaw.map_mass]
  calc
    (∑ x, if x i = a then (independentProduct p).mass x else 0) =
        ∑ x, (independentProduct p).mass x * (if x i = a then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    _ = ∑ b, (p i).mass b * (if b = a then 1 else 0) :=
      independentProduct_coordinate_expectation p i (fun b => if b = a then 1 else 0)
    _ = _ := by simp

theorem independentProduct_map_mass
    {B : I → Type*} [∀ i, Fintype (B i)]
    (p : ∀ i, FiniteLaw (A i)) (f : ∀ i, A i → B i) (y : ∀ i, B i) :
    ((independentProduct p).map (fun x i => f i (x i))).mass y =
      ∏ i, ((p i).map (f i)).mass (y i) := by
  classical
  rw [FiniteLaw.map_mass]
  calc
    (∑ x, if (fun i => f i (x i)) = y then (independentProduct p).mass x else 0) =
        ∑ x : ∀ i, A i, ∏ i, if f i (x i) = y i then (p i).mass (x i) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : ∀ i, f i (x i) = y i
      · simp [h]
      · have hne : (fun i => f i (x i)) ≠ y := fun he => h (congrFun he)
        rw [ite_eq_right hne]
        obtain ⟨i, hi⟩ := not_forall.mp h
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    _ = ∏ i, ∑ a, if f i a = y i then (p i).mass a else 0 :=
      (Fintype.prod_sum (fun i (a : A i) => if f i a = y i then (p i).mass a else 0)).symm
    _ = _ := by simp only [FiniteLaw.map_mass]

theorem independentProduct_map_entropy
    {B : I → Type*} [∀ i, Fintype (B i)]
    (p : ∀ i, FiniteLaw (A i)) (f : ∀ i, A i → B i) :
    finiteEntropy ((independentProduct p).map (fun x i => f i (x i))).mass =
      ∑ i, finiteEntropy ((p i).map (f i)).mass := by
  have hmass : ((independentProduct p).map (fun x i => f i (x i))).mass =
      (independentProduct (fun i => (p i).map (f i))).mass := by
    funext y
    exact independentProduct_map_mass p f y
  rw [hmass, independentProduct_entropy]

def sigmaJoint (p : FiniteLaw I) (q : ∀ i, FiniteLaw (A i)) : FiniteLaw (Sigma A) where
  mass x := p.mass x.1 * (q x.1).mass x.2
  nonneg x := mul_nonneg (p.nonneg x.1) ((q x.1).nonneg x.2)
  total := by simp [Fintype.sum_sigma, ← Finset.mul_sum, (q _).total, p.total]

omit [DecidableEq I] in
@[simp] theorem sigmaJoint_mass (p : FiniteLaw I) (q : ∀ i, FiniteLaw (A i)) (x : Sigma A) :
    (sigmaJoint p q).mass x = p.mass x.1 * (q x.1).mass x.2 := rfl

omit [DecidableEq I] in
theorem sigmaJoint_entropy (p : FiniteLaw I) (q : ∀ i, FiniteLaw (A i)) :
    finiteEntropy (sigmaJoint p q).mass =
      finiteEntropy p.mass + ∑ i, p.mass i * finiteEntropy (q i).mass := by
  simp only [finiteEntropy, sigmaJoint_mass, Fintype.sum_sigma, entropyTerm_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, (q _).total, one_mul]

theorem sigmaJoint_fst_mass (p : FiniteLaw I) (q : ∀ i, FiniteLaw (A i)) (i : I) :
    ((sigmaJoint p q).map Sigma.fst).mass i = p.mass i := by
  classical
  simp [FiniteLaw.map_mass, Fintype.sum_sigma, sigmaJoint_mass,
    Finset.sum_ite_irrel, ← Finset.mul_sum, (q _).total]

omit [DecidableEq I] in
theorem sigmaJoint_map_mass {B : Type*} [Fintype B]
    (p : FiniteLaw I) (q : ∀ i, FiniteLaw (A i)) (f : Sigma A → B) (b : B) :
    ((sigmaJoint p q).map f).mass b =
      ∑ i, p.mass i * ((q i).map (fun a => f ⟨i, a⟩)).mass b := by
  classical
  simp only [FiniteLaw.map_mass, Fintype.sum_sigma, sigmaJoint_mass]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

end MatrixMultiplication.CompletionProductLaws

end

end OAI
