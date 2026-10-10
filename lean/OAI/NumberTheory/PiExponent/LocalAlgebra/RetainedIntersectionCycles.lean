import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeCutBudget

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w

def ProjectiveComponent (k : Type u) (σ : Type v) [Field k] :=
  {P : Ideal (MvPolynomial σ k) // P.IsPrime ∧
    P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) ∧
    ∃ i : σ, MvPolynomial.X i ∉ P}

namespace ProjectiveComponent

variable {k : Type u} {σ : Type v} [Field k]

instance (P : ProjectiveComponent k σ) : P.val.IsPrime := P.property.1

theorem homogeneous (P : ProjectiveComponent k σ) :
    P.val.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := P.property.2.1

noncomputable def coordinate (P : ProjectiveComponent k σ) : σ :=
  P.property.2.2.choose

theorem coordinate_not_mem (P : ProjectiveComponent k σ) :
    MvPolynomial.X P.coordinate ∉ P.val := P.property.2.2.choose_spec

variable [Fintype σ]

noncomputable def hilbertDegree (P : ProjectiveComponent k σ) : ℚ :=
  actualMultiplicity P.val P.homogeneous (actualHP P.val P.homogeneous).natDegree

theorem hilbertDegree_ge_one (P : ProjectiveComponent k σ) : 1 ≤ P.hilbertDegree := by
  obtain ⟨N, hN⟩ := actualHP_eventually P.val P.homogeneous
  exact W27.prime_eventual_hilbert_coefficient_ge_one P.val P.coordinate P.coordinate_not_mem
    (actualHP P.val P.homogeneous) (N+1) (actualHP P.val P.homogeneous).natDegree
    (fun n hn => (hN n (by omega)).symm) rfl

end ProjectiveComponent

structure RetainedPrimeCycle (k : Type u) (σ : Type v) [Field k] where
  Index : Type w
  finiteIndex : Fintype Index
  component : Index → ProjectiveComponent k σ
  coefficient : Index → ℕ

namespace RetainedPrimeCycle

variable {k : Type u} {σ : Type v} [Field k] [Fintype σ]

instance (C : RetainedPrimeCycle.{u,v,w} k σ) : Fintype C.Index := C.finiteIndex

noncomputable def degree (C : RetainedPrimeCycle.{u,v,w} k σ) : ℚ :=
  ∑ a, (C.coefficient a : ℚ) * (C.component a).hilbertDegree

noncomputable def coefficientAt (C : RetainedPrimeCycle.{u,v,w} k σ)
    (P : ProjectiveComponent k σ) : ℕ :=
  ∑ a, if C.component a = P then C.coefficient a else 0

theorem degree_nonneg (C : RetainedPrimeCycle.{u,v,w} k σ) : 0 ≤ C.degree := by
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (Nat.cast_nonneg _) (le_trans (by norm_num)
    (ProjectiveComponent.hilbertDegree_ge_one (C.component a)))

theorem coefficientAt_le_degree (C : RetainedPrimeCycle.{u,v,w} k σ)
    (P : ProjectiveComponent k σ) : (C.coefficientAt P : ℚ) ≤ C.degree := by
  unfold coefficientAt degree
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases h : C.component a = P
  · simp only [ite_eq_left h]
    have hc : (0 : ℚ) ≤ C.coefficient a := Nat.cast_nonneg _
    have hd := (C.component a).hilbertDegree_ge_one
    nlinarith
  · simp only [ite_eq_right h, Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (le_trans (by norm_num)
      (C.component a).hilbertDegree_ge_one)

structure ProperCut (C : RetainedPrimeCycle.{u,v,w} k σ) where
  polynomial : MvPolynomial σ k
  polynomialDegree : ℕ
  positiveDegree : 0 < polynomialDegree
  homogeneous : polynomial.IsHomogeneous polynomialDegree
  avoidsParent : ∀ a, polynomial ∉ (C.component a).val
  dimensionIndex : ℕ
  parentDegree : ∀ a,
    (actualHP (C.component a).val (C.component a).homogeneous).natDegree = dimensionIndex+1
  Child : C.Index → Type w
  finiteChild : ∀ a, Fintype (Child a)
  child : ∀ a, Child a → ProjectiveComponent k σ
  distinctChild : ∀ a, Function.Injective (child a)
  minimalChild : ∀ a b,
    (child a b).val ∈ (Ideal.span {polynomial} ⊔ (C.component a).val).minimalPrimes
  childDegree : ∀ a b,
    (actualHP (child a b).val (child a b).homogeneous).natDegree = dimensionIndex

namespace ProperCut

variable {C : RetainedPrimeCycle.{u,v,w} k σ}

instance (F : ProperCut C) (a : C.Index) : Fintype (F.Child a) := F.finiteChild a

noncomputable def cutLength (F : ProperCut C) (a : C.Index) (b : F.Child a) : ℕ :=
  actualLocalLength (Ideal.span {F.polynomial} ⊔ (C.component a).val) (F.child a b).val

theorem cutLength_spec (F : ProperCut C) (a : C.Index) (b : F.Child a) :
    Module.length (Localization.AtPrime (F.child a b).val)
      (Localization.AtPrime (F.child a b).val ⧸
        (Ideal.span {F.polynomial} ⊔ (C.component a).val).map
          (algebraMap (MvPolynomial σ k) (Localization.AtPrime (F.child a b).val))) =
      F.cutLength a b :=
  actualLocalLength_spec _ _
    (primeCut_isHomogeneous _ (C.component a).homogeneous F.polynomial F.homogeneous)
    (F.minimalChild a b)

noncomputable def next (F : ProperCut C) : RetainedPrimeCycle.{u,v,w} k σ where
  Index := Σ a : C.Index, F.Child a
  finiteIndex := inferInstance
  component := fun x => F.child x.1 x.2
  coefficient := fun x => C.coefficient x.1 * F.cutLength x.1 x.2

@[simp] theorem next_component (F : ProperCut C) (a : C.Index) (b : F.Child a) :
    F.next.component ⟨a,b⟩ = F.child a b := rfl

@[simp] theorem next_coefficient (F : ProperCut C) (a : C.Index) (b : F.Child a) :
    F.next.coefficient ⟨a,b⟩ = C.coefficient a * F.cutLength a b := rfl

def CoversBelow (F : ProperCut C) (T : Ideal (MvPolynomial σ k)) : Prop :=
  ∀ a Q, Q ∈ (Ideal.span {F.polynomial} ⊔ (C.component a).val).minimalPrimes →
    Q ≤ T → ∃ b, (F.child a b).val = Q

theorem parent_budget (F : ProperCut C) (a : C.Index) :
    (∑ b, (F.cutLength a b : ℚ) * (F.child a b).hilbertDegree) ≤
      (F.polynomialDegree : ℚ) * (C.component a).hilbertDegree := by
  have hinj : Function.Injective (fun b : F.Child a => (F.child a b).val) := by
    intro b c h
    exact F.distinctChild a (Subtype.ext h)
  have h := prime_cut_component_budget (C.component a).val (C.component a).homogeneous
    F.polynomial F.homogeneous (F.avoidsParent a) F.positiveDegree F.dimensionIndex
    (F.parentDegree a) (fun b : F.Child a => (F.child a b).val) hinj
    (fun b => (F.child a b).homogeneous) (F.minimalChild a)
    (fun b => (F.child a b).coordinate) (fun b => (F.child a b).coordinate_not_mem)
    (F.childDegree a)
  simpa only [cutLength, ProjectiveComponent.hilbertDegree, F.childDegree, F.parentDegree] using h

theorem degree_next_le (F : ProperCut C) :
    F.next.degree ≤ (F.polynomialDegree : ℚ) * C.degree := by
  change (∑ x : Σ a : C.Index, F.Child a,
    ((C.coefficient x.1 * F.cutLength x.1 x.2 : ℕ) : ℚ) *
      (F.child x.1 x.2).hilbertDegree) ≤ _
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ a, (C.coefficient a : ℚ) *
        ((F.polynomialDegree : ℚ) * (C.component a).hilbertDegree) := by
      apply Finset.sum_le_sum
      intro a _
      simpa only [Nat.cast_mul, mul_assoc, Finset.mul_sum] using
        mul_le_mul_of_nonneg_left (F.parent_budget a) (Nat.cast_nonneg (C.coefficient a))
    _ = (F.polynomialDegree : ℚ) * C.degree := by
      rw [degree, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

end ProperCut

inductive ProperCutHistory (C₀ : RetainedPrimeCycle.{u,v,w} k σ) :
    RetainedPrimeCycle.{u,v,w} k σ → ℕ → Prop
  | nil : ProperCutHistory C₀ C₀ 1
  | step {C : RetainedPrimeCycle.{u,v,w} k σ} {e : ℕ}
      (previous : ProperCutHistory C₀ C e) (F : ProperCut C) :
      ProperCutHistory C₀ F.next (e * F.polynomialDegree)

theorem ProperCutHistory.degree_bound
    {C₀ C : RetainedPrimeCycle.{u,v,w} k σ} {e : ℕ}
    (h : ProperCutHistory C₀ C e) : C.degree ≤ (e : ℚ) * C₀.degree := by
  induction h with
  | nil => simp
  | @step C e previous F ih =>
    calc
      F.next.degree ≤ (F.polynomialDegree : ℚ) * C.degree := F.degree_next_le
      _ ≤ (F.polynomialDegree : ℚ) * ((e : ℚ) * C₀.degree) :=
        mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg F.polynomialDegree)
      _ = ((e * F.polynomialDegree : ℕ) : ℚ) * C₀.degree := by
        rw [Nat.cast_mul]
        ring

theorem ProperCutHistory.coefficient_bound
    {C₀ C : RetainedPrimeCycle.{u,v,w} k σ} {e : ℕ}
    (h : ProperCutHistory C₀ C e) (P : ProjectiveComponent k σ) :
    (C.coefficientAt P : ℚ) ≤ (e : ℚ) * C₀.degree :=
  (C.coefficientAt_le_degree P).trans h.degree_bound

end RetainedPrimeCycle
end PiExponentJets.W22

end OAI
