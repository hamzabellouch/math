import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import OAI.Computability.PerfectCompleteness.Construction.TreeSourceSpaces
import OAI.Computability.PerfectCompleteness.Foundations.OddLists

namespace OAI


namespace PerfectCompleteness.OddListExtraction

open scoped BigOperators Classical
open PointwiseSpaces

abbrev F2 := ZMod 2

variable {X Y A B : Type*}

noncomputable def indicator (q : X → A) (a : A) : X → F2 :=
  fun x => if q x = a then 1 else 0

@[simp] theorem indicator_mul_self (q : X → A) (a : A) :
    indicator q a * indicator q a = indicator q a := by
  classical
  funext x
  by_cases h : q x = a <;> simp [indicator, h]

theorem indicator_mul_of_ne (q : X → A) {a b : A} (hab : a ≠ b) :
    indicator q a * indicator q b = 0 := by
  classical
  funext x
  by_cases ha : q x = a
  · simp [indicator, ha, hab]
  · simp [indicator, ha]

@[simp] theorem sum_indicator [Fintype A] (q : X → A) :
    ∑ a, indicator q a = (1 : X → F2) := by
  classical
  funext x
  simp [indicator, Finset.sum_apply]

theorem indicator_comp [Fintype A] (q : X → A) (π : A → B) (b : B) :
    indicator (π ∘ q) b = ∑ a ∈ Finset.univ.filter (fun a => π a = b), indicator q a := by
  classical
  funext x
  simp only [Finset.sum_apply, indicator, Function.comp_apply]
  by_cases hb : π (q x) = b
  · rw [ite_eq_left hb]
    symm
    rw [Finset.sum_eq_single (q x)]
    · simp
    · intro a _ ha
      simp only [ite_eq_right (Ne.symm ha)]
    · intro h
      exact (h (by simp [hb])).elim
  · rw [ite_eq_right hb]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    have hqa : q x ≠ a := by
      intro heq
      exact hb ((congrArg π heq).trans (Finset.mem_filter.mp ha).2)
    exact ite_eq_right hqa

theorem leaf_indicator_mem (branch : Nat → Nat) :
    ∀ (n : Nat) (D : RecursiveSpaces.Slots branch n → Type*)
      (s : RecursiveSpaces.Slots branch n) (a : D s),
      indicator (fun x : RecursiveSpaces.Assignment D => x s) a ∈
        RecursiveSpaces.space F2 branch n D := by
  intro n
  induction n with
  | zero =>
      intro D s a
      exact Submodule.mem_top
  | succ n ih =>
      intro D s a
      rcases s with ⟨i, s⟩
      have h := ih (RecursiveSpaces.childFamily D i) s a
      have hsquare : indicator
          (fun x : RecursiveSpaces.Assignment (RecursiveSpaces.childFamily D i) => x s) a ∈
          squareSpace (RecursiveSpaces.space F2 branch n (RecursiveSpaces.childFamily D i)) := by
        simpa only [indicator_mul_self] using mul_mem_squareSpace _ h h
      exact RecursiveSpaces.child_square_le_space D i (Submodule.mem_map_of_mem hsquare)

theorem source_leaf_indicator_mem {branch : Nat → Nat} {n t : Nat}
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (s : RecursiveSpaces.Slots branch n) (a : TreeSourceSpaces.LeafDomain slots s) :
    indicator (fun x : TreeSourceSpaces.Domain slots => x s) a ∈ TreeSourceSpaces.H slots :=
  leaf_indicator_mem branch n (TreeSourceSpaces.LeafDomain slots) s a

section Form

variable (H : Submodule F2 (X → F2))

def productElement (f g : H) : squareSpace H :=
  ⟨f.val * g.val, mul_mem_squareSpace H f.property g.property⟩

def multiplicationForm (z : Module.Dual F2 (squareSpace H)) : H →ₗ[F2] H →ₗ[F2] F2 :=
  LinearMap.mk₂ F2 (fun f g => z (productElement H f g))
    (by
      intro f g h
      rw [← map_add]
      congr 1
      apply Subtype.ext
      exact add_mul _ _ _)
    (by
      intro c f g
      rw [← map_smul]
      congr 1
      apply Subtype.ext
      exact smul_mul_assoc _ _ _)
    (by
      intro f g h
      rw [← map_add]
      congr 1
      apply Subtype.ext
      exact mul_add _ _ _)
    (by
      intro c f g
      rw [← map_smul]
      congr 1
      apply Subtype.ext
      exact mul_smul_comm _ _ _)

@[simp] theorem multiplicationForm_apply (z : Module.Dual F2 (squareSpace H))
    (f g : H) : multiplicationForm H z f g = z (productElement H f g) := rfl

noncomputable def formRank (F : H →ₗ[F2] H →ₗ[F2] F2) : Nat :=
  Module.finrank F2 (LinearMap.range F)

variable (q : X → A) (hmem : ∀ a, indicator q a ∈ H)

noncomputable def atom (a : A) : H := ⟨indicator q a, hmem a⟩

noncomputable def diagonal (z : Module.Dual F2 (squareSpace H)) (a : A) : F2 :=
  multiplicationForm H z (atom H q hmem a) (atom H q hmem a)

@[simp] theorem form_atom_self (z : Module.Dual F2 (squareSpace H)) (a : A) :
    multiplicationForm H z (atom H q hmem a) (atom H q hmem a) =
      diagonal H q hmem z a := rfl

theorem form_atom_of_ne (z : Module.Dual F2 (squareSpace H)) {a b : A} (hab : a ≠ b) :
    multiplicationForm H z (atom H q hmem a) (atom H q hmem b) = 0 := by
  have hzero : productElement H (atom H q hmem a) (atom H q hmem b) = 0 := by
    apply Subtype.ext
    exact indicator_mul_of_ne q hab
  simp only [multiplicationForm_apply, hzero, map_zero]

theorem sum_diagonal [Fintype A] (z : Module.Dual F2 (squareSpace H))
    (hone : (1 : X → F2) ∈ squareSpace H) :
    ∑ a, diagonal H q hmem z a = z ⟨1, hone⟩ := by
  classical
  simp only [diagonal, multiplicationForm_apply, ← map_sum]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_sum]
  change (∑ a, (indicator q a * indicator q a)) = (1 : X → F2)
  simp only [indicator_mul_self, sum_indicator]

theorem diagonal_support_card_le_rank [Fintype X] [Fintype A]
    (z : Module.Dual F2 (squareSpace H)) :
    (OddLists.support (diagonal H q hmem z)).card ≤ formRank H (multiplicationForm H z) := by
  classical
  let S := OddLists.support (diagonal H q hmem z)
  let F := multiplicationForm H z
  let v : S → LinearMap.range F := fun a =>
    ⟨F (atom H q hmem a.val), ⟨atom H q hmem a.val, rfl⟩⟩
  have hv : LinearIndependent F2 v := by
    apply (Fintype.linearIndependent_iff (R := F2) (v := v)).mpr
    intro c hc a
    have he := congrArg (fun w : LinearMap.range F => w.val (atom H q hmem a.val)) hc
    have hentry : ∀ b : S, (v b).val (atom H q hmem a.val) = if b = a then 1 else 0 := by
      intro b
      by_cases hba : b = a
      · subst b
        have ha : diagonal H q hmem z a.val = 1 := by
          exact (Finset.mem_filter.mp a.property).2
        exact ha.trans (ite_eq_left rfl).symm
      · have hne : b.val ≠ a.val := fun h => hba (Subtype.ext h)
        exact (form_atom_of_ne H q hmem z hne).trans (ite_eq_right hba).symm
    simpa only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_zero,
      LinearMap.zero_apply, hentry, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] using he
  simpa only [Fintype.card_coe, S, F, formRank] using hv.fintype_card_le_finrank

noncomputable def extractedList [Fintype X] [Fintype A]
    (z : Module.Dual F2 (squareSpace H)) (hone : (1 : X → F2) ∈ squareSpace H)
    (hnorm : z ⟨1, hone⟩ = 1) (s : Nat)
    (hrank : formRank H (multiplicationForm H z) ≤ s) : OddLists.OddList s A :=
  ⟨OddLists.support (diagonal H q hmem z),
    OddLists.support_odd_of_sum_one _ ((sum_diagonal H q hmem z hone).trans hnorm),
    (diagonal_support_card_le_rank H q hmem z).trans hrank⟩

end Form

section Projection

variable [Fintype A] [Fintype B]
variable (H : Submodule F2 (X → F2)) (K : Submodule F2 (Y → F2))
variable (q : X → A) (r : Y → B)
variable (hH : ∀ a, indicator q a ∈ H) (hK : ∀ b, indicator r b ∈ K)
variable (p : X → Y) (π : A → B) (hcomm : ∀ x, r (p x) = π (q x))
variable (T : K →ₗ[F2] H) (hT : ∀ (f : K) x, (T f).val x = f.val (p x))

include hcomm hT

omit [Fintype B] in
theorem atom_pullback (b : B) :
    T (atom K r hK b) = ∑ a ∈ Finset.univ.filter (fun a => π a = b), atom H q hH a := by
  classical
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_sum, Finset.sum_apply, hT, atom]
  have h := congrFun (indicator_comp q π b) x
  simpa only [indicator, Finset.sum_apply, Function.comp_apply, hcomm] using h

omit [Fintype B] in
theorem projected_diagonal
    (z : Module.Dual F2 (squareSpace H)) (F' : K →ₗ[F2] K →ₗ[F2] F2)
    (hagree : ∀ f g, F' f g = multiplicationForm H z (T f) (T g)) (b : B) :
    F' (atom K r hK b) (atom K r hK b) =
      ∑ a ∈ Finset.univ.filter (fun a => π a = b), diagonal H q hH z a := by
  classical
  rw [hagree]
  simp only [multiplicationForm_apply, diagonal, ← map_sum]
  congr 1
  apply Subtype.ext
  funext x
  change (T (atom K r hK b)).val x * (T (atom K r hK b)).val x = _
  simp only [hT, atom, Submodule.coe_sum, Finset.sum_apply, productElement,
    Pi.mul_apply]
  have h := congrFun (indicator_comp q π b) x
  simp only [Finset.sum_apply] at h
  have hidem : ∀ a : A, indicator q a x * indicator q a x = indicator q a x :=
    fun a => congrFun (indicator_mul_self q a) x
  simp only [hidem]
  rw [← h]
  simp only [indicator, Function.comp_apply, hcomm]
  split_ifs <;> simp

theorem projected_support
    (z : Module.Dual F2 (squareSpace H)) (F' : K →ₗ[F2] K →ₗ[F2] F2)
    (hagree : ∀ f g, F' f g = multiplicationForm H z (T f) (T g)) :
    OddLists.support (fun b => F' (atom K r hK b) (atom K r hK b)) =
      OddLists.parityPushforward π (OddLists.support (diagonal H q hH z)) := by
  classical
  rw [OddLists.parityPushforward_support]
  congr 1
  funext b
  rw [projected_diagonal H K q r hH hK p π hcomm T hT z F' hagree b]
  exact Finset.sum_filter _ _

theorem local_extraction_accepts [Fintype X]
    (z : Module.Dual F2 (squareSpace H)) (F' : K →ₗ[F2] K →ₗ[F2] F2)
    (hagree : ∀ f g, F' f g = multiplicationForm H z (T f) (T g))
    (hone : (1 : X → F2) ∈ squareSpace H) (hnorm : z ⟨1, hone⟩ = 1)
    (s : Nat) (positive : 0 < s) (hrank : formRank H (multiplicationForm H z) ≤ s)
    (leftFallback : A) (rightFallback : B) :
    OddLists.OddList.map π
      (OddLists.OddList.extract positive leftFallback
        (OddLists.support (diagonal H q hH z))) =
      OddLists.OddList.extract positive rightFallback
        (OddLists.support (fun b => F' (atom K r hK b) (atom K r hK b))) := by
  classical
  have hleft : Odd (OddLists.support (diagonal H q hH z)).card ∧
      (OddLists.support (diagonal H q hH z)).card ≤ s :=
    (extractedList H q hH z hone hnorm s hrank).property
  have hsupport := projected_support H K q r hH hK p π hcomm T hT z F' hagree
  have hright :
      Odd (OddLists.support (fun b => F' (atom K r hK b) (atom K r hK b))).card ∧
      (OddLists.support (fun b => F' (atom K r hK b) (atom K r hK b))).card ≤ s := by
    rw [hsupport]
    exact ⟨OddLists.parityPushforward_odd π _ hleft.1,
      (OddLists.parityPushforward_card_le π _).trans hleft.2⟩
  apply Subtype.ext
  rw [OddLists.OddList.map_val,
    OddLists.OddList.extract_valid positive leftFallback _ hleft,
    OddLists.OddList.extract_valid positive rightFallback _ hright]
  exact hsupport.symm

end Projection

private theorem parityPushforward_decidableEq_irrel [Fintype B]
    (d₁ d₂ : DecidableEq B) (π : A → B) (L : Finset A) :
    @OddLists.parityPushforward A B _ d₁ π L =
      @OddLists.parityPushforward A B _ d₂ π L :=
  congrArg (fun d : DecidableEq B => @OddLists.parityPushforward A B _ d π L)
    (Subsingleton.elim d₁ d₂)

theorem source_projected_support {branch : Nat → Nat} {n t : Nat}
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (s : RecursiveSpaces.Slots branch n)
    (z : Module.Dual F2 (squareSpace (TreeSourceSpaces.H slots)))
    (F' : TreeSourceSpaces.H projected →ₗ[F2] TreeSourceSpaces.H projected →ₗ[F2] F2)
    (hagree : ∀ f g, F' f g = multiplicationForm (TreeSourceSpaces.H slots) z
      (TreeSourceSpaces.HPullback p f) (TreeSourceSpaces.HPullback p g)) :
    OddLists.support (fun b => F'
      (atom (TreeSourceSpaces.H projected) (fun x => x s)
        (source_leaf_indicator_mem projected s) b)
      (atom (TreeSourceSpaces.H projected) (fun x => x s)
        (source_leaf_indicator_mem projected s) b)) =
      OddLists.parityPushforward (MixedSupport.projectionMap (p s))
        (OddLists.support (diagonal (TreeSourceSpaces.H slots) (fun x => x s)
          (source_leaf_indicator_mem slots s) z)) := by
  have h := projected_support (TreeSourceSpaces.H slots) (TreeSourceSpaces.H projected)
    (fun x => x s) (fun x => x s) (source_leaf_indicator_mem slots s)
    (source_leaf_indicator_mem projected s) (TreeSourceSpaces.sourceProjection p)
    (MixedSupport.projectionMap (p s)) (fun _ => rfl)
    (TreeSourceSpaces.HPullback p) (fun _ _ => rfl) z F' hagree
  exact h.trans (parityPushforward_decidableEq_irrel _ _ _ _)

end PerfectCompleteness.OddListExtraction

end OAI
