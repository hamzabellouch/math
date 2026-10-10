import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.Bits
import OAI.Combinatorics.IndependentSets.PCP.AssignmentTester
import OAI.Combinatorics.IndependentSets.PCP.CodeComposition

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.AlphabetReduction

open IndependentSetsGames.Foundations.Hastad
open CodeComposition

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev LegalPair (accepts : A → A → Bool) :=
  {p : A × A // accepts p.1 p.2 = true}

abbrev InputCoordinate (A : Type*) := Bool × Cube A

def pairEncoding (accepts : A → A → Bool) (p : LegalPair accepts) :
    InputCoordinate A → Bool :=
  pairWord (codeword p.1.1) (codeword p.1.2)

def edgeTesterReject (accepts : A → A → Bool) (left right : Cube A → Bool)
    (F : Cube (LegalPair accepts) → Bool) : ℝ :=
  AssignmentTester.explicitTesterReject (pairEncoding accepts) (pairWord left right) F

theorem rejected_edge_tester_bound (accepts : A → A → Bool)
    (left right : Cube A → Bool)
    (F : Cube (LegalPair accepts) → Bool)
    (hbad : accepts (nearest left) (nearest right) = false) :
    1 / 2048 ≤ edgeTesterReject accepts left right F := by
  have hfar (p : LegalPair accepts) :
      (1 / 8 : ℝ) ≤ AssignmentTester.distance (pairWord left right) (pairEncoding accepts p) := by
    have h := rejected_pair_far accepts left right hbad p.1.1 p.1.2 p.2
    convert h using 1
    rfl
  have h := AssignmentTester.explicit_proximity_soundness (pairEncoding accepts)
    (pairWord left right) F (δ := 1 / 8) (by norm_num) (by norm_num) hfar
  norm_num at h
  exact h

omit [Nonempty A] in
theorem honest_edge_tester (accepts : A → A → Bool) (a b : A)
    (hab : accepts a b = true) :
    edgeTesterReject accepts (codeword a) (codeword b)
      (fun f => f ⟨(a, b), hab⟩) = 0 := by
  unfold edgeTesterReject
  rw [AssignmentTester.explicitTesterReject_eq]
  exact AssignmentTester.tester_perfect_completeness
    (pairEncoding accepts) ⟨(a, b), hab⟩

end IndependentSetsGames.Foundations.PCP.AlphabetReduction
end
namespace IndependentSetsGames.Foundations.PCP.UniformRestriction

open scoped BigOperators

variable {B : Type*} (p : B → Prop)

def restrict (f : B → Bool) : {b // p b} → Bool := fun b => f b.1

variable [DecidablePred p]

def extend (g : {b // p b} → Bool) : B → Bool :=
  fun b => if hb : p b then g ⟨b, hb⟩ else false

def canonicalize (f : B → Bool) : B → Bool := extend p (restrict p f)

omit [DecidablePred p] in
@[simp] theorem restrict_apply (f : B → Bool) (b : {b // p b}) :
    restrict p f b = f b.1 := rfl

@[simp] theorem extend_apply_of_mem (g : {b // p b} → Bool) (b : B) (hb : p b) :
    extend p g b = g ⟨b, hb⟩ := by
  simp [extend, hb]

@[simp] theorem extend_apply_of_not_mem (g : {b // p b} → Bool) (b : B)
    (hb : ¬ p b) : extend p g b = false := by
  simp [extend, hb]

@[simp] theorem restrict_extend (g : {b // p b} → Bool) :
    restrict p (extend p g) = g := by
  funext b
  simp [restrict, extend, b.property]

@[simp] theorem canonicalize_apply_of_mem (f : B → Bool) (b : B) (hb : p b) :
    canonicalize p f b = f b := by
  simp [canonicalize, hb]

@[simp] theorem canonicalize_apply_of_not_mem (f : B → Bool) (b : B)
    (hb : ¬ p b) : canonicalize p f b = false := by
  simp [canonicalize, hb]

@[simp] theorem restrict_canonicalize (f : B → Bool) :
    restrict p (canonicalize p f) = restrict p f := by
  exact restrict_extend p (restrict p f)

@[simp] theorem canonicalize_idempotent (f : B → Bool) :
    canonicalize p (canonicalize p f) = canonicalize p f := by
  simp only [canonicalize, restrict_extend]

theorem canonicalize_eq_iff (f g : B → Bool) :
    canonicalize p f = canonicalize p g ↔ restrict p f = restrict p g := by
  constructor
  · intro h
    simpa only [restrict_canonicalize] using congrArg (restrict p) h
  · intro h
    exact congrArg (extend p) h

variable [Fintype B] [DecidableEq B]

theorem expect_restrict (h : ({b // p b} → Bool) → ℝ) :
    (𝔼 f : B → Bool, h (restrict p f)) = 𝔼 g : {b // p b} → Bool, h g := by
  calc
    (𝔼 f : B → Bool, h (restrict p f)) =
        𝔼 g : ({b // p b} → Bool) × ({b // ¬ p b} → Bool), h g.1 :=
      Fintype.expect_equiv (Equiv.piEquivPiSubtypeProd p (fun _ => Bool))
        _ _ (fun _ => rfl)
    _ = 𝔼 g : {b // p b} → Bool, 𝔼 _k : {b // ¬ p b} → Bool, h g := by
      simpa only [Finset.univ_product_univ] using
        Finset.expect_product
          (Finset.univ : Finset ({b // p b} → Bool))
          (Finset.univ : Finset ({b // ¬ p b} → Bool))
          (fun g : ({b // p b} → Bool) × ({b // ¬ p b} → Bool) => h g.1)
    _ = 𝔼 g : {b // p b} → Bool, h g := by
      simp only [Fintype.expect_const]

theorem expect_canonicalize (h : (B → Bool) → ℝ) :
    (𝔼 f : B → Bool, h (canonicalize p f)) =
      𝔼 g : {b // p b} → Bool, h (extend p g) :=
  expect_restrict p (fun g => h (extend p g))

theorem expect_restrict_pair (h : ({b // p b} → Bool) → ({b // p b} → Bool) → ℝ) :
    (𝔼 f : B → Bool, 𝔼 g : B → Bool, h (restrict p f) (restrict p g)) =
      𝔼 f : {b // p b} → Bool, 𝔼 g : {b // p b} → Bool, h f g := by
  calc
    _ = 𝔼 f : B → Bool, 𝔼 g : {b // p b} → Bool, h (restrict p f) g := by
      apply Finset.expect_congr rfl
      intro f _
      exact expect_restrict p (h (restrict p f))
    _ = _ := expect_restrict p (fun f => 𝔼 g : {b // p b} → Bool, h f g)

end IndependentSetsGames.Foundations.PCP.UniformRestriction

end OAI
