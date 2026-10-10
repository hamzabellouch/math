import Mathlib

namespace OAI

                                                                                           

namespace UniqueGames.Foundations.PCP.UniformRestriction

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

end UniqueGames.Foundations.PCP.UniformRestriction

end OAI
