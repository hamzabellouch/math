import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

namespace OAI

/-!
# Orientation of surjective Jordan maps

This is the algebraic argument recalled in §5 of *Universal strong
Kadison–Kastler stability* (2026), following I. N. Herstein, *Jordan
homomorphisms*, Trans. Amer. Math. Soc. 81 (1956), 331–341. The target is
assumed prime explicitly; no von Neumann algebra representation is needed
for this algebraic step.
-/

namespace KadisonKastler

variable {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

/-- Preservation of twice the Jordan product. Over the complex numbers
this is equivalent to preservation of `(x * y + y * x) / 2`. -/
def PreservesJordan (θ : A →ₗ[ℂ] B) : Prop :=
  ∀ x y, θ (x * y + y * x) = θ x * θ y + θ y * θ x

/-- The ring-theoretic primeness condition used by the orientation proof. -/
def IsPrimeAlgebra (B : Type*) [Ring B] : Prop :=
  ∀ a b : B, (∀ c : B, a * c * b = 0) → a = 0 ∨ b = 0

private theorem eq_of_add_self_eq_add_self {x y : B} (h : x + x = y + y) : x = y := by
  apply smul_right_injective B (two_ne_zero : (2 : ℂ) ≠ 0)
  simpa only [two_smul] using h

theorem PreservesJordan.map_square {θ : A →ₗ[ℂ] B} (hθ : PreservesJordan θ) (x : A) :
    θ (x * x) = θ x * θ x := by
  apply eq_of_add_self_eq_add_self
  simpa only [map_add] using hθ x x

theorem PreservesJordan.map_triple {θ : A →ₗ[ℂ] B} (hθ : PreservesJordan θ) (x y : A) :
    θ (x * y * x) = θ x * θ y * θ x := by
  apply eq_of_add_self_eq_add_self
  calc
    θ (x * y * x) + θ (x * y * x) = θ (x * y * x + x * y * x) := (map_add θ _ _).symm
    _ = θ ((x * (x * y + y * x) + (x * y + y * x) * x) -
        (x * x * y + y * (x * x))) := by congr 1; noncomm_ring
    _ = θ x * θ (x * y + y * x) + θ (x * y + y * x) * θ x -
        (θ (x * x) * θ y + θ y * θ (x * x)) := by
      rw [map_sub, hθ x (x * y + y * x), hθ (x * x) y]
    _ = θ x * θ y * θ x + θ x * θ y * θ x := by
      rw [hθ x y, hθ.map_square x]
      noncomm_ring

theorem PreservesJordan.map_triple_add_reverse {θ : A →ₗ[ℂ] B}
    (hθ : PreservesJordan θ) (x y z : A) :
    θ (x * y * z + z * y * x) = θ x * θ y * θ z + θ z * θ y * θ x := by
  calc
    θ (x * y * z + z * y * x) =
        θ ((x + z) * y * (x + z) - x * y * x - z * y * z) := by
      congr 1; noncomm_ring
    _ = θ (x + z) * θ y * θ (x + z) - θ x * θ y * θ x - θ z * θ y * θ z := by
      rw [map_sub, map_sub, hθ.map_triple, hθ.map_triple, hθ.map_triple]
    _ = θ x * θ y * θ z + θ z * θ y * θ x := by
      rw [map_add]
      noncomm_ring

/-- The two potential multiplicative defects anticommute through every
element of the target. -/
theorem PreservesJordan.defect_relation {θ : A →ₗ[ℂ] B}
    (hθ : PreservesJordan θ) (hsurj : Function.Surjective θ) (a b : A) (C : B) :
    (θ (a * b) - θ a * θ b) * C * (θ (a * b) - θ b * θ a) +
      (θ (a * b) - θ b * θ a) * C * (θ (a * b) - θ a * θ b) = 0 := by
  obtain ⟨c, rfl⟩ := hsurj C
  have he : θ (b * a) = θ a * θ b + θ b * θ a - θ (a * b) := by
    have h := hθ a b
    rw [map_add] at h
    linear_combination (norm := noncomm_ring) h
  have hfirst := hθ.map_triple_add_reverse (a * b) c (b * a)
  have hsource : a * b * c * (b * a) + b * a * c * (a * b) =
      a * (b * c * b) * a + b * (a * c * a) * b := by noncomm_ring
  rw [hsource, map_add, hθ.map_triple, hθ.map_triple,
    hθ.map_triple, hθ.map_triple, he] at hfirst
  linear_combination (norm := noncomm_ring) hfirst

private theorem prime_or_of_anticommutation (hprime : IsPrimeAlgebra B)
    (h k : B) (hrel : ∀ c, h * c * k + k * c * h = 0) : h = 0 ∨ k = 0 := by
  by_cases hk : k = 0
  · exact Or.inr hk
  left
  apply (hprime h k ?_).resolve_right hk
  intro c₁
  apply (hprime (h * c₁ * k) k ?_).resolve_right hk
  intro c₂
  have hzero : (h * c₁ * k * c₂ * k) + (h * c₁ * k * c₂ * k) = 0 + 0 := by
    linear_combination (norm := noncomm_ring)
      hrel (c₁ * k * c₂) + (hrel c₁) * c₂ * k - k * c₁ * (hrel c₂)
  exact eq_of_add_self_eq_add_self hzero

/-- For each pair of source elements, one of the two orientations holds. -/
theorem PreservesJordan.map_mul_or_map_mul_reverse {θ : A →ₗ[ℂ] B}
    (hθ : PreservesJordan θ) (hsurj : Function.Surjective θ)
    (hprime : IsPrimeAlgebra B) (a b : A) :
    θ (a * b) = θ a * θ b ∨ θ (a * b) = θ b * θ a := by
  simpa only [sub_eq_zero] using prime_or_of_anticommutation hprime
    (θ (a * b) - θ a * θ b) (θ (a * b) - θ b * θ a)
    (hθ.defect_relation hsurj a b)

private theorem additive_zero_cover {X Y : Type*} [AddGroup X] [AddGroup Y]
    (f g : X →+ Y) (hcover : ∀ x, f x = 0 ∨ g x = 0) : f = 0 ∨ g = 0 := by
  classical
  by_cases hf : f = 0
  · exact Or.inl hf
  right
  have hex : ∃ x, f x ≠ 0 := by
    by_contra h
    apply hf
    apply AddMonoidHom.ext
    intro x
    exact Classical.byContradiction (fun hx => h ⟨x, hx⟩)
  obtain ⟨x, hx⟩ := hex
  have hgx : g x = 0 := (hcover x).resolve_left hx
  apply AddMonoidHom.ext
  intro y
  by_cases hgy : g y = 0
  · exact hgy
  have hfy : f y = 0 := (hcover y).resolve_right hgy
  rcases hcover (x + y) with hxy | hxy
  · rw [map_add, hfy, add_zero] at hxy
    exact False.elim (hx hxy)
  · rw [map_add, hgx, zero_add] at hxy
    exact False.elim (hgy hxy)

private def mulDefect (θ : A →ₗ[ℂ] B) : A →+ A →+ B where
  toFun a :=
    { toFun := fun b => θ (a * b) - θ a * θ b
      map_zero' := by simp
      map_add' := by intros b c; simp only [mul_add, map_add]; abel }
  map_zero' := by ext b; simp
  map_add' a c := by
    ext b
    change θ ((a + c) * b) - θ (a + c) * θ b =
      (θ (a * b) - θ a * θ b) + (θ (c * b) - θ c * θ b)
    simp only [add_mul, map_add]
    abel

private def reverseMulDefect (θ : A →ₗ[ℂ] B) : A →+ A →+ B where
  toFun a :=
    { toFun := fun b => θ (a * b) - θ b * θ a
      map_zero' := by simp
      map_add' := by intros b c; simp only [mul_add, add_mul, map_add]; abel }
  map_zero' := by ext b; simp
  map_add' a c := by
    ext b
    change θ ((a + c) * b) - θ b * θ (a + c) =
      (θ (a * b) - θ b * θ a) + (θ (c * b) - θ b * θ c)
    simp only [add_mul, mul_add, map_add]
    abel

/-- Herstein's orientation theorem in the complex prime-target case.
A surjective complex-linear Jordan map is multiplicative or antimultiplicative.
The two applications of `additive_zero_cover` are the two additive-subgroup
union arguments in the manuscript's proof. -/
theorem PreservesJordan.multiplicative_or_antimultiplicative {θ : A →ₗ[ℂ] B}
    (hθ : PreservesJordan θ) (hsurj : Function.Surjective θ)
    (hprime : IsPrimeAlgebra B) :
    (∀ a b, θ (a * b) = θ a * θ b) ∨ (∀ a b, θ (a * b) = θ b * θ a) := by
  have hlocal (a : A) : mulDefect θ a = 0 ∨ reverseMulDefect θ a = 0 := by
    apply additive_zero_cover
    intro b
    simpa only [mulDefect, reverseMulDefect, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      sub_eq_zero] using hθ.map_mul_or_map_mul_reverse hsurj hprime a b
  rcases additive_zero_cover (mulDefect θ) (reverseMulDefect θ) hlocal with h | h
  · left
    intro a b
    have h' := congrArg (fun f : A →+ A →+ B => f a b) h
    exact sub_eq_zero.mp h'
  · right
    intro a b
    have h' := congrArg (fun f : A →+ A →+ B => f a b) h
    exact sub_eq_zero.mp h'

end KadisonKastler

end OAI
