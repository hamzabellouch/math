import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # Extending polynomial identities from integral coordinates

This is the identity principle used to extend maps of nilpotent lattices to
their real polynomial coordinate groups.
-/

noncomputable section
namespace PolycyclicRecognition

theorem mvPolynomial_eq_of_integer_grid {I : Type*} (p q : MvPolynomial I ℝ)
    (h : ∀ z : I → ℤ, MvPolynomial.eval (fun i => (z i : ℝ)) p =
      MvPolynomial.eval (fun i => (z i : ℝ)) q) : p = q := by
  apply MvPolynomial.funext_set (fun _ => Set.range (Int.cast : ℤ → ℝ))
  · intro _
    exact Set.infinite_range_of_injective Int.cast_injective
  · intro x hx
    choose z hz using fun i => hx i (Set.mem_univ i)
    have he : (fun i => (z i : ℝ)) = x := funext hz
    simpa only [he] using h z

def IsCoordinatePolynomial {I J : Type*} (f : (I → ℝ) → (J → ℝ)) : Prop :=
  ∃ p : J → MvPolynomial I ℝ, ∀ x j, MvPolynomial.eval x (p j) = f x j

namespace IsCoordinatePolynomial
variable {I J K : Type*}

theorem reindex (r : J → I) : IsCoordinatePolynomial (fun x : I → ℝ => x ∘ r) := by
  refine ⟨fun j => MvPolynomial.X (r j), ?_⟩
  intro x j
  exact MvPolynomial.eval_X _

theorem comp {f : (I → ℝ) → (J → ℝ)} {g : (J → ℝ) → (K → ℝ)}
    (hg : IsCoordinatePolynomial g) (hf : IsCoordinatePolynomial f) :
    IsCoordinatePolynomial (g ∘ f) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨fun k => MvPolynomial.bind₁ p (q k), ?_⟩
  intro x k
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) x (MvPolynomial.bind₁ p (q k)) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  have he : (fun i => MvPolynomial.eval₂Hom (RingHom.id ℝ) x (p i)) = f x := funext (hp x)
  rw [he]
  exact hq (f x) k

theorem pair {f : (I → ℝ) → (J → ℝ)} {g : (I → ℝ) → (K → ℝ)}
    (hf : IsCoordinatePolynomial f) (hg : IsCoordinatePolynomial g) :
    IsCoordinatePolynomial (fun x => Sum.elim (f x) (g x)) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨Sum.elim p q, ?_⟩
  intro x j
  cases j with
  | inl j => exact hp x j
  | inr k => exact hq x k

theorem ext_integer_grid {f g : (I → ℝ) → (J → ℝ)}
    (hf : IsCoordinatePolynomial f) (hg : IsCoordinatePolynomial g)
    (h : ∀ z : I → ℤ, f (fun i => (z i : ℝ)) = g (fun i => (z i : ℝ))) : f = g := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  have he : ∀ j, p j = q j := by
    intro j
    apply mvPolynomial_eq_of_integer_grid
    intro z
    rw [hp, hq, h z]
  funext x j
  rw [← hp, ← hq, he]

theorem ext_nat_grid {f g : (I → ℝ) → (J → ℝ)}
    (hf : IsCoordinatePolynomial f) (hg : IsCoordinatePolynomial g)
    (h : ∀ z : I → ℕ, f (fun i => (z i : ℝ)) = g (fun i => (z i : ℝ))) : f = g := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  have he : ∀ j, p j = q j := by
    intro j
    apply MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → ℝ))
    · intro _
      exact Set.infinite_range_of_injective Nat.cast_injective
    · intro x hx
      choose z hz using fun i => hx i (Set.mem_univ i)
      have hx' : (fun i => (z i : ℝ)) = x := funext hz
      rw [hp, hq, ← hx', h z]
  funext x j
  rw [← hp, ← hq, he]

end IsCoordinatePolynomial

end PolycyclicRecognition

end

end OAI
