import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalRepresentationFunctor
import Mathlib.RepresentationTheory.Coinvariants

namespace OAI

/-! # Exact rational coinvariants for a finite group

The averaging map descends to coinvariants and is a section of their quotient
map. Its naturality proves preservation of injections directly.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2300] Representation.Coinvariants.instModule
variable {H : Type} [Group H] [Fintype H]
variable {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

def finiteRationalAverage (ρ : Representation ℚ H V) : V →ₗ[ℚ] V :=
  (Fintype.card H : ℚ)⁻¹ • ∑ g : H, ρ g

theorem finiteRationalAverage_apply (ρ : Representation ℚ H V) (x : V) :
    finiteRationalAverage ρ x = (Fintype.card H : ℚ)⁻¹ • ∑ g : H, ρ g x := by
  simp only [finiteRationalAverage, LinearMap.smul_apply, LinearMap.sum_apply]

theorem finiteRationalAverage_action (ρ : Representation ℚ H V) (g : H) (x : V) :
    finiteRationalAverage ρ (ρ g x) = finiteRationalAverage ρ x := by
  simp only [finiteRationalAverage_apply]
  congr 1
  exact Fintype.sum_bijective (· * g) (Group.mulRight_bijective g) _ _
    (fun h => by rw [map_mul]; rfl)

def finiteRationalCoinvariantsSection (ρ : Representation ℚ H V) :
    ρ.Coinvariants →ₗ[ℚ] V :=
  Representation.Coinvariants.lift ρ (finiteRationalAverage ρ)
    (fun g => LinearMap.ext (finiteRationalAverage_action ρ g))

theorem finiteRationalAverage_mk (ρ : Representation ℚ H V) (x : V) :
    Representation.Coinvariants.mk ρ (finiteRationalAverage ρ x) =
      Representation.Coinvariants.mk ρ x := by
  rw [finiteRationalAverage_apply, map_smul, map_sum]
  simp only [Representation.Coinvariants.mk_self_apply, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

theorem finiteRationalAverage_natural (ρ : Representation ℚ H V)
    (σ : Representation ℚ H W) (f : Representation.IntertwiningMap ρ σ) (x : V) :
    f (finiteRationalAverage ρ x) = finiteRationalAverage σ (f x) := by
  simp only [finiteRationalAverage_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact congrArg (fun u : V →ₗ[ℚ] W => u x) (f.isIntertwining' g)

theorem finiteRationalCoinvariants_map_injective (ρ : Representation ℚ H V)
    (σ : Representation ℚ H W) (f : Representation.IntertwiningMap ρ σ)
    (hf : Function.Injective f) :
    Function.Injective (Representation.Coinvariants.map ρ σ f) := by
  intro x y hxy
  induction x using Representation.Coinvariants.induction_on with
  | h x =>
    induction y using Representation.Coinvariants.induction_on with
    | h y =>
      have he := congrArg (finiteRationalCoinvariantsSection σ) hxy
      change finiteRationalAverage σ (f x) = finiteRationalAverage σ (f y) at he
      rw [← finiteRationalAverage_natural ρ σ f, ← finiteRationalAverage_natural ρ σ f] at he
      calc
        Representation.Coinvariants.mk ρ x =
          Representation.Coinvariants.mk ρ (finiteRationalAverage ρ x) :=
            (finiteRationalAverage_mk ρ x).symm
        _ = Representation.Coinvariants.mk ρ (finiteRationalAverage ρ y) :=
          congrArg (Representation.Coinvariants.mk ρ) (hf he)
        _ = Representation.Coinvariants.mk ρ y := finiteRationalAverage_mk ρ y

end PolycyclicRecognition

end

end OAI
