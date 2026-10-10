import OAI.GroupTheory.PolycyclicRecognition.Geometry.HeightHomomorphism
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TransferredAction

namespace OAI

/-! # A height homomorphism from the transferred translation action

Coarse maps and a Lipschitz height map define a height quasi-action. An affine
height bound permits invariant-mean correction to a genuine homomorphism.
-/

noncomputable section

namespace PolycyclicRecognition
namespace TransferredHeight

open ThompsonNonamenability

universe u v w

variable {H : Type u} [Group H] [PseudoMetricSpace H]
variable {X : Type v} [PseudoMetricSpace X]
variable {W : Type w} [NormedAddCommGroup W]

/-- The Lipschitz height map turns the metric action defect into a uniform
height defect with the stated constant. -/
theorem composition_close (f : H → X) (r : X → H) (π : X → W)
    (hleft : ∀ h a b : H, dist (h * a) (h * b) = dist a b)
    (L K C E : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hπ : ∀ x y, ‖π x - π y‖ ≤ L * dist x y)
    (hf : ∀ a b, dist (f a) (f b) ≤ K * dist a b + C)
    (hrf : ∀ a, dist (r (f a)) a ≤ E) (h k : H) (x : X) :
    ‖π (transferredMap f r h (transferredMap f r k x)) -
      π (transferredMap f r (h * k) x)‖ ≤ L * (K * E + C) := by
  exact (hπ _ _).trans
    (mul_le_mul_of_nonneg_left
      (transferredMap_mul_close f r hleft K C E hK hf hrf h k x) hL)

variable [NormedSpace ℝ W]

/-- The concrete quasi-action induced by `f ∘ L_h ∘ r`, with shifts `π (f h)`.
Surjectivity belongs to the height map; no exact action law is assumed. -/
def quasiAction (f : H → X) (r : X → H) (π : X → W)
    (A : H → W ≃L[ℝ] W) (hπsurj : Function.Surjective π)
    (hleft : ∀ h a b : H, dist (h * a) (h * b) = dist a b)
    (L K C E B : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hπ : ∀ x y, ‖π x - π y‖ ≤ L * dist x y)
    (hf : ∀ a b, dist (f a) (f b) ≤ K * dist a b + C)
    (hrf : ∀ a, dist (r (f a)) a ≤ E)
    (haffine : ∀ h x, ‖π (transferredMap f r h x) - (π (f h) + A h (π x))‖ ≤ B) :
    HeightQuasiAction H X W where
  height := π
  height_surjective := hπsurj
  maps := transferredMap f r
  shift := fun h => π (f h)
  linear := A
  error := B
  error_nonneg := hB
  affine_error := haffine
  composition_error := L * (K * E + C)
  composition_nonneg := mul_nonneg hL (add_nonneg (mul_nonneg hK hE) hC)
  composition_close := composition_close f r π hleft L K C E hL hK hπ hf hrf

/-- Amenability and finitely many affine linear parts produce a normal subgroup
of finite index and a genuine height homomorphism. Its kernel has uniformly
bounded original height. The geometric affine estimate is still a hypothesis. -/
theorem exists_normal_finiteIndex_height [FiniteDimensional ℝ W]
    (f : H → X) (r : X → H) (π : X → W)
    (A : H → W ≃L[ℝ] W) (hπsurj : Function.Surjective π)
    (hleft : ∀ h a b : H, dist (h * a) (h * b) = dist a b)
    (L K C E B : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hπ : ∀ x y, ‖π x - π y‖ ≤ L * dist x y)
    (hf : ∀ a b, dist (f a) (f b) ≤ K * dist a b + C)
    (hrf : ∀ a, dist (r (f a)) a ≤ E)
    (haffine : ∀ h x, ‖π (transferredMap f r h x) - (π (f h) + A h (π x))‖ ≤ B)
    (M : InvariantMean H) (hfinite : Set.Finite (Set.range A)) :
    ∃ (H₀ : Subgroup H), H₀.Normal ∧ H₀.FiniteIndex ∧
      ∃ (τ : H₀ →* Multiplicative W) (D : ℝ), 0 ≤ D ∧
        (∀ h : H₀, ‖(τ h).toAdd - π (f h)‖ ≤ D) ∧
        (∀ h : τ.ker, ‖π (f (h : H₀))‖ ≤ D) := by
  let Q := quasiAction f r π A hπsurj hleft L K C E B hL hK hC hE hB hπ hf hrf haffine
  exact Q.exists_normal_finiteIndex_height M hfinite

end TransferredHeight
end PolycyclicRecognition

end

end OAI
