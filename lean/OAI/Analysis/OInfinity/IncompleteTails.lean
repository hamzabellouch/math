import OAI.Analysis.OInfinity.IncompleteCocycle

namespace OAI

/-! # Two-sided terminal corners of the incomplete-row cocycle

The actual cocycle transports every completed source layer to its target
layer. Its remaining generator error lies from the source terminal corner
to the next target terminal corner. Neither corner is discarded in norm.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma bergCornerLift_mul_image (φ : E →⋆ₙₐ[ℂ] E) (a x : E) :
    bergCornerLift φ a * φ x = φ (a * x) := by
  simp only [bergCornerLift, add_mul, sub_mul, one_mul, ← map_mul, one_mul,
    sub_self, zero_add]

lemma bergCornerLift_image_mul_star (φ : E →⋆ₙₐ[ℂ] E) (x a : E) :
    φ x * star (bergCornerLift φ a) = φ (x * star a) := by
  rw [← bergCornerLift_star]
  simp only [bergCornerLift, mul_add, mul_sub, mul_one, ← map_mul, mul_one,
    sub_self, zero_add]

lemma bergCornerLift_sandwich_image (φ : E →⋆ₙₐ[ℂ] E) (a x : E) :
    bergCornerLift φ a * φ x * star (bergCornerLift φ a) =
      φ (a * x * star a) := by
  rw [bergCornerLift_mul_image, bergCornerLift_image_mul_star]

section Conjugacy

variable (φ ψ : E →⋆ₙₐ[ℂ] E) (u : unitary E)
variable (hu : ∀ x, (u : E) * φ x * star (u : E) = ψ x)

include hu in
/-- The outer `k` steps transport a whole iterated corner, retaining the
initial `n`-step cocycle inside that corner. -/
lemma incompleteCocycle_conjugate_iterate (n k : ℕ) (x : E) :
    (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + k) : E) *
      bergCornerIterHom φ k x *
        star (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + k) : E) =
    bergCornerIterHom ψ k
      ((finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u n : E) * x *
        star (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u n : E)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Nat.add_succ]
      change ((u : E) * bergCornerLift φ
          (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + k))) *
          φ (bergCornerIterHom φ k x) *
          star ((u : E) * bergCornerLift φ
            (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + k))) = _
      rw [star_mul]
      calc
        _ = (u : E) *
            (bergCornerLift φ
                (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + k)) *
              φ (bergCornerIterHom φ k x) *
              star (bergCornerLift φ
                (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + k)))) *
            star (u : E) := by noncomm_ring
        _ = (u : E) * φ _ * star (u : E) := by rw [bergCornerLift_sandwich_image]
        _ = ψ _ := hu _
        _ = _ := by rw [ih]; rfl

include hu in
lemma incompleteCocycle_tail_conjugate (n k : ℕ) :
    (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + k) : E) *
      bergTowerTail φ k *
        star (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + k) : E) =
      bergTowerTail ψ k := by
  have h := incompleteCocycle_conjugate_iterate φ ψ u hu n k 1
  simpa only [bergCornerIterHom_one_eq_tail, mul_one, Unitary.mul_star_self_of_mem
    (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u n).property] using h

include hu in
lemma incompleteCocycle_tail_transport (n k : ℕ) :
    (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + k) : E) *
      bergTowerTail φ k = bergTowerTail ψ k *
        (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + k) : E) := by
  have h := congrArg (fun z : E => z *
    (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + k) : E))
      (incompleteCocycle_tail_conjugate φ ψ u hu n k)
  simpa only [mul_assoc, Unitary.coe_star_mul_self, mul_one] using h

include hu in
lemma incompleteCocycle_layer_transport (n k : ℕ) :
    (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + k + 1) : E) *
      bergTowerLayer φ k = bergTowerLayer ψ k *
        (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + k + 1) : E) := by
  have h₀ := incompleteCocycle_tail_transport φ ψ u hu (n + 1) k
  have h₁ := incompleteCocycle_tail_transport φ ψ u hu n (k + 1)
  have he : n + 1 + k = n + k + 1 := by omega
  rw [he] at h₀
  simpa only [bergTowerLayer, mul_sub, sub_mul, Nat.add_succ] using congrArg₂
    (fun a b : E => a - b) h₀ h₁

include hu in
/-- The successive cocycle difference is a rectangular operator from the
source terminal projection to the target terminal projection. -/
lemma incompleteCocycle_difference_both_tails (n : ℕ) :
    bergTowerTail ψ n *
      ((finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u n : E) -
        (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + 1) : E)) *
      bergTowerTail φ n =
      (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u n : E) -
        (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + 1) : E) := by
  have h₀ := incompleteCocycle_tail_transport φ ψ u hu 0 n
  have h₁ := incompleteCocycle_tail_transport φ ψ u hu 1 n
  simp only [zero_add, show 1 + n = n + 1 by omega] at h₀ h₁
  have hr := incompleteCocycle_difference_tail φ u n
  calc
    _ = (((finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u n : E) -
          (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + 1) : E)) *
          bergTowerTail φ n) * bergTowerTail φ n := by rw [mul_sub, ← h₀, ← h₁]; noncomm_ring
    _ = _ := by rw [hr, hr]

end Conjugacy

section Row

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (s t : I → E)
variable (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
variable (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
variable (u : unitary E) (hu : ∀ i, (u : E) * s i = t i)

include hu in
lemma incompleteRow_conjugate_corner (x : E) :
    (u : E) * finiteCuntzDiagonalHom s hs x * star (u : E) =
      finiteCuntzDiagonalHom t ht x := by
  have hstar (i : I) : star (s i) * star (u : E) = star (t i) := by
    simpa only [star_mul] using congrArg star (hu i)
  change (u : E) * (∑ i, s i * x * star (s i)) * star (u : E) = _
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ((u : E) * s i) * x * (star (s i) * star (u : E)) := by noncomm_ring
    _ = _ := by rw [hu, hstar]

include hu in
lemma incompleteRow_difference_target_tail (n : ℕ) :
    bergTowerTail (finiteCuntzDiagonalHom t ht) n *
      ((finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift
          (finiteCuntzDiagonalHom s hs)) u n : E) -
        (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift
          (finiteCuntzDiagonalHom s hs)) u (n + 1) : E)) =
      (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift
          (finiteCuntzDiagonalHom s hs)) u n : E) -
        (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift
          (finiteCuntzDiagonalHom s hs)) u (n + 1) : E) := by
  have h := incompleteCocycle_difference_both_tails (finiteCuntzDiagonalHom s hs)
    (finiteCuntzDiagonalHom t ht) u (incompleteRow_conjugate_corner s t hs ht u hu) n
  rw [mul_assoc, incompleteCocycle_difference_tail] at h
  exact h

include hu in
/-- The precise two-family boundary: source depth `n`, target depth `n+1`. -/
lemma incompleteRow_generator_error_both_tails (n : ℕ) (i : I) :
    bergTowerTail (finiteCuntzDiagonalHom t ht) (n + 1) *
      ((finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift
          (finiteCuntzDiagonalHom s hs)) u (n + 1) : E) * s i -
        t i * (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift
          (finiteCuntzDiagonalHom s hs)) u (n + 1) : E)) *
      bergTowerTail (finiteCuntzDiagonalHom s hs) n =
      (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift
          (finiteCuntzDiagonalHom s hs)) u (n + 1) : E) * s i -
        t i * (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift
          (finiteCuntzDiagonalHom s hs)) u (n + 1) : E) := by
  rw [incompleteCocycle_generator_error s t hs u hu, ← mul_assoc,
    bergTowerTail_succ_mul_generator t ht]
  simp only [mul_assoc]
  rw [incompleteCocycle_difference_tail,
    incompleteRow_difference_target_tail s t hs ht u hu]

end Row

end WeakPureInfiniteness

end

end OAI
