import OAI.Analysis.OInfinity.JointRohlinWitness

namespace OAI

/-! # The actual unitary cocycle of an incomplete Cuntz row

The unitary-group endomorphism is `u ↦ 1 - φ(1) + φ(u)`. This retains the
defect projection of the canonical finite row. Its connected cocycles satisfy
the exact generator recursion and an exact terminal-support formula; the
terminal projection is not assigned a small norm.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma bergCornerLift_one (φ : E →⋆ₙₐ[ℂ] E) : bergCornerLift φ 1 = 1 := by
  unfold bergCornerLift
  abel

lemma bergCornerLift_mul (φ : E →⋆ₙₐ[ℂ] E) (x y : E) :
    bergCornerLift φ (x * y) = bergCornerLift φ x * bergCornerLift φ y := by
  let p := 1 - φ 1
  have h11 : φ 1 * φ 1 = φ 1 := by rw [← map_mul, one_mul]
  have hp : p * p = p := by
    calc
      _ = 1 - φ 1 - φ 1 + φ 1 * φ 1 := by dsimp [p]; noncomm_ring
      _ = _ := by rw [h11]; dsimp [p]; abel
  have hpy : p * φ y = 0 := by dsimp [p]; rw [sub_mul, one_mul, ← map_mul, one_mul, sub_self]
  have hxp : φ x * p = 0 := by dsimp [p]; rw [mul_sub, mul_one, ← map_mul, mul_one, sub_self]
  change p + φ (x * y) = (p + φ x) * (p + φ y)
  rw [add_mul, mul_add, mul_add, hp, hpy, hxp, zero_add, add_zero, map_mul]

lemma bergCornerLift_star (φ : E →⋆ₙₐ[ℂ] E) (x : E) :
    bergCornerLift φ (star x) = star (bergCornerLift φ x) := by
  simp only [bergCornerLift, star_add, star_sub, star_one, ← map_star]

def incompleteUnitaryShift (φ : E →⋆ₙₐ[ℂ] E) : unitary E →* unitary E where
  toFun u := ⟨bergCornerLift φ (u : E), by
    constructor
    · rw [← bergCornerLift_star, ← bergCornerLift_mul, u.property.1, bergCornerLift_one]
    · rw [← bergCornerLift_star, ← bergCornerLift_mul, u.property.2, bergCornerLift_one]⟩
  map_one' := Subtype.ext (bergCornerLift_one φ)
  map_mul' u v := Subtype.ext (bergCornerLift_mul φ u v)

@[simp] lemma incompleteUnitaryShift_coe (φ : E →⋆ₙₐ[ℂ] E) (u : unitary E) :
    (incompleteUnitaryShift φ u : E) = bergCornerLift φ u := rfl

lemma incompleteUnitaryShift_continuous (φ : E →⋆ₙₐ[ℂ] E) :
    Continuous (incompleteUnitaryShift φ) := by
  apply Continuous.subtype_mk
  change Continuous (fun u : unitary E => 1 - φ 1 + φ (u : E))
  exact continuous_const.add ((map_continuous φ).comp continuous_subtype_val)

lemma bergCornerIterHom_one_eq_tail (φ : E →⋆ₙₐ[ℂ] E) (n : ℕ) :
    bergCornerIterHom φ n 1 = bergTowerTail φ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bergCornerIterHom_succ, bergTowerTail_succ, ih]

lemma incompleteUnitaryShift_iterate_coe (φ : E →⋆ₙₐ[ℂ] E) (u : unitary E) (n : ℕ) :
    ((incompleteUnitaryShift φ)^[n] u : E) = bergCornerLift (bergCornerIterHom φ n) u := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, bergCornerLift, bergCornerIterHom_zero]; abel
  | succ n ih =>
      rw [Function.iterate_succ_apply', incompleteUnitaryShift_coe, ih]
      simp only [bergCornerLift, map_add, map_sub, bergCornerIterHom_succ]
      abel

lemma incompleteUnitaryShift_iterate_deviation (φ : E →⋆ₙₐ[ℂ] E)
    (u : unitary E) (n : ℕ) :
    (((incompleteUnitaryShift φ)^[n] u : E) - 1) * bergTowerTail φ n =
      ((incompleteUnitaryShift φ)^[n] u : E) - 1 := by
  rw [incompleteUnitaryShift_iterate_coe, ← bergCornerIterHom_one_eq_tail]
  let ψ := bergCornerIterHom φ n
  change (bergCornerLift ψ u - 1) * ψ 1 = bergCornerLift ψ u - 1
  have he : bergCornerLift ψ u - 1 = ψ u - ψ 1 := by unfold bergCornerLift; abel
  rw [he, sub_mul, ← map_mul, ← map_mul, mul_one, one_mul]

lemma finiteGroupCocycle_succ_right (α : unitary E →* unitary E) (u : unitary E) (n : ℕ) :
    finiteGroupCocycle (G := unitary E) α u (n + 1) = finiteGroupCocycle (G := unitary E) α u n * α^[n] u := by
  induction n with
  | zero => simp [finiteGroupCocycle]
  | succ n ih =>
      change u * α (finiteGroupCocycle (G := unitary E) α u (n + 1)) =
        (u * α (finiteGroupCocycle (G := unitary E) α u n)) * α^[n + 1] u
      rw [ih, map_mul, Function.iterate_succ_apply']
      group

lemma incompleteCocycle_difference_tail (φ : E →⋆ₙₐ[ℂ] E) (u : unitary E) (n : ℕ) :
    ((finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u n : E) -
      (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + 1) : E)) * bergTowerTail φ n =
        (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u n : E) -
          (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u (n + 1) : E) := by
  rw [finiteGroupCocycle_succ_right]
  let v := finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u n
  let w := (incompleteUnitaryShift φ)^[n] u
  change ((v : E) - (v : E) * (w : E)) * bergTowerTail φ n = (v : E) - (v : E) * (w : E)
  have he : (v : E) - (v : E) * (w : E) = -(v : E) * ((w : E) - 1) := by noncomm_ring
  rw [he, mul_assoc, incompleteUnitaryShift_iterate_deviation]

lemma finiteGroupCocycle_one (α : unitary E →* unitary E) (n : ℕ) :
    finiteGroupCocycle (G := unitary E) α 1 n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finiteGroupCocycle, ih, map_one, one_mul]

lemma finiteGroupCocycle_continuous (α : unitary E →* unitary E)
    (hα : Continuous α) (n : ℕ) : Continuous (fun u => finiteGroupCocycle (G := unitary E) α u n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact continuous_id.mul (hα.comp ih)

lemma incompleteCocycle_joined (φ : E →⋆ₙₐ[ℂ] E) (u : unitary E)
    (hu : Joined (1 : unitary E) u) (n : ℕ) :
    Joined (1 : unitary E) (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) u n) := by
  obtain ⟨p⟩ := hu
  refine ⟨{
    toFun := fun t => finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift φ) (p t) n
    continuous_toFun := (finiteGroupCocycle_continuous _ (incompleteUnitaryShift_continuous φ) n).comp p.continuous
    source' := by rw [p.source, finiteGroupCocycle_one]
    target' := by rw [p.target] }⟩

section Row
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (s t : I → E) (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)

lemma incompleteCocycle_generator (u : unitary E)
    (hu : ∀ i, (u : E) * s i = t i) (n : ℕ) (i : I) :
    (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift (finiteCuntzDiagonalHom s hs)) u (n + 1) : E) * s i =
      t i * (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift (finiteCuntzDiagonalHom s hs)) u n : E) := by
  change ((u : E) * bergCornerLift (finiteCuntzDiagonalHom s hs)
    (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift (finiteCuntzDiagonalHom s hs)) u n)) * s i = _
  rw [mul_assoc, bergCornerLift_mul_generator s hs, ← mul_assoc, hu]

lemma incompleteCocycle_generator_error (u : unitary E)
    (hu : ∀ i, (u : E) * s i = t i) (n : ℕ) (i : I) :
    (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift (finiteCuntzDiagonalHom s hs)) u (n + 1) : E) * s i -
      t i * (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift (finiteCuntzDiagonalHom s hs)) u (n + 1) : E) =
    t i * ((finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift (finiteCuntzDiagonalHom s hs)) u n : E) -
      (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift (finiteCuntzDiagonalHom s hs)) u (n + 1) : E)) := by
  rw [incompleteCocycle_generator s t hs u hu, mul_sub]

lemma incompleteCocycle_generator_error_tail (u : unitary E)
    (hu : ∀ i, (u : E) * s i = t i) (n : ℕ) (i : I) :
    ((finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift (finiteCuntzDiagonalHom s hs)) u (n + 1) : E) * s i -
      t i * (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift (finiteCuntzDiagonalHom s hs)) u (n + 1) : E)) *
        bergTowerTail (finiteCuntzDiagonalHom s hs) n =
      (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift (finiteCuntzDiagonalHom s hs)) u (n + 1) : E) * s i -
        t i * (finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift (finiteCuntzDiagonalHom s hs)) u (n + 1) : E) := by
  rw [incompleteCocycle_generator_error s t hs u hu, mul_assoc, incompleteCocycle_difference_tail]

end Row

def canonicalRowCorner (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (N : ℕ) : E →⋆ₙₐ[ℂ] E :=
  finiteCuntzDiagonalHom (fun i : Fin N => s i)
    (fun i j => by simpa only [Fin.ext_iff] using hs i j)

def canonicalIncompleteCocycle (s : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (N : ℕ) (u : unitary E) : ℕ → unitary E :=
  finiteGroupCocycle (G := unitary E) (incompleteUnitaryShift (canonicalRowCorner s hs N)) u

/-- The canonical finite rows have an actual connected unitary cocycle with
the exact tail-supported generator defect. This is not yet a small-error
half-flip: the displayed difference on the terminal tail remains to be
cancelled by the two-family construction. -/
lemma exists_connected_canonicalIncompleteCocycle [Nontrivial E] (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hc : ∀ i j, Commute (star (t i)) (s j)) (N : ℕ) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (∀ n, Joined (1 : unitary E) (canonicalIncompleteCocycle s hs N u n)) ∧
      (∀ n i, i < N →
        (canonicalIncompleteCocycle s hs N u (n + 1) : E) * s i =
          t i * (canonicalIncompleteCocycle s hs N u n : E)) ∧
      (∀ n i, i < N →
        ((canonicalIncompleteCocycle s hs N u (n + 1) : E) * s i -
          t i * (canonicalIncompleteCocycle s hs N u (n + 1) : E)) *
            bergTowerTail (canonicalRowCorner s hs N) n =
        (canonicalIncompleteCocycle s hs N u (n + 1) : E) * s i -
          t i * (canonicalIncompleteCocycle s hs N u (n + 1) : E)) := by
  obtain ⟨u, hu, hstep⟩ := exists_connected_infinite_transfer_step s t hs ht hc N 1
  have hus (i : Fin N) : (u : E) * s i = t i := by simpa only [OneMemClass.coe_one, mul_one] using hstep i i.isLt
  refine ⟨u, hu, fun n => incompleteCocycle_joined _ u hu n, ?_, ?_⟩
  · intro n i hi
    exact incompleteCocycle_generator (fun j : Fin N => s j) (fun j : Fin N => t j)
      (fun j k => by simpa only [Fin.ext_iff] using hs j k) u hus n ⟨i, hi⟩
  · intro n i hi
    exact incompleteCocycle_generator_error_tail (fun j : Fin N => s j) (fun j : Fin N => t j)
      (fun j k => by simpa only [Fin.ext_iff] using hs j k) u hus n ⟨i, hi⟩

end WeakPureInfiniteness

end

end OAI
