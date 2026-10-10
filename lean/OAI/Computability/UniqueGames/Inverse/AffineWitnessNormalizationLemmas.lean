import Mathlib.Data.Fintype.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OAI.Computability.UniqueGames.Inverse.AffineWitnessLemmas

namespace OAI

section

/-!
The finite orbit count completing the first-bit witness normalization.
The assumption in `normalize_of_good_count` is precisely that agreement is
strictly greater than the reciprocal of the row-kernel cardinality, expressed
without division. It is a quantitative goodness hypothesis, not an inverse
theorem or a nonlinear rank premise.
-/

namespace UniqueGamesTheorem.Inverse.AffineWitness

variable {D C R : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

/-- The actual simultaneous row/column slice, including its affine offsets. -/
abbrev Slice (A : C →ₗ[F2] R) (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) :=
  {M : D →ₗ[F2] C // InSlice A Z M₀ M}

def sliceShift (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (h : A.ker) (M : Slice A Z M₀) :
    Slice A Z M₀ :=
  ⟨shift e h M, shift_preserves_slice e A Z M₀ M heZ h M.property⟩

theorem sliceShift_zero (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (M : Slice A Z M₀) :
    sliceShift e A Z M₀ heZ 0 M = M := by
  apply Subtype.ext
  exact shift_zero e M.val

theorem sliceShift_add (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C)
    (heZ : ∀ w ∈ Z, e w = 0) (h k : A.ker) (M : Slice A Z M₀) :
    sliceShift e A Z M₀ heZ (h + k) M =
      sliceShift e A Z M₀ heZ h (sliceShift e A Z M₀ heZ k M) := by
  apply Subtype.ext
  exact shift_add e (h : C) (k : C) M.val

/-- If the affine coset misses first bit one, folding limits agreement to one
point per row-kernel orbit. No rank-level inequality is used. -/
theorem agreement_count_le [Finite D] [Finite C]
    (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (F : (D →ₗ[F2] C) → C)
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (hno : ¬ ∃ w ∈ Z, e (z + w) = 1) :
    Nat.card A.ker * Nat.card {M : Slice A Z M₀ // F M = M.val z + u} ≤
      Nat.card (Slice A Z M₀) := by
  classical
  let : Fintype D := Fintype.ofFinite D
  let : Fintype C := Fintype.ofFinite C
  let : Fintype (D →ₗ[F2] C) := Fintype.ofInjective DFunLike.coe DFunLike.coe_injective
  obtain ⟨hz, heZ⟩ := no_affine_representative e Z z hno
  have hcount := folded_action_card_mul_agreement_le
    (sliceShift e A Z M₀ heZ)
    (sliceShift_zero e A Z M₀ heZ)
    (sliceShift_add e A Z M₀ heZ)
    (fun h : A.ker => (h : C)) Subtype.val_injective
    (fun M : Slice A Z M₀ => F M)
    (fun M : Slice A Z M₀ => M.val z + u)
    (fun h M => hfold h M)
    (fun h M => shift_preserves_target e z hz u h M)
  simpa only [Nat.card_eq_fintype_card] using hcount

/-- A good affine witness has a first-bit-one representative with an adjusted
intercept, agreeing with the original target on every matrix of its slice. -/
theorem normalize_of_good_count [Finite D] [Finite C]
    (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (F : (D →ₗ[F2] C) → C)
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (hgood : Nat.card (Slice A Z M₀) <
      Nat.card A.ker * Nat.card {M : Slice A Z M₀ // F M = M.val z + u}) :
    ∃ z' : D, ∃ u' : C, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  apply normalize e A Z M₀ z u
  by_contra hno
  exact (not_lt_of_ge (agreement_count_le e A Z M₀ z u F hfold hno)) hgood

end UniqueGamesTheorem.Inverse.AffineWitness

end

section

/-! The probability form of first-bit witness normalization. -/

namespace UniqueGamesTheorem.Inverse.AffineWitness

variable {D C R : Type*}
  [AddCommGroup D] [Module F2 D]
  [AddCommGroup C] [Module F2 C]
  [AddCommGroup R] [Module F2 R]

/-- An agreement lower bound above the inverse row-kernel size produces a
first-bit-one representative while preserving the entire affine target. -/
theorem normalize_of_density [Finite D] [Finite C]
    (e : D →ₗ[F2] F2) (A : C →ₗ[F2] R)
    (Z : Submodule F2 D) (M₀ : D →ₗ[F2] C) (z : D) (u : C)
    (F : (D →ₗ[F2] C) → C)
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (η : ℝ)
    (hgood : η ≤
      (Nat.card {M : Slice A Z M₀ // F M = M.val z + u} : ℝ) /
        (Nat.card (Slice A Z M₀) : ℝ))
    (hsize : 1 < η * (Nat.card A.ker : ℝ)) :
    ∃ z' : D, ∃ u' : C, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  classical
  let : Fintype D := Fintype.ofFinite D
  let : Fintype C := Fintype.ofFinite C
  let : Fintype (D →ₗ[F2] C) := Fintype.ofInjective DFunLike.coe DFunLike.coe_injective
  let : Nonempty (Slice A Z M₀) := ⟨⟨M₀, rfl, fun _ _ => rfl⟩⟩
  have hpos : (0 : ℝ) < (Nat.card (Slice A Z M₀) : ℝ) := by
    exact_mod_cast Nat.card_pos (α := Slice A Z M₀)
  have hmass := (le_div_iff₀ hpos).mp hgood
  have hmul := mul_le_mul_of_nonneg_right hmass
    (Nat.cast_nonneg (α := ℝ) (Nat.card A.ker))
  have hstrict := mul_lt_mul_of_pos_right hsize hpos
  apply normalize_of_good_count e A Z M₀ z u F hfold
  have hreal : (Nat.card (Slice A Z M₀) : ℝ) <
      (Nat.card A.ker : ℝ) *
        (Nat.card {M : Slice A Z M₀ // F M = M.val z + u} : ℝ) := by
    nlinarith only [hmul, hstrict]
  exact_mod_cast hreal

end UniqueGamesTheorem.Inverse.AffineWitness

end

section

namespace UniqueGamesTheorem.Inverse.AffineWitness

theorem first_bit_witness {m ℓ r : ℕ}
    (e : (Fin m → F2) →ₗ[F2] F2)
    (A : (Fin ℓ → F2) →ₗ[F2] (Fin r → F2))
    (Z : Submodule F2 (Fin m → F2))
    (M₀ : (Fin m → F2) →ₗ[F2] (Fin ℓ → F2))
    (z : Fin m → F2) (u : Fin ℓ → F2)
    (F : ((Fin m → F2) →ₗ[F2] (Fin ℓ → F2)) → (Fin ℓ → F2))
    (hfold : ∀ (h : A.ker) M, F (shift e h M) = F M + h)
    (α : ℝ) (hα : 0 < α)
    (hgood : α / 2 ≤
      (Nat.card {M : Slice A Z M₀ // F M = M.val z + u} : ℝ) /
        (Nat.card (Slice A Z M₀) : ℝ))
    (hsmall : 1 / (2 : ℝ) ^ (ℓ - r) < α / 8) :
    ∃ z' : Fin m → F2, ∃ u' : Fin ℓ → F2, e z' = 1 ∧
      ∀ M, InSlice A Z M₀ M → M z' + u' = M z + u := by
  have hpow : (0 : ℝ) < 2 ^ (ℓ - r) := pow_pos (by norm_num) _
  have hsep := (div_lt_iff₀ hpow).mp hsmall
  have hk : (2 : ℝ) ^ (ℓ - r) ≤ (Nat.card A.ker : ℝ) := by
    exact_mod_cast binary_kernel_card_lower A
  have hscale := mul_le_mul_of_nonneg_left hk hα.le
  have hsize : 1 < (α / 2) * (Nat.card A.ker : ℝ) := by
    nlinarith only [hsep, hscale]
  exact normalize_of_density e A Z M₀ z u F hfold (α / 2) hgood hsize

end UniqueGamesTheorem.Inverse.AffineWitness

end

end OAI
