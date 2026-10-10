import OAI.Algebra.Finitistic.Bar.Weight

namespace OAI
open scoped TensorProduct
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u
variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- Count-r submodule of the two-sided bar term, with the leading D coefficient uncounted. -/
def twoSidedWeight (n r : ℕ) : Submodule D (D ⊗[k] term k (TrivSqZeroExt D X) N n) :=
  Submodule.span D {w | ∃ (d : D) (v : term k (TrivSqZeroExt D X) N n),
    Word k D X N n r v ∧ w = d ⊗ₜ[k] v}

variable {k D X N}

theorem word_count_le {n r : ℕ} {v : term k (TrivSqZeroExt D X) N n}
    (hv : Word k D X N n r v) : r ≤ n := by
  induction hv with
  | nil => exact Nat.le_refl 0
  | base d h ih => exact Nat.le_trans ih (Nat.le_succ _)
  | ideal x h ih => exact Nat.succ_le_succ ih

theorem weight_eq_bot_of_lt {n r : ℕ} (h : n < r) : weight k D X N n r = ⊥ := by
  apply Submodule.span_eq_bot.mpr
  intro v hv
  exact False.elim (Nat.not_le_of_gt h (word_count_le hv))

/-- A count-r two-sided bar term is zero below degree r. -/
theorem twoSidedWeight_eq_bot_of_lt {n r : ℕ} (h : n < r) :
    twoSidedWeight k D X N n r = ⊥ := by
  apply Submodule.span_eq_bot.mpr
  rintro v ⟨d, z, hz, rfl⟩
  exact False.elim (Nat.not_le_of_gt h (word_count_le hz))

theorem tensor_weight_mem {n r : ℕ} (d : D) {v : term k (TrivSqZeroExt D X) N n}
    (hv : v ∈ weight k D X N n r) : d ⊗ₜ[k] v ∈ twoSidedWeight k D X N n r := by
  let g := TensorProduct.mk k D (term k (TrivSqZeroExt D X) N n) d
  have hle : weight k D X N n r ≤
      ((twoSidedWeight k D X N n r).restrictScalars k).comap g := by
    apply Submodule.span_le.mpr
    intro z hz
    exact Submodule.subset_span ⟨d, z, hz, rfl⟩
  exact hle hv

/-- Projection of the leading square-zero coefficient kills an ideal letter and retains a base letter. -/
theorem coefficient_weight_mem {n r : ℕ}
    {v : term k (TrivSqZeroExt D X) N (n+1)} (hv : v ∈ weight k D X N (n+1) r) :
    FreeBaseChange.coefficient (fstHom k D X) (term k (TrivSqZeroExt D X) N n) v ∈
      twoSidedWeight k D X N n r := by
  let g := FreeBaseChange.coefficient (fstHom k D X) (term k (TrivSqZeroExt D X) N n)
  have hle : weight k D X N (n+1) r ≤
      ((twoSidedWeight k D X N n r).restrictScalars k).comap g := by
    apply Submodule.span_le.mpr
    intro z hz
    cases hz with
    | base d h =>
      exact Submodule.subset_span ⟨d, _, h, rfl⟩
    | ideal x h =>
      change (0 : D) ⊗ₜ[k] _ ∈ twoSidedWeight k D X N n _
      rw [TensorProduct.zero_tmul]
      exact Submodule.zero_mem _
  exact hle hv

variable [Module (TrivSqZeroExt D X) N] [IsScalarTower k (TrivSqZeroExt D X) N]

/-- The actual D-linear two-sided differential preserves X-count; no flatness enters the proof. -/
theorem twoSidedDifferential_mem
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0)
    (n r : ℕ) {v : D ⊗[k] term k (TrivSqZeroExt D X) N (n+1)}
    (hv : v ∈ twoSidedWeight k D X N (n+1) r) :
    twoSidedDifferential k (TrivSqZeroExt D X) D N (fstHom k D X) n v ∈
      twoSidedWeight k D X N n r := by
  have hle : twoSidedWeight k D X N (n+1) r ≤
      (twoSidedWeight k D X N n r).comap
        (twoSidedDifferential k (TrivSqZeroExt D X) D N (fstHom k D X) n) := by
    apply Submodule.span_le.mpr
    rintro v ⟨d, z, hz, rfl⟩
    change twoSidedDifferential k (TrivSqZeroExt D X) D N (fstHom k D X) n
      (d ⊗ₜ[k] z) ∈ twoSidedWeight k D X N n r
    rw [twoSidedDifferential_tmul]
    exact Submodule.sub_mem _
      (Submodule.smul_mem _ d (coefficient_weight_mem (Submodule.subset_span hz)))
      (tensor_weight_mem d (differential_mem hN n r (Submodule.subset_span hz)))
  exact hle hv

variable (k D X N)

/-- A genuine D-module chain complex for each fixed number of square-zero entries. -/
def twoSidedWeightComplex
    (hN : ∀ (x : X) (v : N), (inr x : TrivSqZeroExt D X) • v = 0) (r : ℕ) :
    ChainComplex (ModuleCat D) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of D (twoSidedWeight k D X N n r))
    (fun n => ModuleCat.ofHom
      ((twoSidedDifferential k (TrivSqZeroExt D X) D N (fstHom k D X) n).restrict
        (fun v hv => twoSidedDifferential_mem hN n r hv)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact LinearMap.congr_fun
        (twoSidedDifferential_sq k (TrivSqZeroExt D X) D N (fstHom k D X) n) v)
end DerivedBar.SquareZero

end

end OAI
