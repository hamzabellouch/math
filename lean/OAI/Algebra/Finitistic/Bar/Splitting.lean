import OAI.Algebra.Finitistic.Bar.Projection
import Mathlib.Algebra.DirectSum.Module

namespace OAI
open scoped TensorProduct DirectSum
open TensorProduct CategoryTheory TrivSqZeroExt
noncomputable section

namespace DerivedBar.SquareZero
universe u

private theorem internal_of_projections {R V : Type u} [Ring R] [AddCommGroup V] [Module R V]
    (S : ℕ → Submodule R V) (p : ℕ → Module.End R V)
    (hself : ∀ r v, v ∈ S r → p r v = v)
    (hother : ∀ r s, r ≠ s → ∀ v, v ∈ S s → p r v = 0)
    (htop : iSup S = ⊤) : DirectSum.IsInternal S := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top _ htop
  intro r
  rw [Submodule.disjoint_def]
  intro v hv hrest
  have hle : (⨆ (s : ℕ) (_ : s ≠ r), S s) ≤ (p r).ker := by
    refine iSup_le fun s => iSup_le fun hs => ?_
    intro w hw
    exact hother r s (Ne.symm hs) w hw
  have hz := hle hrest
  change p r v = 0 at hz
  rwa [hself r v hv] at hz

variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- The homogeneous absolute bar term is an internal direct sum. -/
theorem weight_internal (n : ℕ) : DirectSum.IsInternal (weight k D X N n) :=
  internal_of_projections _ (projection k D X N n)
    (fun _ _ h => projection_self h) (fun _ _ h _ hv => projection_other h hv)
    (weight_iSup k D X N n)

/-- Actual D-linear count projection on the two-sided bar term. -/
def twoSidedProjection (n r : ℕ) : Module.End D (D ⊗[k] term k (TrivSqZeroExt D X) N n) :=
  AlgebraTensorModule.lTensor D D (projection k D X N n r)

@[simp] theorem twoSidedProjection_tmul (n r : ℕ) (d : D)
    (v : term k (TrivSqZeroExt D X) N n) :
    twoSidedProjection k D X N n r (d ⊗ₜ[k] v) = d ⊗ₜ[k] projection k D X N n r v := rfl

variable {k D X N}

theorem twoSidedProjection_self {n r : ℕ}
    {v : D ⊗[k] term k (TrivSqZeroExt D X) N n} (hv : v ∈ twoSidedWeight k D X N n r) :
    twoSidedProjection k D X N n r v = v := by
  have hle : twoSidedWeight k D X N n r ≤
      (twoSidedProjection k D X N n r - LinearMap.id).ker := by
    apply Submodule.span_le.mpr
    rintro w ⟨d, z, hz, rfl⟩
    change d ⊗ₜ[k] projection k D X N n r z - d ⊗ₜ[k] z = 0
    rw [projection_word hz r, ite_eq_left rfl, sub_self]
  have hz := hle hv
  change twoSidedProjection k D X N n r v - v = 0 at hz
  exact sub_eq_zero.mp hz

theorem twoSidedProjection_other {n r s : ℕ} (hrs : r ≠ s)
    {v : D ⊗[k] term k (TrivSqZeroExt D X) N n} (hv : v ∈ twoSidedWeight k D X N n s) :
    twoSidedProjection k D X N n r v = 0 := by
  have hle : twoSidedWeight k D X N n s ≤ (twoSidedProjection k D X N n r).ker := by
    apply Submodule.span_le.mpr
    rintro w ⟨d, z, hz, rfl⟩
    change d ⊗ₜ[k] projection k D X N n r z = 0
    rw [projection_word hz r, ite_eq_right hrs, TensorProduct.tmul_zero]
  exact hle hv

variable (k D X N)

/-- Expansion of internal A entries as D ⊕ X spans the two-sided bar term as a D-module. -/
theorem twoSidedWeight_iSup (n : ℕ) : (⨆ r, twoSidedWeight k D X N n r) = ⊤ := by
  apply top_unique
  intro v hv
  clear hv
  induction v using TensorProduct.inductionOn with
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul d v =>
    let T := (⨆ r, twoSidedWeight k D X N n r)
    let g := TensorProduct.mk k D (term k (TrivSqZeroExt D X) N n) d
    have hle : Submodule.span k {w | ∃ r, Word k D X N n r w} ≤
        (T.restrictScalars k).comap g := by
      apply Submodule.span_le.mpr
      rintro w ⟨r, hw⟩
      exact (le_iSup (twoSidedWeight k D X N n) r)
        (Submodule.subset_span ⟨d, w, hw, rfl⟩)
    apply hle
    rw [all_words_span]
    trivial

/-- The genuine D-module decomposition of each two-sided bar term by X-count. -/
theorem twoSidedWeight_internal (n : ℕ) : DirectSum.IsInternal (twoSidedWeight k D X N n) :=
  internal_of_projections _ (twoSidedProjection k D X N n)
    (fun _ _ h => twoSidedProjection_self h)
    (fun _ _ h _ hv => twoSidedProjection_other h hv)
    (twoSidedWeight_iSup k D X N n)

/-- Canonical sum of homogeneous tensors, as a linear equivalence. -/
def twoSidedWeightEquiv (n : ℕ) :
    (⨁ r : ℕ, twoSidedWeight k D X N n r) ≃ₗ[D]
      D ⊗[k] term k (TrivSqZeroExt D X) N n :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap _) (twoSidedWeight_internal k D X N n)
end DerivedBar.SquareZero

end

end OAI
