import Mathlib
import OAI.Computability.MaxCut.Games.AffineWitnessFiniteDensity
import OAI.Computability.MaxCut.Games.RowErasureSelection

namespace OAI

/-!
Normalize the affine target chosen from visible row advice. The selected row
and column equations are unchanged. Only the target coefficient and intercept
are replaced, with exact target equality on the entire selected slice.
-/

namespace MaxCutGames.Inverse.RowErasureDescriptions

open MaxCutGames.Inverse.Shortcode

/-- Replace the affine target while retaining all row and column data. -/
def Description.withTarget {ell m r : ℕ} (d : Description ell m r)
    (z : Vector m) (u : Vector ell) : Description ell m r :=
  (d.1, d.2.1, d.2.2.1, d.2.2.2.1, z, u)

@[simp] theorem Description.withTarget_toSlice {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).toSlice = d.toSlice := rfl

@[simp] theorem Description.withTarget_coefficient {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).coefficient = z := rfl

@[simp] theorem Description.withTarget_intercept {ell m r : ℕ}
    (d : Description ell m r) (z : Vector m) (u : Vector ell) :
    (d.withTarget z u).intercept = u := rfl

end MaxCutGames.Inverse.RowErasureDescriptions

namespace MaxCutGames.Inverse.RowErasureMatrix

open MaxCutGames.Inverse.Shortcode
open MaxCutGames.Inverse.RowErasure
open MaxCutGames.Inverse.RowErasureDescriptions

noncomputable section

variable {ell m r : ℕ}

/-- Normalization of the already chosen description. The sampled matrix is
absent from the selector's inputs; pointwise target equality holds afterward
for every matrix in the selected slice. -/
theorem exists_normalizedChosenDescription
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    let d₀ := (family ell m r).chosenDescription f α A S hgood
    ∃ d : Description ell m r,
      (family ell m r).rowMap d = A ∧
      (family ell m r).rowValue d = S ∧
      ((family ell m r).points d).Nonempty ∧
      α / 2 ≤ (family ell m r).agreement f d ∧
      e d.coefficient = 1 ∧
      d.toSlice = d₀.toSlice ∧
      (family ell m r).agreement f d = (family ell m r).agreement f d₀ ∧
      ∀ M, M ∈ (family ell m r).points d₀ →
        (family ell m r).target d M = (family ell m r).target d₀ M := by
  classical
  let d₀ := (family ell m r).chosenDescription f α A S hgood
  obtain ⟨hrow, hvalue, hnonempty, hagree⟩ :=
    (family ell m r).chosenDescription_spec f α A S hgood
  obtain ⟨M₀, hM₀⟩ := hnonempty
  have hcontains : d₀.toSlice.Contains M₀ := by
    exact (Finset.mem_filter.mp hM₀).2
  have hagree' : α / 2 ≤ d₀.toSlice.affineAgreement f d₀.coefficient d₀.intercept := by
    exact (family_agreement d₀ f) ▸ hagree
  obtain ⟨z, u, hfirst, heq, htarget⟩ :=
    d₀.toSlice.first_bit_normalization M₀ hcontains e f d₀.coefficient d₀.intercept
      (fun h M => hfold h M) α hα hagree' hsmall
  have heq' : (family ell m r).agreement f (d₀.withTarget z u) =
      (family ell m r).agreement f d₀ := by
    rw [family_agreement, family_agreement]
    exact heq
  refine ⟨d₀.withTarget z u, hrow, hvalue, ⟨M₀, hM₀⟩, ?_, hfirst, rfl, heq', ?_⟩
  · exact heq'.symm ▸ hagree
  · intro M hM
    exact htarget M (Finset.mem_filter.mp hM).2

/-- A fixed normalized witness determined by the visible table and row advice.
All remaining inputs are the fixed normalization functional and proofs. -/
def normalizedChosenDescription
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    Description ell m r :=
  Classical.choose (exists_normalizedChosenDescription f α A S hgood e hfold hα hsmall)

theorem normalizedChosenDescription_spec
    (f : Mat ell m → Vector ell) (α : ℝ) (A : RowMap ell r) (S : Mat r m)
    (hgood : (family ell m r).GoodAdvice f α A S)
    (e : Vector m →ₗ[F2] F2)
    (hfold : ∀ (h : Vector ell) M,
      f (M + rankOne h (functionalRow e)) = f M + h)
    (hα : 0 < α) (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    let d₀ := (family ell m r).chosenDescription f α A S hgood
    let d := normalizedChosenDescription f α A S hgood e hfold hα hsmall
    (family ell m r).rowMap d = A ∧
      (family ell m r).rowValue d = S ∧
      ((family ell m r).points d).Nonempty ∧
      α / 2 ≤ (family ell m r).agreement f d ∧
      e d.coefficient = 1 ∧
      d.toSlice = d₀.toSlice ∧
      (family ell m r).agreement f d = (family ell m r).agreement f d₀ ∧
      ∀ M, M ∈ (family ell m r).points d₀ →
        (family ell m r).target d M = (family ell m r).target d₀ M :=
  Classical.choose_spec
    (exists_normalizedChosenDescription f α A S hgood e hfold hα hsmall)

end
end MaxCutGames.Inverse.RowErasureMatrix

end OAI
