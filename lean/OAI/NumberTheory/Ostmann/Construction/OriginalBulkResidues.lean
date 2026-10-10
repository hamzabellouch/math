import OAI.NumberTheory.Ostmann.Construction.OriginalPrimeCellExpansion
import OAI.NumberTheory.Ostmann.Construction.PrimeGridResidueLift

namespace OAI

/-! # Separating the real cells and residues of the original prime sample -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem sum_joint_cells_residues {J C R : Type*}
    [Fintype J] [Fintype C] [Fintype R] (F : (J → C × R) → ℂ) :
    (∑ a : J → C × R, F a) =
      ∑ c : J → C, ∑ z : J → R, F (fun j => (c j, z j)) := by
  let e := Equiv.arrowProdEquivProdArrow J (fun _ => C) (fun _ => R)
  rw [← e.symm.sum_comp F, Fintype.sum_prod_type]
  rfl

/-- Each actual prime tuple selects its own residue kernel. The left side is
precisely the joint box/residue sum to which the Page comparison is applied. -/
theorem original_bulk_residue_expansion {J C : Type*} [Fintype J] [Fintype C]
    (P : Finset ℕ) (M : ℕ) [NeZero M] (u v : J → C → ℝ)
    (c₀ : C × (ZMod M)ˣ)
    (hP : ∀ j, primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) ⊆ P)
    (hsep : ∀ j (c d : C × (ZMod M)ˣ), c ≠ d →
      ¬Nat.ModEq M c.2.val.val d.2.val.val ∨ v j c.1 ≤ u j d.1 ∨ v j d.1 ≤ u j c.1)
    (f : (J → C) → (J → (ZMod M)ˣ) → BulkIntegrand J) :
    let S := fun j => primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1)
    let Z := fun j => (∑ p ∈ S j, (p : ℝ)⁻¹)⁻¹
    let label := fun (x : J → P) j => primeCellLabel M
      (fun c : C × (ZMod M)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) c₀ (x j)
    ((∏ j, Z j : ℝ) : ℂ) * ∑ c : J → C, ∑ z : J → (ZMod M)ˣ,
      ∫ y, f c z y ∂Measure.pi (fun j => primeLogCellMeasure M (z j).val.val (u j (c j)) (v j (c j))) =
    ∑ x : J → P, ((∏ j, primeSubsetPrior P (S j) (x j) : ℝ) : ℂ) *
      f (fun j => (label x j).1) (fun j => (label x j).2) (fun j => Real.log (x j : ℕ)) := by
  have h := original_prime_cell_expansion P (fun _ : J => M)
    (fun _ (c : C × (ZMod M)ˣ) => c.2.val.val)
    (fun j c => u j c.1) (fun j c => v j c.1) c₀ hP hsep
    (fun a => f (fun j => (a j).1) (fun j => (a j).2))
  rw [sum_joint_cells_residues] at h
  exact h

end Ostmann

end OAI
