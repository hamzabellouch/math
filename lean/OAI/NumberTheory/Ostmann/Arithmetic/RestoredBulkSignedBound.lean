import OAI.NumberTheory.Ostmann.Arithmetic.RestoredPrimeCellExpansion
import OAI.NumberTheory.Ostmann.Arithmetic.BulkWeightedCellComparison

namespace OAI

/-! # Return the signed bulk integral estimate to the original prime atoms -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

theorem restored_bulk_prime_bound {J C : Type*} [Fintype J] [Fintype C]
    (P : Finset ℕ) (M : ℕ) [NeZero M] (u v : J → C → ℝ)
    (hu : ∀ j c, 0 < u j c) (c₀ : C × (ZMod M)ˣ)
    (hP : ∀ j, primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) ⊆ P)
    (hsep : ∀ j (c d : C × (ZMod M)ˣ), c ≠ d →
      ¬Nat.ModEq M c.2.val.val d.2.val.val ∨ v j c.1 ≤ u j d.1 ∨ v j d.1 ≤ u j c.1)
    (D : J → Finset ℕ)
    (hD : ∀ j, (∑ p ∈ primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) \ D j, (p : ℝ)⁻¹) ≠ 0)
    (K : BulkIntegrand J) (a : (J → (ZMod M)ˣ) → ℂ)
    (input : PublishedProgressionInput) (Q : ℕ) (err : (J → C) → (J → (ZMod M)ˣ) → ℝ)
    (herror : ∀ c z,
      ‖(∫ y, K y ∂Measure.pi (fun j => primeLogCellMeasure M (z j).val.val (u j (c j)) (v j (c j)))) -
        ∫ y, K y ∂Measure.pi (fun j => primeGiantMeasure input Q M
          (z j).val.val (u j (c j)) (v j (c j)))‖ ≤ err c z)
    (B : ℝ) :
    let S := fun j => primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1)
    let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
    let label := fun (x : J → P) j => primeCellLabel M
      (fun c : C × (ZMod M)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) c₀ (x j)
    ‖∑ z, ∫ y, (K.constMul (a z)) y ∂Measure.pi (fun j => bulkCellMixture (Z j)
      (fun c => primeGiantMeasure input Q M (z j).val.val (u j c) (v j c)))‖ ≤ B →
    ‖∑ x : J → P,
      ((∏ j, (if (x j : ℕ) ∈ S j then Z j * (x j : ℝ)⁻¹ else 0) : ℝ) : ℂ) *
        (a (fun j => (label x j).2) * K (fun j => Real.log (x j : ℕ)))‖ ≤
      B + (∏ j, Z j) * ∑ c : J → C, ∑ z, ‖a z‖ * err c z := by
  dsimp only
  intro hmain
  let S := fun j => primeCellSupport M (fun c : C × (ZMod M)ˣ => c.2.val.val)
    (fun c => u j c.1) (fun c => v j c.1)
  let Z := fun j => (∑ p ∈ S j \ D j, (p : ℝ)⁻¹)⁻¹
  have hZ (j : J) : 0 ≤ Z j := by dsimp only [Z]; positivity
  let μ := fun (c : J → C) (z : J → (ZMod M)ˣ) j =>
    primeLogCellMeasure M (z j).val.val (u j (c j)) (v j (c j))
  let ν := fun (c : J → C) (z : J → (ZMod M)ˣ) j =>
    primeGiantMeasure input Q M (z j).val.val (u j (c j)) (v j (c j))
  let _ : ∀ c z j, IsFiniteMeasure (ν c z j) := fun c z j =>
    finite_primeGiantMeasure input Q M (z j).val.val _ _ (hu j (c j))
  let _ : ∀ (z : J → (ZMod M)ˣ) j c,
      IsFiniteMeasure (primeGiantMeasure input Q M (z j).val.val (u j c) (v j c)) :=
    fun z j c => finite_primeGiantMeasure input Q M (z j).val.val _ _ (hu j c)
  have hm := bulk_residue_mixture_integral Z hZ
    (fun z j c => primeGiantMeasure input Q M (z j).val.val (u j c) (v j c))
    (fun z => K.constMul (a z))
  rw [hm] at hmain
  have he := restored_bulk_residue_expansion P M u v c₀ hP hsep D hD
    (fun _ z => K.constMul (a z))
  exact (congrArg norm he).symm.trans_le
    (bulk_weighted_cell_bound K a Z hZ μ ν err herror B hmain)

end Ostmann

end OAI
