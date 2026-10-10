import OAI.MeasureTheory.Falconer.Geometry.IntegerEnergyRefinement
import OAI.MeasureTheory.Falconer.Estimates.ScalarRuzsa

namespace OAI

/-! Transfer the integer additive-energy refinement to separated real
sets, preserving the original points and the quantized difference bound. -/
namespace Falconer
open scoped Pointwise

theorem same_scalar_cell_dist_lt {δ x y : ℝ} (hδ : 0 < δ) (hcell : ⌊x/δ⌋ = ⌊y/δ⌋) :
    |x-y| < δ := by
  have hx0 := Int.floor_le (x/δ)
  have hx1 := Int.lt_floor_add_one (x/δ)
  have hy0 := Int.floor_le (y/δ)
  have hy1 := Int.lt_floor_add_one (y/δ)
  rw [hcell] at hx0 hx1
  have hh : |x/δ-y/δ| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  rw [← sub_div,abs_div,abs_of_pos hδ] at hh
  exact (div_lt_one hδ).1 hh

theorem scalarCells_injective {δ : ℝ} (hδ : 0 < δ) {A : Finset ℝ}
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|) :
    Set.InjOn (fun x => ⌊x/δ⌋) (A : Set ℝ) := by
  intro x hx y hy he
  by_contra hne
  exact (not_lt_of_ge (hsep x hx y hy hne)) (same_scalar_cell_dist_lt hδ he)

theorem scalar_energy_refinement {δ K : ℝ} (hδ : 0 < δ)
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|)
    (hBsep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ |x-y|)
    (hcard : A.card = B.card) (hK : 1 ≤ K)
    (henergy : (A.card : ℝ)^3 ≤ K*(Finset.addEnergy (scalarCells δ A) (scalarCells δ B) : ℝ)) :
    ∃ G ⊆ B, (B.card : ℝ)/(8*K) ≤ (G.card : ℝ) ∧
      ((scalarCells δ (G-G)).card : ℝ) ≤ 4194304*K^9*(B.card : ℝ) := by
  have hAc : (scalarCells δ A).card = A.card := Finset.card_image_of_injOn (scalarCells_injective hδ hAsep)
  have hBc : (scalarCells δ B).card = B.card := Finset.card_image_of_injOn (scalarCells_injective hδ hBsep)
  have hAn : (scalarCells δ A).Nonempty := Finset.image_nonempty.mpr hA
  have hBn : (scalarCells δ B).Nonempty := Finset.image_nonempty.mpr hB
  obtain ⟨S,hSB,hSsize,hSdiff⟩ := integer_energy_refinement (scalarCells δ A) (scalarCells δ B)
    hAn hBn (by rw [hAc,hBc,hcard]) hK (by simpa only [hAc] using henergy)
  obtain ⟨G,hGB,hGimage⟩ := Finset.subset_image_iff.mp hSB
  have hGc : G.card = S.card := by
    rw [← hGimage]
    exact (Finset.card_image_of_injOn ((scalarCells_injective hδ hBsep).mono hGB)).symm
  have hGdiff := scalarCells_sub_card δ G G
  change (scalarCells δ (G-G)).card ≤ 2*(G.image (fun x => ⌊x/δ⌋)-G.image (fun x => ⌊x/δ⌋)).card at hGdiff
  rw [hGimage] at hGdiff
  rw [hBc] at hSsize hSdiff
  refine ⟨G,hGB,by simpa only [hGc] using hSsize,?_⟩
  have hGdiffR : ((scalarCells δ (G-G)).card : ℝ) ≤ 2*((S-S).card : ℝ) := by exact_mod_cast hGdiff
  nlinarith

end Falconer

end OAI
