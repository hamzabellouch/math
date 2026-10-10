import OAI.Combinatorics.Progressions.Estimates.AllocatedReferenceJetWindow

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem selectedResidueSmoothWeight_pos_of_width {K X : Type*} [Fintype K] [Fintype X]
    (q : X → ℕ) (hq : ∀ x, 0 < q x)
    (cells : Finset (ColumnResiduePattern K X q)) (hcells : cells.Nonempty)
    (V : K × X → ℝ) (hV : ∀ z, 0 < V z) (hwidth : ∀ z, 2 * (q z.2 : ℝ) ≤ V z) :
    0 < ∑' z, selectedResidueSmoothWeight q cells V z := by
  obtain ⟨a, ha⟩ := hcells
  let z := boundedColumnResidueRepresentative q a
  have hres : columnResiduePattern q z = a := by
    apply (columnResiduePattern_eq_iff q a z).mpr
    exact fun i => boundedColumnResidueRepresentative_congr q a i
  have hsmall (i) : |(z i : ℝ) / V i| ≤ 1 / 2 := by
    obtain ⟨h0, h1⟩ := boundedColumnResidueRepresentative_bounds q hq a i
    have hz : (0 : ℝ) ≤ z i := by exact_mod_cast h0
    have hzq : (z i : ℝ) < q i.2 := by exact_mod_cast h1
    rw [abs_of_nonneg (div_nonneg hz (hV i).le), div_le_iff₀ (hV i)]
    linarith [hwidth i]
  have hpos : 0 < selectedResidueSmoothWeight q cells V z := by
    rw [selectedResidueSmoothWeight_plateau q cells V z (by rwa [hres]) hsmall]
    exact pow_pos smoothProbabilityProfile_pos_zero _
  exact hpos.trans_le (Summable.le_tsum (selectedResidueSmoothWeight_summable q cells V hV) z
    (fun _ _ => selectedResidueSmoothWeight_nonneg q cells V _))

namespace BooleanCubeKernel

theorem referenceJetEnvelope_mass_pos {X : Type*} [Fintype X] {dim : ℕ}
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (H : X → ℝ) (hH : ∀ x, 1 ≤ H x)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X q)) (hcells : cells.Nonempty) :
    0 < ∑' z, selectedResidueSmoothWeight q cells (referenceJetEnvelopeWidths q H) z := by
  apply selectedResidueSmoothWeight_pos_of_width q hq cells hcells _
    (referenceJetEnvelopeWidths_pos q hq H (fun x => lt_of_lt_of_le zero_lt_one (hH x)))
  intro z
  dsimp only [referenceJetEnvelopeWidths]
  have hh := mul_le_mul_of_nonneg_left (hH z.2) (by positivity : 0 ≤ 20 * (q z.2 : ℝ))
  nlinarith [show (0 : ℝ) ≤ q z.2 from Nat.cast_nonneg _]

end BooleanCubeKernel
end Erdos3

end

end OAI
