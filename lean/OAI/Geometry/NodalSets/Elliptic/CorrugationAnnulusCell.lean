import OAI.Geometry.NodalSets.Elliptic.CorrugationFixedAmplitude
import OAI.Geometry.NodalSets.Elliptic.CorrugationGlobalJets

namespace OAI

namespace Yau.Geometry
open Set
noncomputable section

lemma centered_cell_integer_of_bounds (t : ℝ) (j : ℤ)
    (hlo : -1/2 ≤ t-(j:ℝ)) (hhi : t-(j:ℝ) < 1/2) :
    ⌊t+(1/2:ℝ)⌋ = j := by
  apply Int.floor_eq_iff.mpr
  constructor <;> linarith

lemma corrugationCellRadius_rectangle (z : ℝ × ℝ) (j k : ℤ)
    (h1 : z.1-(j:ℝ) ∈ Icc (1/16:ℝ) (3/32))
    (h2 : z.2-(k:ℝ) ∈ Icc (0:ℝ) (1/32)) :
    corrugationCellRadius z ∈ Icc (1/16:ℝ) (1/8) := by
  have hj := centered_cell_integer_of_bounds z.1 j (by linarith [h1.1]) (by linarith [h1.2])
  have hk := centered_cell_integer_of_bounds z.2 k (by linarith [h2.1]) (by linarith [h2.2])
  have hr := corrugationCellRadius_properties z
  have he : (corrugationCellRadius z)^2 = (z.1-(j:ℝ))^2+(z.2-(k:ℝ))^2 := by
    simpa only [corrugationCellPoint,corrugationCellIndex,hj,hk] using hr.2
  have hsq1 : (z.1-(j:ℝ))^2 ≤ (3/32:ℝ)^2 := sq_le_sq' (by linarith [h1.1]) h1.2
  have hsq2 : (z.2-(k:ℝ))^2 ≤ (1/32:ℝ)^2 := sq_le_sq' (by linarith [h2.1]) h2.2
  constructor
  · nlinarith [h1.1,sq_nonneg (z.2-(k:ℝ))]
  · nlinarith [hr.1]

lemma corrugation_rectangle_fixed_slope :
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ (z : ℝ × ℝ) (j k : ℤ),
      z.1-(j:ℝ) ∈ Icc (1/16:ℝ) (3/32) →
      z.2-(k:ℝ) ∈ Icc (0:ℝ) (1/32) →
      l₀ ≤ corrugationSlope corrugationFixedAmplitude (1/4) (corrugationCellRadius z) := by
  obtain ⟨l₀,hl₀,hann⟩ := corrugationFixedAmplitude_spec.2.2.2
  exact ⟨l₀,hl₀,fun z j k h1 h2 ↦ hann _ (corrugationCellRadius_rectangle z j k h1 h2)⟩

end
end Yau.Geometry

end OAI
