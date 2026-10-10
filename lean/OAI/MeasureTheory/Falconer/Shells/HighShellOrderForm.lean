import OAI.MeasureTheory.Falconer.Shells.HighShellMixture
import OAI.MeasureTheory.Falconer.Estimates.ListBoundedFunctions
import OAI.MeasureTheory.Falconer.Estimates.SpatialLeibnizSubpower

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace PositiveDistanceData

noncomputable def inverseOrderForm (d : PositiveDistanceData) (j : ℕ) (v r : ℝ) : ℂ :=
  ((inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)).map (fun b =>
    d.absorbedInverseCoefficient j v b*d.inverseSpatialMixture j b.2 r)).sum

theorem inverseOrderForm_data (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (j : ℕ) (v : ℝ) :
    Measurable (d.inverseOrderForm j v) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖d.inverseOrderForm j v r‖ ≤ C := by
  apply list_sum_measurable_bounded
  intro b hb
  have hd := d.inverseSpatialMixture_data hQ j hb (Measure.dirac (0:ℝ))
  refine ⟨hd.1.const_mul _,
    ‖d.absorbedInverseCoefficient j v b‖*
      (spatialFourierCost 96 2004 (by norm_num) (by norm_num) j*d.inversePhasedBound j),?_,?_⟩
  · exact mul_nonneg (norm_nonneg _) (mul_nonneg (spatialFourierCost_nonneg ..) (d.inversePhasedBound_nonneg j))
  · intro r
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hd.2.1 r) (norm_nonneg _)

theorem inverseOrderForm_shell (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hsig : 0 ≤ d.sig) (hq : 0 < d.q)
    (hqs : d.sig*d.N ≤ (d.q:ℝ)) (hw : d.a+100*d.q < d.t)
    {v : ℝ} (hv : (d.t:ℝ)-d.sig*d.N ≤ v) (j : ℕ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] {B : ℝ} (_hB0 : 0 ≤ B)
    (hB : ∀ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList), ∀ ξ,
      (∫ r, ‖d.inversePhasedForm b.2 ξ r‖^2 ∂μ) ≤ B) :
    (∫ r, ‖d.inverseOrderForm j v r‖^2 ∂μ) ≤
      (spatialFourierCost 96 2004 (by norm_num) (by norm_num) j *
        ((inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)).map (fun b => ‖b.1‖)).sum)^2*B := by
  let C := spatialFourierCost 96 2004 (by norm_num) (by norm_num) j
  have hC : 0 ≤ C := spatialFourierCost_nonneg ..
  let L := inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList)
  let F := fun b : ℂ × (PairMaskIndex → ℕ) =>
    fun r => d.absorbedInverseCoefficient j v b*d.inverseSpatialMixture j b.2 r
  have ht (b : ℂ × (PairMaskIndex → ℕ)) (hb : b ∈ L) :
      Measurable (F b) ∧ Integrable (fun r => ‖F b r‖^2) μ ∧
        (∫ r, ‖F b r‖^2 ∂μ) ≤ (‖b.1‖*C)^2*B := by
    have hd := d.inverseSpatialMixture_data hQ j hb μ
    have hcoeff := d.absorbedInverseCoefficient_norm hsig hq hqs hw hv j hb
    have hm := shell_multiplier_square μ (fun _ => d.absorbedInverseCoefficient j v b)
      (d.inverseSpatialMixture j b.2) measurable_const hd.1 hd.2.2 (norm_nonneg b.1)
      (Eventually.of_forall (fun _ => hcoeff))
    refine ⟨hd.1.const_mul _,hm.1,?_⟩
    apply hm.2.trans
    apply (mul_le_mul_of_nonneg_left (d.inverseSpatialMixture_shell hQ j hb μ (hB b hb))
      (sq_nonneg ‖b.1‖)).trans_eq
    dsimp [C]
    ring
  have hh := list_weighted_shell_square L μ F (fun b => ‖b.1‖*C)
    (fun b _ => mul_nonneg (norm_nonneg _) hC)
    (fun b hb => (ht b hb).2.1) (fun b hb => (ht b hb).1.aestronglyMeasurable)
    (fun b hb => (ht b hb).2.2)
  have he : (L.map (fun b => ‖b.1‖*C)).sum = C*(L.map (fun b => ‖b.1‖)).sum := by
    rw [List.sum_map_mul_right]
    ring
  rw [he] at hh
  exact hh

end PositiveDistanceData

end PlanarFalconer

end OAI
