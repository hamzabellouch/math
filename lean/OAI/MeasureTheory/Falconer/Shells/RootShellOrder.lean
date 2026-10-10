import OAI.MeasureTheory.Falconer.Shells.RootShellMixture
import OAI.MeasureTheory.Falconer.Estimates.ListBoundedFunctions
import OAI.MeasureTheory.Falconer.Shells.ListWeightedShell

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace RootShellData

noncomputable def inverseOrderForm (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ) (r : ℝ) : ℂ :=
  ((inverseLeibnizTerms j (d.indices)).map (fun b =>
    d.coefficient j b*d.inverseSpatialMixture δ L hδ hL j b.2 r)).sum

theorem inverseOrderForm_data (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (j : ℕ) :
    Measurable (d.inverseOrderForm δ L hδ hL j) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖d.inverseOrderForm δ L hδ hL j r‖ ≤ C := by
  apply list_sum_measurable_bounded
  intro b hb
  have hmdata := d.inverseSpatialMixture_data δ L hδ hL hd he j hb (Measure.dirac (0:ℝ))
  refine ⟨hmdata.1.const_mul _,
    ‖d.coefficient j b‖*
      (spatialFourierCost δ L hδ hL j*d.inversePhasedBound j),?_,?_⟩
  · exact mul_nonneg (norm_nonneg _) (mul_nonneg (spatialFourierCost_nonneg ..) (d.inversePhasedBound_nonneg j))
  · intro r
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hmdata.2.1 r) (norm_nonneg _)

theorem inverseOrderForm_shell (d : RootShellData) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) [IsFiniteMeasure d.left.ρ] [IsFiniteMeasure d.right.ρ]
    (hd : 0 < d.left.Q.side) (he : 0 < d.right.Q.side) (hsig : 0 ≤ d.sig)
    (hL₁ : ∀ b ∈ d.left.S, descriptorLength b ≤ d.N/2)
    (hL₂ : ∀ b ∈ d.right.S, descriptorLength b ≤ d.N/2) (j : ℕ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] {B : ℝ} (_hB0 : 0 ≤ B)
    (hB : ∀ b ∈ inverseLeibnizTerms j (d.indices), ∀ ξ,
      (∫ r, ‖d.inversePhasedForm b.2 ξ r‖^2 ∂μ) ≤ B) :
    (∫ r, ‖d.inverseOrderForm δ L hδ hL j r‖^2 ∂μ) ≤
      (spatialFourierCost δ L hδ hL j *
        ((inverseLeibnizTerms j (d.indices)).map (fun b => ‖b.1‖)).sum)^2*B := by
  let C := spatialFourierCost δ L hδ hL j
  have hC : 0 ≤ C := spatialFourierCost_nonneg ..
  let I := inverseLeibnizTerms j (d.indices)
  let F := fun b : ℂ × (RootMaskIndex → ℕ) =>
    fun r => d.coefficient j b*d.inverseSpatialMixture δ L hδ hL j b.2 r
  have ht (b : ℂ × (RootMaskIndex → ℕ)) (hb : b ∈ I) :
      Measurable (F b) ∧ Integrable (fun r => ‖F b r‖^2) μ ∧
        (∫ r, ‖F b r‖^2 ∂μ) ≤ (‖b.1‖*C)^2*B := by
    have hmdata := d.inverseSpatialMixture_data δ L hδ hL hd he j hb μ
    have hcoeff := d.coefficient_norm hsig hL₁ hL₂ j hb
    have hm := shell_multiplier_square μ (fun _ => d.coefficient j b)
      (d.inverseSpatialMixture δ L hδ hL j b.2) measurable_const hmdata.1 hmdata.2.2 (norm_nonneg b.1)
      (Eventually.of_forall (fun _ => hcoeff))
    refine ⟨hmdata.1.const_mul _,hm.1,?_⟩
    apply hm.2.trans
    apply (mul_le_mul_of_nonneg_left (d.inverseSpatialMixture_shell δ L hδ hL hd he j hb μ (hB b hb))
      (sq_nonneg ‖b.1‖)).trans_eq
    dsimp [C]
    ring
  have hh := list_weighted_shell_square I μ F (fun b => ‖b.1‖*C)
    (fun b _ => mul_nonneg (norm_nonneg _) hC)
    (fun b hb => (ht b hb).2.1) (fun b hb => (ht b hb).1.aestronglyMeasurable)
    (fun b hb => (ht b hb).2.2)
  have he : (I.map (fun b => ‖b.1‖*C)).sum = C*(I.map (fun b => ‖b.1‖)).sum := by
    rw [List.sum_map_mul_right]
    ring
  rw [he] at hh
  exact hh

end RootShellData

end PlanarFalconer

end OAI
