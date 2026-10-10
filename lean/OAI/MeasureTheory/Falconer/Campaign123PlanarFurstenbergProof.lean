import OAI.MeasureTheory.Falconer.Incidence.OriginalBlockIncidence
import OAI.MeasureTheory.Falconer.Estimates.OriginalWeakCosts
import OAI.MeasureTheory.Falconer.Estimates.OneInputMain

namespace OAI

/-! Discharge the precise planar Furstenberg specialization used by the
all-dimensional Falconer proof, by the finite multiscale incidence argument. -/
namespace Falconer
open MeasureTheory
open scoped ENNReal

theorem publishedPlanarFurstenberg_proved : PublishedPlanarFurstenberg := by
  intro b f hb hbhalf hbf hf1
  let κ := min b (min (f-b) (1/100:ℝ))/16
  have hκ : 0 < κ := div_pos (lt_min hb (lt_min (sub_pos.mpr hbf) (by norm_num))) (by norm_num)
  have hκb : κ ≤ b/16 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hκg : κ ≤ (f-b)/16 := div_le_div_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  have hκone : κ ≤ (1/100:ℝ)/16 := div_le_div_of_nonneg_right
    ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  obtain ⟨B,hB,_,lam,ζ,hlam,hζ,M,hM,hblock⟩ := original_block_incidence hκ
    (by linarith : κ ≤ 1/100) (by linarith : κ ≤ b) (by linarith : b ≤ 1-8*κ)
    (by linarith : b+8*κ ≤ f) (by linarith : f ≤ 2)
  have hC : 0 ≤ originalIncidenceCost B := by unfold originalIncidenceCost; positivity
  obtain ⟨ε,hε,hε1,_,_,N0,hN0,habsorb⟩ := exists_incidence_absorption_parameters hlam hζ
    (originalIncidenceCost B) hC
  let δ0 := min 1 (1/(4*(2:ℝ)^(B*(M+N0+1))))
  have hδ0 : 0 < δ0 := lt_min (by norm_num) (by positivity)
  refine ⟨ε,δ0,hε,hδ0,min_le_left _ _,?_⟩
  intro δ hδ hδsmall P hP hPchart hPsep hPball V hV
  have hδ1 : δ ≤ 1 := hδsmall.le.trans (min_le_left _ _)
  have hsmall : δ ≤ 1/(4*(2:ℝ)^(B*(M+N0+1))) := hδsmall.le.trans (min_le_right _ _)
  obtain ⟨m,hm,hscale,hscale'⟩ := incidence_block_scale_choice hB hδ hsmall
  have hmM : M ≤ m := by omega
  have hNm : m ≤ m*B := Nat.le_mul_of_pos_right m hB
  have hNN : N0 ≤ m*B := by omega
  obtain ⟨hpoly,hfinal⟩ := habsorb (m*B) hNN
  have hcost := original_weak_costs hδ hδ1 hε.le hε1 hlam.le hb.le
    (by linarith : b ≤ 1) (by linarith : 0 ≤ f) (by linarith : f ≤ 2) hscale' hpoly hfinal
  have hK : 1 ≤ δ^(-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hcard := hblock m hmM δ (δ^(-ε)) hδ hδ1 hK hscale hcost.1
    P hP hPchart hPsep hPball V hV
  have hcoeff : 0 < 162*δ^(-ε)*δ^b*(16*(1/(2:ℝ)^(m*B))/δ+1)^2 := by positivity
  exact (mul_le_mul_iff_right₀ hcoeff).mp (hcost.2.trans hcard)

theorem falconer_distance_conjecture :
    ∀ (d : ℕ), 2 ≤ d → ∀ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E →
      (d : ℝ≥0∞) / 2 < dimH E →
        0 < volume {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r} :=
  mainTarget_of_planar_furstenberg publishedPlanarFurstenberg_proved

end Falconer

end OAI
