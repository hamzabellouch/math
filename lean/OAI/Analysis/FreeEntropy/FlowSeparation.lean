import OAI.Analysis.FreeEntropy.ModelFlowLimit

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace FiniteEntropySeparation
 def chosenStart (h : ℝ) : ℝ := h/(4*((chosenP+1:ℕ):ℝ))
 theorem chosenStart_pos {h : ℝ} (hh : 0<h) : 0<chosenStart h := by unfold chosenStart; positivity
 theorem chosenStart_le_time {h : ℝ} (hh : h<1) : chosenStart h≤chosenTime := by
  unfold chosenStart
  apply (div_le_iff₀ (by positivity : (0:ℝ)<4*((chosenP+1:ℕ):ℝ))).mpr
  norm_num [chosenP,chosenTime] at *
  linarith
 theorem chosen_short_bound {h : ℝ} (hh : 0<h) :
    (1/2:ℝ)*(∫u in h..(h+chosenStart h),Model.heatFisherReal chosenP u)≤(1:ℝ)/8 := by
  have hb := Model.heatFisher_short_bound chosenP chosenP_ge_two hh (chosenStart_pos hh).le
  have he : ((chosenP+1:ℕ):ℝ)*chosenStart h/(2*h)=(1:ℝ)/8 := by
    unfold chosenStart
    field_simp
    ; ring
  rwa [he] at hb
 theorem flow_to_chiStar_gap {h β : ℝ} (hh0 : 0<h) (hh1 : h<1)
    (hflow : β+(1/2:ℝ)*(∫u in (h+chosenStart h)..(h+chosenTime),Model.heatFisherReal chosenP u)≤
      Model.gaussianEntropy chosenP (h+chosenTime)-1) :
    (β:EReal)≤chiStar (Model.τ chosenP) (Model.X chosenP h) (Model.auxiliaryNoise chosenP)-(1/2:EReal) := by
  have ht : 0<h+chosenTime := by linarith [chosenTime_pos]
  have hstart := chosenStart_pos hh0
  have hst := chosenStart_le_time hh1
  have ha : h≤h+chosenStart h := by linarith
  have hab : h+chosenStart h≤h+chosenTime := by linarith
  have hi1 := Model.heatFisherReal_intervalIntegrable chosenP chosenP_ge_two h (h+chosenStart h) hh0 ha
  have hi2 := Model.heatFisherReal_intervalIntegrable chosenP chosenP_ge_two (h+chosenStart h) (h+chosenTime) (by linarith) hab
  have he := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hf := Model.chiStar_flow chosenP chosenP_ge_two h (h+chosenTime) hh0 (by linarith [chosenTime_pos])
  rw [Model.chiStar_tail_formula chosenP chosenP_ge_two h hh0,
    Model.chiStar_tail_formula chosenP chosenP_ge_two (h+chosenTime) ht,← EReal.coe_sub] at hf
  have hfR := EReal.coe_injective hf
  have htail := Model.entropy_deficit_le chosenP chosenP_ge_two (h+chosenTime) ht (chosen_large_noise hh0.le)
  have hshort := chosen_short_bound hh0
  rw [Model.chiStar_tail_formula chosenP chosenP_ge_two h hh0]
  change (β:EReal)≤((Model.gaussianEntropy chosenP h-(1/2:ℝ)*(∫u in Ioi h,Model.fisherDeficit chosenP u):ℝ):EReal)-(((1/2:ℝ):ℝ):EReal)
  rw [← EReal.coe_sub,EReal.coe_le_coe_iff]
  linarith
end FiniteEntropySeparation

end

end OAI
