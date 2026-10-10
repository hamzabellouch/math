import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierProfilePairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveHeightBand

namespace OAI

/-! Compact Fourier Poincare profiles remain genuine sections after a
positive dilation of the cutoff. No unit-height lower bound is required. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups CompactlySupported
namespace CubicFirstMoment

theorem cubicThetaPositiveFourierProfile_compact_sum (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) {K : Set (ℂ × ℝ)} (hK : IsCompact K)
    (hpos : ∀ p∈K,0<p.2) :
    ∃ S : Finset CubicThetaBottomRow,∀ p∈K,
      cubicThetaFourierProfileSeries h p W=∑ r∈S,cubicThetaFourierProfileTerm h r p W := by
  obtain ⟨S,hS⟩ := cubicThetaRows_compact_below hε hK hpos
  refine ⟨S,fun p hp => ?_⟩
  apply tsum_eq_sum
  intro r hr
  exact cubicThetaFourierProfileTerm_zero h r p W (hW _ (hS p hp r hr).le)

lemma cubicThetaPositiveFourierProfile_continuousOn (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    ContinuousOn (fun p => cubicThetaFourierProfileSeries h p W) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaPositiveFourierProfile_compact_sum h W hε hW hK hKpos
  have he : (fun q => cubicThetaFourierProfileSeries h q W)=ᶠ[𝓝 p]
      (fun q => ∑ r∈S,cubicThetaFourierProfileTerm h r q W) := by
    filter_upwards [hKn] with q hq
    exact hS q hq
  have hd : ContinuousAt (fun q => ∑ r∈S,cubicThetaFourierProfileTerm h r q W) p := by
    clear hS he
    classical
    induction S using Finset.induction_on with
    | empty => simpa using (continuousAt_const (x:=p) (y:=(0:ℂ)))
    | @insert r S hr ih =>
      simp only [Finset.sum_insert hr]
      exact (cubicThetaFourierProfileTerm_continuousAt h r W hp).add ih
  exact (hd.congr_of_eventuallyEq he).continuousWithinAt

theorem cubicThetaPositiveFourierProfile_core (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    ∃ (H : ℝ) (S : Finset SL(2,Eisenstein)),∀ p : CubicThetaPoint,
      cubicThetaQuotientMap p∉cubicThetaQuotientCore S H →
        cubicThetaFourierProfileSeries h p.val W=0 := by
  obtain ⟨B,hB⟩ := W.hasCompactSupport.isCompact.bddAbove_image continuous_id.continuousOn
  obtain ⟨S,hS⟩ := cubicThetaPositiveHeightBand_core (H:=B) hε
  refine ⟨max B ε⁻¹,S,fun p hp => ?_⟩
  suffices hz : ∀ r,cubicThetaFourierProfileTerm h r p.val W=0 by
    simp only [cubicThetaFourierProfileSeries,hz,tsum_zero]
  intro r
  by_cases hlo : r.height p.val≤ε
  · exact cubicThetaFourierProfileTerm_zero h r p.val W (hW _ hlo)
  by_cases hz : W (r.height p.val)=0
  · exact cubicThetaFourierProfileTerm_zero h r p.val W hz
  have hhi : r.height p.val≤B := hB (mem_image_of_mem id (subset_closure hz))
  have he : cubicThetaPointHeight (r.completion • p)=r.height p.val := by
    change (cubicThetaBottomRow r.completion).height p.val=_
    rw [r.completion_row]
  have hq := hS 1 (r.completion • p) (by rw [he]; linarith) (by rw [he]; exact hhi)
  rw [one_smul,cubicThetaQuotient_covering.map_smul] at hq
  exact False.elim (hp hq)

def cubicThetaPositiveFourierProfileSection (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) : CubicThetaSection :=
  ⟨⟨fun p => cubicThetaFourierProfileSeries h p.val W,by
      apply continuous_iff_continuousAt.mpr
      intro p
      have hc := (cubicThetaPositiveFourierProfile_continuousOn h W hε hW).continuousAt
        ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)
      exact hc.comp continuous_subtype_val.continuousAt⟩,by
    intro g p
    exact cubicThetaFourierProfileSeries_automorphy h g p.property W⟩

lemma cubicThetaPositiveFourierProfileSection_compact (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    HasCompactSupport (cubicThetaSectionNorm (cubicThetaPositiveFourierProfileSection h W hε hW)) := by
  obtain ⟨H,S,hS⟩ := cubicThetaPositiveFourierProfile_core h W hε hW
  apply HasCompactSupport.of_support_subset_isCompact (cubicThetaQuotientCore_compact S H)
  intro q hq
  by_contra hn
  have hz := hS (cubicThetaQuotientLift q) (by rwa [cubicThetaQuotientLift_map])
  apply hq
  change ‖cubicThetaFourierProfileSeries h (cubicThetaQuotientLift q).val W‖=0
  rw [hz,norm_zero]

def cubicThetaPositiveFourierProfileL2 (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) : CubicThetaGlobalL2 :=
  (cubicThetaCompactSection_memLp (cubicThetaPositiveFourierProfileSection h W hε hW)
    (cubicThetaPositiveFourierProfileSection_compact h W hε hW)).toLp _

end CubicFirstMoment

end

end OAI
