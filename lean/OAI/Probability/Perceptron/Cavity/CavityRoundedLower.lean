import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityApproxStationary
import OAI.Probability.Perceptron.Variational.CappedAContinuity
import OAI.Probability.Perceptron.Cavity.BulkCavityRecursion

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

def cavityProfileMoment (η : Measure Time) (B : ℝ) : ℝ :=
  ∫ r : Time,(r:ℝ)*cappedA η B r/2 ∂η

def roundedProfileMoment (η : Measure Time) [IsProbabilityMeasure η] (B : ℝ) (j : ℕ) : ℝ :=
  let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  let M:=strictRoundModel F j
  ∑ i,M.weight i*(cappedA η B (roundTimeValue F j i)/2)*(roundTimeValue F j i:ℝ)

lemma roundedProfileMoment_tendsto (η : Measure Time) [IsProbabilityMeasure η]
    {B : ℝ} (hB : B<1) :
    Tendsto (roundedProfileMoment η B) atTop (𝓝 (cavityProfileMoment η B)) := by
  let G : Time→ᵇℝ:=ContinuousMap.equivBoundedOfCompact Time ℝ
    ⟨fun r=>(r:ℝ)*cappedA η B r/2,by exact
      (continuous_subtype_val.mul ((cappedA_continuous η hB).comp continuous_subtype_val)).div_const 2⟩
  have h:=ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (quantileRoundLaw_tendsto η) G
  have he j : (∫ r,G r ∂(quantileRoundLaw η j : Measure Time))=roundedProfileMoment η B j := by
    let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
    change (∫ r : Time,(r:ℝ)*cappedA η B r/2 ∂timeLaw.map (roundTime F j))=_
    rw [integral_map (roundTime_mono F j).measurable.aemeasurable (by
      exact ((continuous_subtype_val.mul ((cappedA_continuous η hB).comp continuous_subtype_val)).div_const 2).measurable.aestronglyMeasurable)]
    change (∫ u,(roundTime F j u:ℝ)*cappedA η B (roundTime F j u)/2 ∂timeLaw)=_
    have hv:=(strictRoundModel F j).integral (fun r=>r*cappedA η B r/2)
    change (∫ u,(roundTime F j u:ℝ)*cappedA η B (roundTime F j u)/2 ∂timeLaw)=_ at hv
    rw [hv]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [roundedProfileMoment,roundTimeValue,F]
    ring
  simp_rw [he] at h
  convert h using 1
  rfl

lemma roundedCavityValue_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    {α : ℝ} (hα : 0≤α) (g : Jet3) (n d : ℕ)
    (η : Measure Time) [IsProbabilityMeasure η] {B K a ε : ℝ}
    (hB : B<1) (ha0 : 0≤a) (haK : a≤K)
    (hη : ∀ᵐ r : Time ∂η,(r:ℝ)≤B) (hA : ∀ᵐ r : Time ∂η,cappedA η B r≤a)
    (hdα : |(d:ℝ)-(n+1:ℕ)*α|≤1)
    (hdim : ∀ k (w h : Fin (k+1)→ℝ) (hw : ∀ i,0<w i) (hw1 : ∑ i,w i=1),
      Monotone h → 0≤h 0 → h (Fin.last k)≤K/2 →
      |finiteSphericalFieldValue n k w h-sInf (finiteSphericalDualValues w h (fun i=>(hw i).le) hw1)|<ε)
    (j : ℕ) :
    (n+1:ℕ)*(a/2+(terminalVariational P α g.f).toReal-roundedProfileMoment η B j-
      cappedAError (quantileRoundLaw η j) η B-ε)-‖g.f‖ ≤
      roundedCavityValue n d g P η B ha0 haK j := by
  let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  let M:=strictRoundModel F j
  let q:=roundTimeValue F j
  let h:=fun i=>cappedA η B (q i)/2
  let h':=fun i=>cappedA (quantileRoundLaw η j) B (q i)/2
  have hh : Monotone h:=fun i l hil=>div_le_div_of_nonneg_right
    ((cappedA_monotone η hB) (roundTimeValue_mono F j hil)) (by norm_num)
  have hh' : Monotone h':=fun i l hil=>div_le_div_of_nonneg_right
    ((cappedA_monotone (quantileRoundLaw η j) hB) (roundTimeValue_mono F j hil)) (by norm_num)
  have hh0 : 0≤h 0:=div_nonneg (cappedA_nonneg η B (q 0).prop.1) (by norm_num)
  have hh'0 : 0≤h' 0:=div_nonneg (cappedA_nonneg (quantileRoundLaw η j) B (q 0).prop.1) (by norm_num)
  have hp i : (roundedCavityPair η B ha0 haK j i).2.val=cappedA η B (q i) :=
    roundTimeValue_profile_exact η hB ha0 haK hA j i
  have htop : h (Fin.last M.depth)≤K/2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    rw [←hp]
    exact ((roundedCavityPair η B ha0 haK j _).2.prop.2)
  have hq1 : (q (Fin.last M.depth):ℝ)<1:=
    (roundTimeValue_support η hη j _).trans_lt hB
  have hs i : 2*h' i=weightedStepA M.weight (fun l=>(q l:ℝ)) (q i) := by
    dsimp [h']; rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)]
    exact quantileRoundLaw_stationary η hη j i
  have hd i : |h i-h' i|≤cappedAError (quantileRoundLaw η j) η B/2 := by
    dsimp [h,h']
    rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),abs_sub_comm]
    exact div_le_div_of_nonneg_right (cappedA_sub_bound (quantileRoundLaw η j) η hB (q i)) (by norm_num)
  have hlow:=finiteCavity_trial_lower P hα g.f n d M.weight h h' q M.weight_pos M.weight_sum hh hh0 hh' hh'0
    (roundTimeValue_mono F j) hq1 hs
    (div_nonneg (cappedAError_nonneg _ _ _) (by norm_num)) hd
    (hdim _ _ _ M.weight_pos M.weight_sum hh hh0 htop) hdα (a:=a)
  have herr : 2*(cappedAError (quantileRoundLaw η j) η B/2)=cappedAError (quantileRoundLaw η j) η B:=by ring
  rw [herr] at hlow
  unfold roundedCavityValue
  simp_rw [hp]
  exact hlow


lemma markedTimePair_eq_map (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K))) :
    markedTimePair K μ=(μ : Measure (CompactArray (BulkPairRange K))).map
      (fun Q=>nonnegativeSpinTime (Q 0 1).1) := by
  change Measure.map (fun Q : CompactArray Time=>Q 0 1)
    (Measure.map (compactMapArray (fun p : BulkPairRange K=>nonnegativeSpinTime p.1)) (μ : Measure _))=_
  rw [Measure.map_map (by fun_prop) (by
    exact (compactMapArray_continuous (nonnegativeSpinTime_continuous.comp continuous_fst)).measurable)]
  rfl

lemma marked_cappedA_identification {K B a : ℝ}
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hB : B<1)
    (hn : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),0≤(Q 0 1).1.val)
    (hBd : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),(Q 0 1).2.val≤a)
    (f : ℝ→ℝ)
    (hg : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),(Q 0 1).2.val=f (Q 0 1).1.val)
    (hsc : ∀ᵐ r : Time ∂markedTimePair K μ,f r=∫ t in 0..(r:ℝ),(realTail (markedTimePair K μ) t)⁻¹^2)
    (hbound : ∀ᵐ r : Time ∂markedTimePair K μ,(r:ℝ)≤B) :
    (∀ᵐ r : Time ∂markedTimePair K μ,cappedA (markedTimePair K μ) B r≤a) ∧
    cavityProfileMoment (markedTimePair K μ) B=
      (∫ Q,(Q 0 1).1.val*(Q 0 1).2.val ∂(μ : Measure (CompactArray (BulkPairRange K))))/2 := by
  let e:=fun Q : CompactArray (BulkPairRange K)=>nonnegativeSpinTime (Q 0 1).1
  have he : Measurable e:=(nonnegativeSpinTime_continuous.comp (by fun_prop)).measurable
  have hid : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),
      cappedA (markedTimePair K μ) B (e Q)=(Q 0 1).2.val := by
    filter_upwards [markedTimePair_ae μ hsc,markedTimePair_ae μ hbound,hn,hg] with Q hS hBd hN hG
    rw [cappedA_eq_integral (markedTimePair K μ) hbound (e Q).prop.1 hBd,←hS]
    rw [nonnegativeSpinTime_val hN]
    exact hG.symm
  have hmap : (μ : Measure (CompactArray (BulkPairRange K))).map e=markedTimePair K μ :=
    (markedTimePair_eq_map K μ).symm
  constructor
  · have hh : ∀ᵐ r : Time ∂(μ : Measure _).map e,cappedA (markedTimePair K μ) B r≤a := by
      apply (ae_map_iff he.aemeasurable (measurableSet_le
        (((cappedA_continuous (markedTimePair K μ) hB).comp continuous_subtype_val).measurable)
        measurable_const)).mpr
      filter_upwards [hid,hBd] with Q hQ hBnd
      change cappedA (markedTimePair K μ) B (e Q)≤a
      rwa [hQ]
    rwa [hmap] at hh
  · have hi:=integral_map he.aemeasurable
      (show AEStronglyMeasurable (fun r : Time=>(r:ℝ)*cappedA (markedTimePair K μ) B r/2)
        ((μ : Measure _).map e) from
        ((continuous_subtype_val.mul ((cappedA_continuous (markedTimePair K μ) hB).comp
          continuous_subtype_val)).div_const 2).measurable.aestronglyMeasurable)
    rw [hmap] at hi
    unfold cavityProfileMoment
    rw [hi,←integral_div]
    apply integral_congr_ae
    filter_upwards [hid,hn] with Q hQ hN
    rw [hQ,nonnegativeSpinTime_val hN]
end SphericalPerceptronFreeEnergy

end

end OAI
