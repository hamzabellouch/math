import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierStripSupport

namespace OAI

/-! Scalar height windows on the same arithmetic quotient. Their multiplier
is trivial; they will be paired with the invariant squared theta norm. -/
noncomputable section
open Set Filter Topology
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaScalarWindow (W : C_c(ℝ,ℂ)) (p : ℂ × ℝ) : ℂ :=
  ∑' r : CubicThetaBottomRow,W (r.height p)

lemma cubicThetaScalarWindow_invariant (W : C_c(ℝ,ℂ))
    (g : cubicThetaPrincipalGroup) {p : ℂ × ℝ} (hp : 0<p.2) :
    cubicThetaScalarWindow W (cubicThetaMobius (cubicThetaPrincipalComplex g) p)=
      cubicThetaScalarWindow W p := by
  unfold cubicThetaScalarWindow
  simp_rw [←CubicThetaBottomRow.height_rightMul _ g hp]
  exact (CubicThetaBottomRow.rightMulEquiv g).tsum_eq (fun r => W (r.height p))

lemma cubicThetaScalarWindow_compact_sum (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) {K : Set (ℂ × ℝ)}
    (hK : IsCompact K) (hpos : ∀ p∈K,0<p.2) :
    ∃ S : Finset CubicThetaBottomRow,∀ p∈K,
      cubicThetaScalarWindow W p=∑ r∈S,W (r.height p) := by
  obtain ⟨S,hS⟩ := cubicThetaRows_compact_below hε hK hpos
  refine ⟨S,fun p hp => ?_⟩
  apply tsum_eq_sum
  intro r hr
  exact hW _ (hS p hp r hr).le

lemma cubicThetaScalarWindow_continuousOn (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    ContinuousOn (cubicThetaScalarWindow W) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaScalarWindow_compact_sum W hε hW hK hKpos
  have he : cubicThetaScalarWindow W=ᶠ[𝓝 p]
      (fun q => ∑ r∈S,W (r.height q)) := by
    filter_upwards [hKn] with q hq
    exact hS q hq
  have hc : ContinuousAt (fun q => ∑ r∈S,W (r.height q)) p :=
    by
      clear hS he
      classical
      induction S using Finset.induction_on with
      | empty => simpa using (continuousAt_const (x:=p) (y:=(0:ℂ)))
      | @insert r S hr ih =>
        simp only [Finset.sum_insert hr]
        exact (W.continuous.continuousAt.comp (r.height_contDiffAt hp).continuousAt).add ih
  exact (hc.congr_of_eventuallyEq he).continuousWithinAt

def cubicThetaScalarQuotientWindow (W : C_c(ℝ,ℂ)) (q : CubicThetaQuotient) : ℂ :=
  cubicThetaScalarWindow W (cubicThetaQuotientLift q).val

lemma cubicThetaScalarQuotientWindow_apply (W : C_c(ℝ,ℂ)) (p : CubicThetaPoint) :
    cubicThetaScalarQuotientWindow W (cubicThetaQuotientMap p)=
      cubicThetaScalarWindow W p.val := by
  have he := cubicThetaQuotientLift_map (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaScalarQuotientWindow
  rw [←hg]
  exact cubicThetaScalarWindow_invariant W g p.property

lemma cubicThetaScalarQuotientWindow_continuous (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    Continuous (cubicThetaScalarQuotientWindow W) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  have he : cubicThetaScalarQuotientWindow W ∘ cubicThetaQuotientMap=
      fun p : CubicThetaPoint => cubicThetaScalarWindow W p.val :=
    funext (cubicThetaScalarQuotientWindow_apply W)
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro p
  exact ((cubicThetaScalarWindow_continuousOn W hε hW).continuousAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds p.property)).comp
      continuous_subtype_val.continuousAt

lemma cubicThetaScalarStripSeed_summable (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (p : CubicThetaPoint) :
    Summable (fun g : cubicThetaPrincipalGroup => cubicThetaFourierStripSeed 0 W (g • p)) := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaFourierStripSeed_compact 0 W hε hW
  have hs := (cubicTheta_compact_translates_locallyFinite hK).point_finite p
  apply summable_of_ne_finset_zero (s:=hs.toFinset)
  intro g hg
  by_contra hn
  exact hg (hs.mem_toFinset.mpr (hsub hn))

lemma cubicThetaScalarWindow_group_sum (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (p : CubicThetaPoint) :
    (∑' g : cubicThetaPrincipalGroup,cubicThetaFourierStripSeed 0 W (g • p))=
      cubicThetaScalarWindow W p.val := by
  let e : (CubicThetaBottomRow × Eisenstein) ≃ cubicThetaPrincipalGroup :=
    (Equiv.prodComm _ _).trans cubicThetaRowTranslationEquiv
  let f : cubicThetaPrincipalGroup → ℂ := fun g => cubicThetaFourierStripSeed 0 W (g • p)
  have hs : Summable (fun rw => f (e rw)) :=
    e.summable_iff.mpr (cubicThetaScalarStripSeed_summable W hε hW p)
  calc
    _ = ∑' rw : CubicThetaBottomRow × Eisenstein,f (e rw) := (e.tsum_eq f).symm
    _ = ∑' r : CubicThetaBottomRow,∑' w : Eisenstein,f (e (r,w)) := hs.tsum_prod
    _ = ∑' r : CubicThetaBottomRow,W (r.height p.val) := by
      apply tsum_congr
      intro r
      change (∑' w : Eisenstein,cubicThetaFourierStripSeed 0 W
        ((cubicThetaPrincipalTranslation w*r.completion) • p))=_
      simp_rw [mul_smul]
      rw [cubicThetaFourierStripSeed_translation_sum]
      have hh : (r.completion • p).val.2=r.height p.val := by
        change (cubicThetaBottomRow r.completion).height p.val=_
        rw [r.completion_row]
      rw [hh]
      simp [cubicThetaHorizontalCharacter,cubicThetaRowFrequency,tracePair]
    _ = _ := rfl

end CubicFirstMoment

end

end OAI
