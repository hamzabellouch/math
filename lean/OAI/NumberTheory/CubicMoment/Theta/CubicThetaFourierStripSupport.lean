import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierStripSeed
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPoincareUnfolding

namespace OAI

/-! Compact support and absolute integrability of the half-open Fourier seed
at every positive height cutoff. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaFourierStripSeed_compact (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    ∃ K : Set CubicThetaPoint,IsCompact K ∧
      Function.support (cubicThetaFourierStripSeed h W)⊆K := by
  obtain ⟨L,hL,hcell⟩ := cubicThetaHorizontalCell_compact_container
  let B := tsupport W ∩ Ici ε
  have hB : IsCompact B := W.hasCompactSupport.inter_right isClosed_Ici
  have hpos : L ×ˢ B⊆{y : ℂ × ℝ | 0<y.2} := fun y hy => lt_of_lt_of_le hε hy.2.2
  have hi : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  refine ⟨cubicThetaPointInclusion.symm '' (L ×ˢ B),
    (hL.prod hB).image_of_continuousOn (hi.mono hpos),?_⟩
  intro p hp
  have hz : p.val.1∈cubicThetaHorizontalCell := by
    by_contra hn
    exact hp (by simp only [cubicThetaFourierStripSeed,ite_eq_right hn])
  have hw : W p.val.2≠0 := by
    intro hn
    exact hp (by simp only [cubicThetaFourierStripSeed,ite_eq_left hz,hn,zero_mul])
  refine ⟨p.val,⟨hcell hz,subset_tsupport W hw,?_⟩,?_⟩
  · exact (lt_of_not_ge (fun hv => hw (hW _ hv))).le
  · exact cubicThetaPointInclusion.left_inv (by rw [cubicThetaPointInclusion_source]; trivial)

lemma cubicThetaFourierStripSeed_mul_integrable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (g : CubicThetaPoint → ℂ) (hg : Continuous g) :
    Integrable (fun p => star (cubicThetaFourierStripSeed h W p)*g p)
      cubicThetaPointMeasure := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaFourierStripSeed_compact h W hε hW
  let f : CubicThetaPoint → ℂ := fun p =>
    star (W p.val.2*cubicThetaHorizontalCharacter h p.val.1)*g p
  have hf : Continuous f := by
    exact ((W.continuous.comp (continuous_snd.comp continuous_subtype_val)).mul
      ((cubicThetaHorizontalCharacter_continuous h).comp
        (continuous_fst.comp continuous_subtype_val))).star.mul hg
  let A : Set CubicThetaPoint := {p | p.val.1∈cubicThetaHorizontalCell}
  have hA : MeasurableSet A := cubicThetaHorizontalCell_measurable.preimage
    (measurable_fst.comp cubicThetaPointInclusion_measurableEmbedding.measurable)
  have he : (fun p => star (cubicThetaFourierStripSeed h W p)*g p)=
      A.indicator (K.indicator f) := by
    funext p
    by_cases ha : p.val.1∈cubicThetaHorizontalCell
    · by_cases hk : p∈K
      · simp [A,ha,hk,cubicThetaFourierStripSeed,f]
      · have hz : cubicThetaFourierStripSeed h W p=0 :=
          not_not.mp (fun hn => hk (hsub hn))
        simp [A,ha,hk,hz]
    · have hz : cubicThetaFourierStripSeed h W p=0 := ite_eq_right ha
      simp [A,ha,hz]

  rw [he]
  exact ((hf.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet).indicator hA

lemma cubicThetaFourierStripSeed_pair_integrable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection) :
    Integrable (fun p => star (cubicThetaFourierStripSeed h W p)*F.val p)
      cubicThetaPointMeasure :=
  cubicThetaFourierStripSeed_mul_integrable h W hε hW F.val F.val.continuous

lemma cubicThetaFourierStripSeed_pair_summable (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection)
    (p : CubicThetaPoint) :
    Summable (fun g : cubicThetaPrincipalGroup =>
      star (cubicThetaFourierStripSeed h W (g • p))*F.val (g • p)) := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaFourierStripSeed_compact h W hε hW
  have hs := (cubicTheta_compact_translates_locallyFinite hK).point_finite p
  apply summable_of_ne_finset_zero (s:=hs.toFinset)
  intro g hg
  have hgp : g • p∉K := fun hh => hg (hs.mem_toFinset.mpr hh)
  have hz : cubicThetaFourierStripSeed h W (g • p)=0 :=
    not_not.mp (fun hn => hgp (hsub hn))
  rw [hz,star_zero,zero_mul]

end CubicFirstMoment

end

end OAI
