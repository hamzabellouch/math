import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevDistribution
import OAI.Analysis.Conductivity.Variational.CentralEuclideanJets
import OAI.Analysis.Conductivity.Sobolev.LpExtension
import OAI.Analysis.Conductivity.Variational.SmoothNormalizedEndFamily
import OAI.Analysis.Conductivity.Variational.SmoothRepresentativeGluing

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma contDiffOn_local_global {g : R3 → ℝ} {U : Set R3}
    (hU : IsOpen U) (hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g U) {x : R3} (hx : x∈U) :
    ∃ (V : Set R3) (G : R3 → ℝ),IsOpen V ∧ x∈V ∧ V⊆U ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) G ∧ EqOn G g V := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  obtain ⟨χ,hχ,_,hχs,_,hχone⟩ := exists_smooth_core_cutoff isCompact_singleton
    Metric.isOpen_ball (Metric.isBounded_ball (x := x) (r := r))
    (singleton_subset_iff.mpr (Metric.mem_ball_self hr))
  have he : (fun y => χ y*g y)=ᶠ[𝓝 x] g := by
    filter_upwards [hχone x (mem_singleton x)] with y hy
    simp only [hy,one_mul]
  obtain ⟨V,hVs,hV,hxV⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hx) he)
  exact ⟨V,fun y => χ y*g y,hV,hxV,fun _ hy => (hVs hy).1,
    smooth_mul_of_support_in_open hU hg hχ (hχs.trans hball),fun _ hy => (hVs hy).2⟩

theorem weak_partial_of_contDiffOn_representative (f F : WholeL2) {U : Set R3}
    (hU : IsOpen U) (v : R3) (g : R3 → ℝ)
    (hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g U)
    (heq : (f : R3 → ℝ)=ᵐ[volume.restrict U] g)
    (hweak : ∀ ψ : R3 → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ⊆U → (∫ x,F x*ψ x)=-(∫ x,f x*fderiv ℝ ψ x v)) :
    ∀ᵐ x∂volume,x∈U → F x=fderiv ℝ g x v := by
  classical
  have hlocal (x : U) := contDiffOn_local_global hU hg x.property
  choose V G hV hxV hVU hG he using hlocal
  have hcover : (⋃ x : U,V x)=U := by
    apply Subset.antisymm (iUnion_subset (fun x => hVU x))
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩
  have hp (x : U) : ∀ᵐ y∂volume.restrict (V x),F y=fderiv ℝ g y v := by
    have heq' : (f : R3 → ℝ)=ᵐ[volume.restrict (V x)] G x := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (hVU x) heq,
        ae_restrict_mem (hV x).measurableSet] with y hy hyV
      exact hy.trans (he x hyV).symm
    have hw := weak_partial_of_smooth_representative f F (hV x) v (G x) (hG x) heq'
      (fun ψ hψ hc hsp => hweak ψ hψ hc (hsp.trans (hVU x)))
    filter_upwards [ae_restrict_of_ae hw,ae_restrict_mem (hV x).measurableSet] with y hy hyV
    rw [hy hyV]
    exact congrArg (fun D : R3 →L[ℝ] ℝ => D v)
      ((show G x=ᶠ[𝓝 y] g from Filter.Eventually.mono ((hV x).mem_nhds hyV) (fun t ht => he x ht)).fderiv_eq)
  have hh := ae_on_open_cover volume V hV (fun y => F y=fderiv ℝ g y v) hp
  rw [hcover] at hh
  exact (ae_restrict_iff' hU.measurableSet).mp hh

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma original_zero_pairing (f : Lp ℝ 2 ballMeasure) (ψ : R3 → ℝ) :
    (∫ x,lpZeroExtensionCLM (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) f x*ψ x)=
      ∫ x,f x*ψ x∂ballMeasure := by
  change _ = ∫ x in ball,f x*ψ x
  rw [←integral_indicator (show MeasurableSet ball from Metric.isOpen_ball.measurableSet)]
  apply integral_congr_ae
  filter_upwards [lpZeroExtensionCLM_ae (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) f] with x hx
  rw [hx]
  by_cases h : x∈ball
  · simp only [indicator_of_mem h]
    rfl
  · simp only [indicator_of_notMem h,zero_mul]

def originalWholeValue (u : H1) : WholeL2 :=
  lpZeroExtensionCLM (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) (weakValueL u)

def originalWholeDirection (u : H1) (v : R3) : WholeL2 :=
  lpZeroExtensionCLM (show MeasurableSet ball from Metric.isOpen_ball.measurableSet) (weakDirectionL v u)

lemma originalWholeValue_ae (u : H1) : originalWholeValue u=ᵐ[volume] ball.indicator (weakValue u) :=
  lpZeroExtensionCLM_ae_of_ae _ _ (weakValueL_apply_ae u)

lemma originalWholeDirection_ae (u : H1) (v : R3) :
    originalWholeDirection u v=ᵐ[volume] ball.indicator (fun x => inner ℝ v (weakGradient u x)) :=
  lpZeroExtensionCLM_ae_of_ae _ _ (weakDirectionL_apply_ae u v)

lemma originalWhole_weak_partial (u : H1) (v : R3) (ψ : R3 → ℝ)
    (hψ : ContDiff ℝ (↑(⊤:ℕ∞)) ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆ball) :
    (∫ x,originalWholeDirection u v x*ψ x)=
      -(∫ x,originalWholeValue u x*fderiv ℝ ψ x v) := by
  have he := weak_integration_by_parts u hψ hc hs v
  rw [L2.inner_def,L2.inner_def] at he
  change (∫ x,lpZeroExtensionCLM _ (weakDirectionL v u) x*ψ x)=
    -(∫ x,lpZeroExtensionCLM _ (weakValueL u) x*fderiv ℝ ψ x v)
  rw [original_zero_pairing,original_zero_pairing]
  have hv := (weakValueL_apply_ae (smoothH1 ψ hψ)).trans (smoothH1_value ψ hψ)
  have hd : (weakDirectionL v (smoothH1 ψ hψ) : R3 → ℝ)=ᵐ[ballMeasure]
      (fun x => fderiv ℝ ψ x v) := by
    filter_upwards [weakDirectionL_apply_ae (smoothH1 ψ hψ) v,smoothH1_gradient ψ hψ] with x hx hy
    simp only [hx,hy,inner_gradient_right,RCLike.conj_to_real]
  calc
    _ = ∫ x,inner ℝ (weakValueL (smoothH1 ψ hψ) x) (weakDirectionL v u x)∂ballMeasure := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      simp only [hx,Real.inner_apply,mul_comm]
    _ = _ := he
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hd] with x hx
      simp only [hx,Real.inner_apply,mul_comm]

theorem original_contDiffOn_representative_gradient (u : H1) {U : Set R3}
    (hU : IsOpen U) (hUb : U⊆ball) (g : R3 → ℝ)
    (hg : ContDiffOn ℝ (↑(⊤:ℕ∞)) g U)
    (heq : weakValue u=ᵐ[volume.restrict U] g) :
    ∀ᵐ x∂volume,x∈U → weakGradient u x=gradient g x := by
  have hf : (originalWholeValue u : R3 → ℝ)=ᵐ[volume.restrict U] g := by
    filter_upwards [ae_restrict_of_ae (originalWholeValue_ae u),heq,ae_restrict_mem hU.measurableSet] with x hx he hxU
    rw [hx,indicator_of_mem (hUb hxU),he]
  have hi (i : Fin 3) := weak_partial_of_contDiffOn_representative
    (originalWholeValue u) (originalWholeDirection u (EuclideanSpace.single i 1)) hU
    (EuclideanSpace.single i 1) g hg hf
    (fun ψ hψ hc hsp => originalWhole_weak_partial u _ ψ hψ hc (hsp.trans hUb))
  have hd (i : Fin 3) := originalWholeDirection_ae u (EuclideanSpace.single i 1)
  filter_upwards [ae_all_iff.mpr hi,ae_all_iff.mpr hd] with x hx hd hxU
  ext i
  have he := hx i hxU
  rw [hd i,indicator_of_mem (hUb hxU)] at he
  have hgr : inner ℝ (EuclideanSpace.single i 1) (gradient g x)=fderiv ℝ g x (EuclideanSpace.single i 1) := by
    simp only [inner_gradient_right,RCLike.conj_to_real]
  rw [←hgr] at he
  simpa only [EuclideanSpace.inner_single_left,RCLike.conj_to_real,one_mul] using he

end ScalarConductivity

end
end

end OAI
