import Mathlib
import OAI.Analysis.Conductivity.Branching.AttachedEndGradientL2
import OAI.Analysis.Conductivity.Geometry.CollarLip
import OAI.Analysis.Conductivity.Branching.AttachedCutLayer
import OAI.Analysis.Conductivity.Geometry.CollarInteriorFacts

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal

theorem smooth_attachedEnd_matched_H1 {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {q χ : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hc : HasCompactSupport χ) (hχb : ∀ x,|χ x|≤1)
    {a b η : ℝ} (ha : a≠0) (hη : 0<η) (hl : -(1:ℝ)/100≤b-η) (hr : b+η≤1/100)
    (hχs : tsupport χ⊆sourceClosedCollarBand (b-η) (b+η))
    (htrace : ∀ h,f.val 0 h=mFourierCoeff (fun θ => (q (sourceAngularCollar b θ):ℂ)) h)
    (g : SpectralL2 TorusModes) (hg : ∀ h,g h=(torusRate s h:ℂ)*f.val 0 h) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=cutMatchedValue (fun y => a*(sourceCollarTime y-b)) χ
        (fun y => (attachedEndPoissonField s f a b 0 y).re-q y) (WithLp.ofLp x) ∧
      ∀ i,weakGradient w x i=cutMatchedGradient (fun y => a*(sourceCollarTime y-b)) χ
        (fun y => (attachedEndPoissonField s f a b 0 y).re-q y)
        (fun y => fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y-fderiv ℝ q y)
        i (WithLp.ofLp x)) := by
  let τ : (Fin 3 → ℝ) → ℝ := fun y => a*(sourceCollarTime y-b)
  let p : (Fin 3 → ℝ) → ℝ := fun y => (attachedEndPoissonField s f a b 0 y).re-q y
  let F : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ :=
    fun y => fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y-fderiv ℝ q y
  let R := |a| *η
  let l := min b (b+R/a)
  let r := max b (b+R/a)
  let D := sourceClosedCollarBand l r
  have hR : 0≤R := (mul_pos (abs_pos.mpr ha) hη).le
  have hdiv : R/|a|=η := by dsimp [R]; field_simp
  obtain ⟨hlen,hleft,hright,hiff,hnear⟩ := affine_layer_interval (b:=b) ha hR
  have hl' : -(1:ℝ)/100≤l := by dsimp only [l]; rw [hdiv] at hleft; linarith
  have hr' : r≤(1:ℝ)/100 := by dsimp only [r]; rw [hdiv] at hright; linarith
  have hb : b∈Icc (-(1:ℝ)/100) (1/100) := ⟨by linarith,by linarith⟩
  have hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R := fun t ht => (hiff t).mp ht
  have hD : MeasurableSet D := (isCompact_sourceClosedCollarBand hl' hr').measurableSet
  have hDfull : D⊆sourceClosedCollarBand (-(1:ℝ)/100) (1/100) :=
    fun y hy => ⟨hl'.trans hy.1,hy.2.trans hr'⟩
  have hχfull : tsupport χ⊆sourceClosedCollarBand (-(1:ℝ)/100) (1/100) :=
    fun y hy => ⟨hl.trans (hχs hy).1,(hχs hy).2.trans hr⟩
  have htD : ∀ y∈tsupport χ,0<τ y → y∈D := by
    intro y hy ht
    apply (hiff _).mpr
    have hbound : |sourceCollarTime y-b|≤η := by
      apply abs_le.mpr
      constructor <;> linarith [(hχs hy).1,(hχs hy).2]
    refine ⟨ht.le,?_⟩
    calc
      a*(sourceCollarTime y-b) ≤ |a*(sourceCollarTime y-b)| := le_abs_self _
      _ = |a| *|sourceCollarTime y-b| := abs_mul _ _
      _ ≤ R := mul_le_mul_of_nonneg_left hbound (abs_nonneg a)
  have hp : MemLp p 2 (volume.restrict D) :=
    (attachedEndPoissonField_memLp s hs f ha hR min_le_max hl' hr' hT 0).re.sub
      (continuous_sourceBand_memLp hq.continuous hl' hr')
  obtain ⟨K,hK⟩ := attachedEndTime_lipschitz a b
  have hu := cutMatchedValue_memLp hK.continuous hχ.continuous hc hD hp htD
  apply localized_matched_seam_H1_pi hK hχ hc hD hp htD _ F _ _ (by norm_num : (5:ℝ)/2<3)
    (fun y hy => sourceBand_euclidean_bound (hχfull hy))
    (smooth_attachedEnd_cut_thin hs f hq hχb ha hη hl hr htrace g hg hu)
  · intro y hy ht
    exact (attachedEndPoissonField_localLip s hs f a b ht
      (sourceDirections_ne_zero_on_band (hχfull hy))).sub
      (localLipAt_of_contDiffAt (hq.of_le (by simp)).contDiffAt)
  · intro i
    exact (attachedEndPoisson_grad_memLp s hs f ha hR hb min_le_max hl' hr' hT i).sub
      (continuous_sourceBand_memLp ((hq.continuous_fderiv (by simp)).clm_apply continuous_const) hl' hr')
  · filter_upwards [ae_restrict_of_ae (attachedEndPoisson_real_differentiable_ae s hs f a b),
      ae_restrict_mem hD] with y hy hyD ht
    exact (hy (hDfull hyD) ht).hasFDerivAt.sub
      ((hq.differentiable (by simp)) y).hasFDerivAt

end ScalarConductivity

end

end OAI
