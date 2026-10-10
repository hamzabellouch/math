import Mathlib
import OAI.Analysis.Conductivity.Walls.LocalizedMatchedSeam
import OAI.Analysis.Conductivity.Geometry.CutSlopeGradient

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem cut_attachedEnd_H10 (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s))
    {a b l r R : ℝ} (ha : a≠0) (hR : 0≤R)
    (hb : b∈Icc (-(1:ℝ)/100) (1/100))
    (hlr : l≤r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (hpos : ∀ t∈Icc l r,0<a*(t-b))
    {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hc : HasCompactSupport χ) (hχs : tsupport χ⊆sourceClosedCollarBand l r) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=χ (WithLp.ofLp x)*(attachedEndPoissonField s f a b 0 (WithLp.ofLp x)).re ∧
      ∀ i,weakGradient w x i=
        fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)*
          (attachedEndPoissonField s f a b 0 (WithLp.ofLp x)).re+
        χ (WithLp.ofLp x)*fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re)
          (WithLp.ofLp x) (Pi.single i 1)) := by
  let D := sourceClosedCollarBand l r
  have hD : MeasurableSet D := measurableSet_Icc.preimage measurable_sourcePhysicalCoordinates.fst
  have hband {x : Fin 3 → ℝ} (hx : x∈D) :
      x∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) := ⟨hl.trans hx.1,hx.2.trans hr⟩
  let p := fun y => (attachedEndPoissonField s f a b 0 y).re
  have hp : MemLp p 2 (volume.restrict D) :=
    (attachedEndPoissonField_memLp s hs f ha hR hlr hl hr hT 0).re
  have hd : ∀ᵐ x∂volume.restrict D,0<(1:ℝ) → HasFDerivAt p (fderiv ℝ p x) x := by
    filter_upwards [ae_restrict_mem hD,
      ae_restrict_of_ae (attachedEndPoisson_real_differentiable_ae s hs f a b)] with x hx hdx _
    exact (hdx (hband hx) (hpos _ hx)).hasFDerivAt
  have hthin : Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*
      ∫ x in {x | 0<(1:ℝ) ∧ ((n:ℝ)+1)*(1:ℝ)≤2},
        (cutMatchedValue (fun _ => 1) χ p x)^2) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (3:ℕ)] with n hn
    have hn' : (3:ℝ)≤n := by exact_mod_cast hn
    have he : {x : Fin 3 → ℝ | 0<(1:ℝ) ∧ ((n:ℝ)+1)*(1:ℝ)≤2}=∅ := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,not_and]
      intro _
      linarith
    simp only [he,Measure.restrict_empty,integral_zero_measure,mul_zero]
  obtain ⟨w,hw,he⟩ := localized_matched_seam_H1_pi
    (LipschitzWith.const (1:ℝ)) hχ hc hD hp
    (fun x hx _ => hχs hx)
    (fun x hx _ => attachedEndPoissonField_localLip s hs f a b
      (hpos _ (hχs hx)) (sourceDirections_ne_zero_on_band (hband (hχs hx))))
    (fderiv ℝ p) (attachedEndPoisson_grad_memLp s hs f ha hR hb hlr hl hr hT)
    hd (show (5:ℝ)/2<3 by norm_num)
    (fun x hx => sourceBand_euclidean_bound (hband (hχs hx))) hthin
  refine ⟨w,hw,?_⟩
  simpa only [cutMatchedValue,cutMatchedGradient,show (0:ℝ)<1 by norm_num,ite_true,p] using he

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def fullAttachedEndValue (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (a b κ : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  (attachedEndPoissonField s f a b 0 y).re+κ*(a*(sourceCollarTime y-b))

def fullAttachedEndGradient (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (a b κ : ℝ) (y : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re) y (Pi.single i 1)+
    κ*fderiv ℝ (fun y => a*(sourceCollarTime y-b)) y (Pi.single i 1)

theorem cut_fullAttachedEnd_H10 (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ)
    {a b l r R : ℝ} (ha : a≠0) (hR : 0≤R)
    (hb : b∈Icc (-(1:ℝ)/100) (1/100))
    (hlr : l≤r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (hpos : ∀ t∈Icc l r,0<a*(t-b))
    {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hc : HasCompactSupport χ) (hχb : ∀ x,|χ x|≤1)
    (hχs : tsupport χ⊆sourceClosedCollarBand l r) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=χ (WithLp.ofLp x)*fullAttachedEndValue s f a b κ (WithLp.ofLp x) ∧
      ∀ i,weakGradient w x i=
        fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)*fullAttachedEndValue s f a b κ (WithLp.ofLp x)+
        χ (WithLp.ofLp x)*fullAttachedEndGradient s f a b κ (WithLp.ofLp x) i) := by
  obtain ⟨u,hu,he⟩ := cut_attachedEnd_H10 s hs f ha hR hb hlr hl hr hT hpos hχ hc hχs
  obtain ⟨v,hv,hve⟩ := compact_collar_slope_value_gradient hχ hc hχb ha hb κ l r hl hr hχs
  refine ⟨u+v,H10.add_mem hu hv,?_⟩
  filter_upwards [he,hve,weakValue_add u v,weakGradient_add u v] with x hx hy hv hg
  rw [hv,hg]
  simp only [Pi.add_apply,WithLp.ofLp_add]
  rw [hx.1,hy.1]
  constructor
  · by_cases h : WithLp.ofLp x∈tsupport χ
    · rw [max_eq_right (hpos _ (hχs h)).le]
      dsimp only [fullAttachedEndValue]
      ring
    · simp only [image_eq_zero_of_notMem_tsupport h,zero_mul,mul_zero,add_zero]
  · intro i
    simp only [hx.2 i,hy.2 i]
    by_cases h : WithLp.ofLp x∈tsupport χ
    · rw [max_eq_right (hpos _ (hχs h)).le,ite_eq_left (hpos _ (hχs h))]
      dsimp only [fullAttachedEndValue,fullAttachedEndGradient]
      ring
    · have hd : fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)=0 :=
        image_eq_zero_of_notMem_tsupport (f:=fun y => fderiv ℝ χ y (Pi.single i 1))
          (fun hh => h (tsupport_fderiv_apply_subset ℝ _ hh))
      simp only [image_eq_zero_of_notMem_tsupport h,hd,zero_mul,mul_zero,add_zero]

lemma exists_band_cutoff {l₀ l r r₀ : ℝ} (hl : l₀<l) (hr : r<r₀)
    (hl₀ : -(1:ℝ)/100≤l₀) (hr₀ : r₀≤1/100) :
    ∃ χ : (Fin 3 → ℝ) → ℝ,ContDiff ℝ (↑(⊤:ℕ∞)) χ ∧ HasCompactSupport χ ∧
      (∀ x,|χ x|≤1) ∧ tsupport χ⊆sourceClosedCollarBand l₀ r₀ ∧
      (∀ x∈sourceClosedCollarBand l r,χ=ᶠ[𝓝 x] (fun _ => 1)) := by
  have hbig := isCompact_sourceClosedCollarBand hl₀ hr₀
  have hsmall := isCompact_sourceClosedCollarBand (hl₀.trans hl.le) (hr.le.trans hr₀)
  have hi : sourceClosedCollarBand l r⊆interior (sourceClosedCollarBand l₀ r₀) := by
    intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    have hm := locallyLipschitz_sourceCollarTime.continuous.continuousAt
      (isOpen_Ioo.mem_nhds (show sourceCollarTime x∈Ioo l₀ r₀ from
        ⟨hl.trans_le hx.1,hx.2.trans_lt hr⟩))
    exact mem_of_superset hm (fun y hy => ⟨hy.1.le,hy.2.le⟩)
  obtain ⟨χ,hχ1,hχ0,hχb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Fin 3 → ℝ)) hsmall.isClosed hi (n:=↑(⊤:ℕ∞))
  refine ⟨χ,χ.contMDiff.contDiff,HasCompactSupport.intro hbig hχ0,?_,?_,?_⟩
  · intro x
    rw [abs_of_nonneg (hχb x).1]
    exact (hχb x).2
  · apply closure_minimal _ hbig.isClosed
    intro x hx
    by_contra hn
    exact hx (hχ0 x hn)
  · intro x hx
    exact hχ1.filter_mono (nhds_le_nhdsSet hx)

theorem fullAttachedEnd_neighborhood_H10 (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ)
    {a b l₀ l r r₀ R : ℝ} (ha : a≠0) (hR : 0≤R)
    (hb : b∈Icc (-(1:ℝ)/100) (1/100))
    (hlr : l≤r) (hl : l₀<l) (hr : r<r₀)
    (hl₀ : -(1:ℝ)/100≤l₀) (hr₀ : r₀≤1/100)
    (hT : ∀ t∈Icc l₀ r₀,affineEndTime a b t∈Icc 0 R)
    (hpos : ∀ t∈Icc l₀ r₀,0<a*(t-b)) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      WithLp.ofLp x∈sourceClosedCollarBand l r →
      weakValue w x=fullAttachedEndValue s f a b κ (WithLp.ofLp x) ∧
      ∀ i,weakGradient w x i=fullAttachedEndGradient s f a b κ (WithLp.ofLp x) i) := by
  obtain ⟨χ,hχ,hc,hχb,hχs,hχ1⟩ := exists_band_cutoff hl hr hl₀ hr₀
  obtain ⟨w,hw,he⟩ := cut_fullAttachedEnd_H10 s hs f κ ha hR hb
    (hl.le.trans (hlr.trans hr.le)) hl₀ hr₀ hT hpos hχ hc hχb hχs
  refine ⟨w,hw,?_⟩
  filter_upwards [he] with x hx hm
  have heq := hχ1 _ hm
  have hone := heq.self_of_nhds
  have hd : fderiv ℝ χ (WithLp.ofLp x)=0 := by
    rw [heq.fderiv_eq]
    exact fderiv_const_apply (1:ℝ)
  simpa only [hone,hd,_root_.zero_apply,one_mul,zero_mul,zero_add] using hx

end ScalarConductivity

end

end OAI
