import Mathlib
import OAI.Analysis.AffineBernstein.GraphBallArea
import OAI.Analysis.AffineBernstein.AmbientStraightening

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma triangular_graph_patch_area {n : ℕ} {Ω K : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcp : 0 < c) (v : Space n × ℝ) :
    (∫ y in {y | (triangularBaseEquiv M hc hcp.ne').symm (y-v.1) ∈ K},
       affineAreaDensity (triangularGraphFunction u M hc hcp.ne' v) y) =
      Real.rpow |M.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
        ∫ x in K, affineAreaDensity u x := by
  let P := triangularBaseEquiv M hc hcp.ne'
  let a := (triangularLinearHeight M).comp P.symm.toContinuousLinearMap
  have hi := affine_area_pullback_integral hΩ hu hp hK hKΩ
    P.symm (-P.symm v.1) a hcp (v.2-a v.1)
  change |(equivMatrix P.symm).det| * (∫ y in {y | P.symm y+(-P.symm v.1) ∈ K},
      affineAreaDensity (triangularGraphFunction u M hc hcp.ne' v) y) = _ at hi
  have he : {y | P.symm y+(-P.symm v.1) ∈ K} = {y | P.symm (y-v.1) ∈ K} := by
    ext y
    simp only [sub_eq_add_neg,mem_ofPred_eq,map_add,map_neg]
  rw [he,triangular_area_scaling M hc hcp] at hi
  apply mul_left_cancel₀ (abs_pos.mpr (equivMatrix_det_ne P.symm)).ne'
  exact hi.trans (by ring)

lemma triangularGraph_smooth_positive {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (M : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) {c : ℝ}
    (hc : M (0,1) = (0,c)) (hcp : 0 < c) (v : Space n × ℝ) :
    let Ω' := {y | (triangularBaseEquiv M hc hcp.ne').symm (y-v.1) ∈ Ω}
    let g := triangularGraphFunction u M hc hcp.ne' v
    IsOpen Ω' ∧ ContDiffOn ℝ ∞ g Ω' ∧ (∀ y ∈ Ω', (hessian g y).PosDef) := by
  let B := (triangularBaseEquiv M hc hcp.ne').symm
  let a := (triangularLinearHeight M).comp B.toContinuousLinearMap
  have he : {y | B (y-v.1) ∈ Ω} = affineBaseMap (equivMatrix B) (-B v.1) ⁻¹' Ω := by
    ext y
    simp only [mem_ofPred_eq,mem_preimage,affineBaseMap,toEuclideanCLM_equivMatrix,
      ContinuousLinearEquiv.coe_coe,sub_eq_add_neg,map_add,map_neg]
  change IsOpen {y | B (y-v.1) ∈ Ω} ∧
    ContDiffOn ℝ ∞ (cleGraphPullback u B (-B v.1) a c (v.2-a v.1)) {y | B (y-v.1) ∈ Ω} ∧ _
  rw [cleGraphPullback_eq,he]
  refine ⟨hΩ.preimage (contDiff_affineBaseMap _ _).continuous,
    contDiffOn_affineGraphPullback hu _ _ _ _ _,?_⟩
  intro y hy
  change (hessian (cleGraphPullback u B (-B v.1) a c (v.2-a v.1)) y).PosDef
  rw [cleGraphPullback_eq]
  exact posDef_hessian_affineGraphPullback hΩ hu hp (equivMatrix_det_ne B) (-B v.1) a hcp (v.2-a v.1) hy

lemma integral_affineAreaDensity_le_box_measurable {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    {R : ℝ} (hR : 0 ≤ R) (hxR : ∀ x ∈ K, ∀ j, |x j| ≤ R)
    (huR : ∀ x ∈ K, |u x| ≤ R) :
    (∫ x in K, affineAreaDensity u x) ≤ (graphAreaBoxBound n R).toReal := by
  have hcont : ContinuousOn (affineAreaDensity u) K := fun x hx =>
    (contDiffAt_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds (hKΩ hx)))
      (hp x (hKΩ hx))).continuousAt.continuousWithinAt
  have hnn : 0 ≤ᵐ[volume.restrict K] affineAreaDensity u := by
    filter_upwards [ae_restrict_mem hK] with x hx
    exact Real.rpow_nonneg (hp x (hKΩ hx)).det_pos.le _
  rw [integral_eq_lintegral_of_nonneg_ae hnn (hcont.aestronglyMeasurable hK)]
  exact ENNReal.toReal_mono (graphAreaBoxBound_ne_top n R)
    (graph_affine_area_in_box hΩ hc hK hKΩ hu hp hR hxR huR)

/-- Genuine affine area of every bounded measurable patch of an arbitrary
invertible affine image of the original convex graph. The constant depends
only on dimension and the physical coordinate radius, not on the affine map. -/
theorem affine_image_graph_area_in_box {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    {R : ℝ} (hR : 0 ≤ R)
    (hxR : ∀ x ∈ K, ∀ i, |(L (x,u x)+v).1 i| ≤ R)
    (htR : ∀ x ∈ K, |(L (x,u x)+v).2| ≤ R) :
    Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
      (∫ x in K, affineAreaDensity u x) ≤ (graphAreaBoxBound n (2*R)).toReal := by
  have he : L ((0 : Space n),1) ≠ 0 := by
    intro he
    have : ((0 : Space n),(1 : ℝ)) = 0 := L.injective (show L ((0 : Space n),1) = L 0 by simpa only [map_zero] using he)
    exact one_ne_zero (congrArg Prod.snd this)
  obtain ⟨A,c,hc,hAe,hAd,hAb⟩ := bounded_ambient_straightening he
  let M := L.trans A
  have hMc : M (0,1) = (0,c) := hAe
  let P := triangularBaseEquiv M hMc hc.ne'
  let Ω' : Set (Space n) := {y | P.symm (y-(A v).1) ∈ Ω}
  let K' : Set (Space n) := {y | P.symm (y-(A v).1) ∈ K}
  let g := triangularGraphFunction u M hMc hc.ne' (A v)
  have hreg := triangularGraph_smooth_positive hΩ hu hp M hMc hc (A v)
  have hΩ' : IsOpen Ω' := hreg.1
  have hg : ContDiffOn ℝ ∞ g Ω' := hreg.2.1
  have hgp : ∀ y ∈ Ω', (hessian g y).PosDef := hreg.2.2
  have hK' : MeasurableSet K' := hK.preimage (P.symm.continuous.comp (continuous_id.sub continuous_const)).measurable
  have hKΩ' : K' ⊆ Ω' := fun _ hy => hKΩ hy
  have hcv' : Convex ℝ Ω' := by
    intro x hx y hy a b ha hb hab
    change P.symm (a • x+b • y-(A v).1) ∈ Ω
    have heq : P.symm (a • x+b • y-(A v).1) =
        a • P.symm (x-(A v).1)+b • P.symm (y-(A v).1) := by
      rw [← map_smul,← map_smul,← map_add]
      congr 1
      calc
        _ = a • x+b • y-(a+b) • (A v).1 := by rw [hab,one_smul]
        _ = _ := by module
    rw [heq]
    exact hcv hx hy ha hb hab
  have himage (y : Space n) :
      M (P.symm (y-(A v).1),u (P.symm (y-(A v).1)))+A v = (y,g y) := by
    apply Prod.ext
    · change (M (_,u _)).1+(A v).1 = y
      rw [triangular_fst M hMc]
      change P (P.symm (y-(A v).1))+(A v).1 = y
      simp
    · rw [Prod.snd_add,triangular_snd M hMc]
      exact (triangularGraphFunction_eval u M hMc hc.ne' (A v) y).symm
  have hbox (y : Space n) (hy : y ∈ K') :
      (∀ i, |y i| ≤ 2*R) ∧ |g y| ≤ 2*R := by
    let x := P.symm (y-(A v).1)
    have hb := hAb hR (L (x,u x)+v) (hxR x hy) (htR x hy)
    have heq : A (L (x,u x)+v) = (y,g y) := by
      rw [map_add]
      exact himage y
    rwa [heq] at hb
  have hi := integral_affineAreaDensity_le_box_measurable hΩ' hcv' hK' hKΩ' hg hgp
    (mul_nonneg (by norm_num) hR) (fun y hy => (hbox y hy).1) (fun y hy => (hbox y hy).2)
  have har := triangular_graph_patch_area hΩ hu hp hK hKΩ M hMc hc (A v)
  have hd : |M.toContinuousLinearMap.det| = |L.toContinuousLinearMap.det| := by
    rw [show M = L.trans A from rfl,abs_det_trans,hAd,one_mul]
  rw [hd] at har
  exact har ▸ hi

end AffineBernstein
end

end OAI
