import OAI.Geometry.NodalSets.Charts.AdaptedChartFamilyLemmas
import OAI.Geometry.NodalSets.Elliptic.EnvelopeContactJet

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma form_derivative_zero (G : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hG : DifferentiableAt ℝ G 0)
    (hz : ∀ u v, fderiv ℝ (fun x ↦ G x u v) 0 = 0) : fderiv ℝ G 0 = 0 := by
  ext w u v
  have hd := (hG.hasFDerivAt.clm_apply (hasFDerivAt_const u 0)).clm_apply (hasFDerivAt_const v 0)
  have hh := congrArg (fun L : Coord →L[ℝ] ℝ ↦ L w) (hz u v)
  rw [hd.fderiv] at hh
  simpa using hh

lemma inverse_fderiv_zero
    (G : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : Coord ≃L[ℝ] Coord →L[ℝ] ℝ) (he : G 0 = e.toContinuousLinearMap)
    (hG : DifferentiableAt ℝ G 0) (hz : fderiv ℝ G 0 = 0) :
    DifferentiableAt ℝ (fun x ↦ ContinuousLinearMap.inverse (G x)) 0 ∧
    fderiv ℝ (fun x ↦ ContinuousLinearMap.inverse (G x)) 0 = 0 := by
  have hi : DifferentiableAt ℝ
      (ContinuousLinearMap.inverse : (Coord →L[ℝ] Coord →L[ℝ] ℝ) → ((Coord →L[ℝ] ℝ) →L[ℝ] Coord)) (G 0) := by
    rw [he]
    exact (contDiffAt_map_inverse (n := (1:ℕ∞ω)) e).differentiableAt (by norm_num)
  constructor
  · exact hi.comp (0:Coord) hG
  · change fderiv ℝ (ContinuousLinearMap.inverse ∘ G) 0 = 0
    rw [fderiv_comp (0:Coord) hi hG, hz, ContinuousLinearMap.comp_zero]

lemma orthonormal_inverse_axis (G : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < G v v)
    (he : ∀ i j : Fin 4, G (Pi.single i 1) (Pi.single j 1) = if i=j then 1 else 0)
    (j : Fin 4) : ContinuousLinearMap.inverse G (ContinuousLinearMap.proj j) = Pi.single j 1 := by
  have hi : ContinuousLinearMap.inverse G = (positiveMetricEquiv G hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv G hp)
  rw [hi]
  apply (positiveMetricEquiv G hp).injective
  rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  ext x
  have hx : G (Pi.single j 1) x = x j := by
    conv_lhs => arg 2; rw [coord_expansion x]
    simp [map_sum, he, mul_ite]
  exact hx.symm

lemma pulledForm_slice_smooth
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g) (p : QuadParam Coord) :
    ContDiff ℝ ∞ (pulledForm g p) := by
  have hpair : ContDiff ℝ ∞ (fun x : Coord ↦ (p,x)) := contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def, Function.uncurry_def] using
    (pulledForm_smooth (E := Coord) g hg).comp hpair

def inverseChartCoeff (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (y : Coord) (e : Coord ≃L[ℝ] Coord) (i j : Fin 4) (x : Coord) : ℝ :=
  (ContinuousLinearMap.inverse
    (pulledForm g (y,e.toContinuousLinearMap,actualFrameConnection g y e) x)
    (ContinuousLinearMap.proj j)) i

theorem actual_inverse_metric_normal_jets
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (y : Coord) (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) :
    (∀ i j, inverseChartCoeff g y e i j 0 = if i=j then 1 else 0) ∧
    ∀ i j, fderiv ℝ (inverseChartCoeff g y e i j) 0 = 0 := by
  let G := pulledForm g (y,e.toContinuousLinearMap,actualFrameConnection g y e)
  have hG : ContDiff ℝ ∞ G := pulledForm_slice_smooth g hg _
  have hv (u v : Coord) : G 0 u v = g y (e u) (e v) := pullbackMetric_quadratic_zero g y e _ u v
  have hpos : ∀ v, v ≠ 0 → 0 < G 0 v v := by
    intro v hv0
    rw [hv]
    exact hp y (e v) (by intro hz; exact hv0 (e.injective (by simpa using hz)))
  have hnormal : ∀ i j : Fin 4, G 0 (Pi.single i 1) (Pi.single j 1) = if i=j then 1 else 0 := by
    intro i j
    rw [hv]
    exact he i j
  have hz : fderiv ℝ G 0 = 0 := form_derivative_zero G (hG.differentiable (by simp) 0)
    (fun u v ↦ actualMetricChart_metric_first_zero g hg hs hp y e u v)
  obtain ⟨hi,hzi⟩ := inverse_fderiv_zero G (positiveMetricEquiv (G 0) hpos) rfl
    (hG.differentiable (by simp) 0) hz
  constructor
  · intro i j
    change (ContinuousLinearMap.inverse (G 0) (ContinuousLinearMap.proj j)) i = _
    rw [orthonormal_inverse_axis (G 0) hpos hnormal]
    simp [Pi.single_apply]
  · intro i j
    have h := (ContinuousLinearMap.proj i : Coord →L[ℝ] ℝ).hasFDerivAt.comp (0:Coord)
      (hi.hasFDerivAt.clm_apply (hasFDerivAt_const (ContinuousLinearMap.proj j : Coord →L[ℝ] ℝ) (0:Coord)))
    change fderiv ℝ ((ContinuousLinearMap.proj i : Coord →L[ℝ] ℝ) ∘
      (fun x ↦ ContinuousLinearMap.inverse (G x) (ContinuousLinearMap.proj j : Coord →L[ℝ] ℝ))) 0 = 0
    rw [h.fderiv]
    simp only [hzi, ContinuousLinearMap.comp_zero, zero_add]
    ext v
    simp

end
end Yau.Geometry

end OAI
