import OAI.Geometry.SurfaceImmersion.Geometry.MetricAcceleration
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartGeometry

namespace OAI

/-! The positive intrinsic phase Hessian gives negative first-coordinate
acceleration in the actual nonlinear phase chart. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame PhaseGeometry

lemma induced_connection_slots {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (i : Fin 3) :
    metricConnectionAt (inducedCoordinateMetric F p,fderiv ℝ (inducedCoordinateMetric F) p) i =
      let X := coordDeriv dx F p
      let Y := coordDeriv dy F p
      let C := (![coordDeriv dx (coordDeriv dx F) p,
        coordDeriv dx (coordDeriv dy F) p,coordDeriv dy (coordDeriv dy F) p] : Fin 3 → RVec 4) i
      (((Y ⬝ᵥ Y)*(X ⬝ᵥ C)-(X ⬝ᵥ Y)*(Y ⬝ᵥ C))/gramDet X Y,
       ((X ⬝ᵥ X)*(Y ⬝ᵥ C)-(X ⬝ᵥ Y)*(X ⬝ᵥ C))/gramDet X Y) := by
  have hcomm := real_second_coordDeriv_comm hF p dy dx
  fin_cases i <;>
    simp only [metricConnectionAt, metricJetDet, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals
    simp only [inducedCoordinateMetric_derivative hF]
    simp only [inducedCoordinateMetric, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    simp only [realMetric_partial hF, hcomm]
    simp only [realMetric, NormalFrame.gramDet, dotProduct_comm]
    congr 1 <;> congr 1 <;> ring

lemma second_connection_decomposition {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) :
    let Gamma := metricConnectionAt (inducedCoordinateMetric F p,fderiv ℝ (inducedCoordinateMetric F) p)
    coordDeriv v (coordDeriv w F) p =
      fderiv ℝ F p (connectionContract Gamma v w) + realSecondForm F v w p := by
  dsimp only
  have hb (i : Fin 3) :
      (![coordDeriv dx (coordDeriv dx F) p,coordDeriv dx (coordDeriv dy F) p,
        coordDeriv dy (coordDeriv dy F) p] : Fin 3 → RVec 4) i =
      fderiv ℝ F p
        (metricConnectionAt (inducedCoordinateMetric F p,fderiv ℝ (inducedCoordinateMetric F) p) i) +
      realSecondTensor F p i := by
    rw [induced_connection_slots hF p i]
    change _ = coordDeriv _ F p + _
    conv_rhs => lhs; rw [coordDeriv_eq_basis]
    fin_cases i <;> simp only [realSecondTensor,Matrix.cons_val_zero',Matrix.cons_val_succ',
      realSecondForm,realNormalPart] <;> abel
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  change coordDeriv dx (coordDeriv dx F) p = _ at h0
  change coordDeriv dx (coordDeriv dy F) p = _ at h1
  change coordDeriv dy (coordDeriv dy F) p = _ at h2
  rw [second_coordDeriv_bilinear hF,h0,h1,h2,connectionContract,map_add,map_add,
    map_smul,map_smul,map_smul,realSecondForm_bilinear hF]
  simp only [realSecondTensor]
  module

lemma scalar_second_coordDeriv_comp {phi : Base → ℝ} {f : Base → Base}
    (hphi : ContDiff ℝ ∞ phi) (hf : ContDiff ℝ ∞ f) (v w p : Base) :
    coordDeriv v (coordDeriv w (phi ∘ f)) p =
      coordDeriv (fderiv ℝ f p v) (coordDeriv (fderiv ℝ f p w) phi) (f p) +
      fderiv ℝ phi (f p) (coordDeriv v (coordDeriv w f) p) := by
  have hDF : ContDiff ℝ ∞ (fderiv ℝ phi) := hphi.fderiv_right (m := ∞) (by simp)
  have hD1 := ((hDF.differentiable (by simp)) (f p)).hasFDerivAt.comp p
    ((hf.differentiable (by simp)) p).hasFDerivAt
  have hD2 := (((hf.fderiv_right (m := ∞) (by simp)).clm_apply
      (show ContDiff ℝ ∞ (fun _ : Base => w) from contDiff_const)).differentiable
    (by simp) p).hasFDerivAt
  have hp := hD1.clm_apply hD2
  have he : (fun q => (fderiv ℝ phi ∘ f) q (coordDeriv w f q)) = coordDeriv w (phi ∘ f) := by
    funext q
    simp only [coordDeriv,fderiv_comp q (hphi.differentiable (by simp) _) (hf.differentiable (by simp) _),
      ContinuousLinearMap.comp_apply,Function.comp_apply]
  change HasFDerivAt (fun q => (fderiv ℝ phi ∘ f) q (coordDeriv w f q)) _ p at hp
  rw [he] at hp
  have heval := congrArg (fun L => L v) hp.fderiv
  have hsecond := (((hDF.differentiable (by simp)) (f p)).hasFDerivAt.clm_apply
    (hasFDerivAt_const (fderiv ℝ f p w) (f p))).fderiv
  change fderiv ℝ (fun q => fderiv ℝ phi q (fderiv ℝ f p w)) (f p) = _ at hsecond
  change fderiv ℝ (coordDeriv (fderiv ℝ f p w) phi) (f p) = _ at hsecond
  change fderiv ℝ (coordDeriv w (phi ∘ f)) p v =
    fderiv ℝ (coordDeriv (fderiv ℝ f p w) phi) (f p) (fderiv ℝ f p v) +
    fderiv ℝ phi (f p) (fderiv ℝ (fun x => fderiv ℝ f x w) p v)
  rw [hsecond]
  simpa only [coordDeriv,add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    zero_apply,map_zero,zero_add,add_zero,Function.comp_apply,add_comm] using heval

lemma phase_chart_connection_identity {F : RField 4} {f : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hf : ContDiff ℝ ∞ f) (p : Base)
    (hImm : Function.Injective (fderiv ℝ F (f p)))
    (hdet : coordDet (fderiv ℝ f p) ≠ 0) :
    let oldGamma := metricConnectionAt (inducedCoordinateMetric F (f p),
      fderiv ℝ (inducedCoordinateMetric F) (f p))
    let newGamma := metricConnectionAt (inducedCoordinateMetric (F ∘ f) p,
      fderiv ℝ (inducedCoordinateMetric (F ∘ f)) p) 2
    fderiv ℝ f p newGamma = coordDeriv dy (coordDeriv dy f) p +
      connectionContract oldGamma (fderiv ℝ f p dy) (fderiv ℝ f p dy) := by
  dsimp only
  apply hImm
  have hD := gramDet_ne_zero_of_injective _ hImm
  have hs := second_coordDeriv_comp_smooth hF hf dy dy p
  rw [second_connection_decomposition hF] at hs
  have hn := second_connection_decomposition (hF.comp hf) p dy dy
  simp only [connectionContract,dy,zero_mul,one_mul,mul_zero,add_zero,zero_add,
    zero_smul,one_smul] at hn
  change coordDeriv dy (coordDeriv dy (F ∘ f)) p =
    fderiv ℝ (F ∘ f) p
      (metricConnectionAt (inducedCoordinateMetric (F ∘ f) p,
        fderiv ℝ (inducedCoordinateMetric (F ∘ f)) p) 2) +
      realSecondForm (F ∘ f) dy dy p at hn
  rw [realSecondForm_comp_smooth hF hf dy dy p hD hdet] at hn
  have he := hn.symm.trans hs
  rw [fderiv_comp p (hF.differentiable (by simp) _) (hf.differentiable (by simp) _),
    ContinuousLinearMap.comp_apply] at he
  rw [map_add]
  apply add_right_cancel (b := realSecondForm F (fderiv ℝ f p dy) (fderiv ℝ f p dy) (f p))
  exact he.trans (by abel)

lemma phase_chart_hessian_dy {F : RField 4} {phi : Base → ℝ} {f : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hphi : ContDiff ℝ ∞ phi) (hf : ContDiff ℝ ∞ f)
    (p : Base) (hphase : phi ∘ f =ᶠ[𝓝 p] Prod.fst)
    (hImm : Function.Injective (fderiv ℝ F (f p)))
    (hdet : coordDet (fderiv ℝ f p) ≠ 0) :
    coordinateMetricHessian (inducedCoordinateMetric (F ∘ f)) Prod.fst p dy dy =
      coordinateMetricHessian (inducedCoordinateMetric F) phi (f p)
        (fderiv ℝ f p dy) (fderiv ℝ f p dy) := by
  let a := fderiv ℝ f p dy
  let oldGamma := metricConnectionAt (inducedCoordinateMetric F (f p),
      fderiv ℝ (inducedCoordinateMetric F) (f p))
  let newGamma := metricConnectionAt (inducedCoordinateMetric (F ∘ f) p,
      fderiv ℝ (inducedCoordinateMetric (F ∘ f)) p) 2
  have hd : (fderiv ℝ phi (f p)).comp (fderiv ℝ f p) = ContinuousLinearMap.fst ℝ ℝ ℝ := by
    rw [← fderiv_comp p (hphi.differentiable (by simp) _) (hf.differentiable (by simp) _),
      hphase.fderiv_eq,fderiv_fst]
  have hs : coordDeriv dy (coordDeriv dy (phi ∘ f)) p = 0 := by
    have he : coordDeriv dy (phi ∘ f) =ᶠ[𝓝 p] coordDeriv dy Prod.fst := by
      filter_upwards [hphase.eventuallyEq_nhds] with x hx
      exact congrArg (fun L : Base →L[ℝ] ℝ => L dy) hx.fderiv_eq
    rw [coordDeriv,he.fderiv_eq]
    change coordDeriv dy (coordDeriv dy Prod.fst) p = 0
    have he : coordDeriv dy (Prod.fst : Base → ℝ) = fun _ => 0 := by
      funext q
      simp [coordDeriv,fderiv_fst,dy]
    rw [he]
    simp [coordDeriv]
  rw [scalar_second_coordDeriv_comp hphi hf] at hs
  have hc := phase_chart_connection_identity hF hf p hImm hdet
  change fderiv ℝ f p newGamma = _ + connectionContract oldGamma a a at hc
  have hp := congrArg (fderiv ℝ phi (f p)) hc
  rw [map_add] at hp
  have hn : fderiv ℝ phi (f p) (fderiv ℝ f p newGamma) = newGamma.1 := by
    change ((fderiv ℝ phi (f p)).comp (fderiv ℝ f p)) newGamma = _
    rw [hd]
    rfl
  rw [hn] at hp
  rw [coordinateMetricHessian_fst_dy,coordinateMetricHessian,
    phaseLinear_phaseDerivative]
  change -newGamma.1 = coordDeriv a (coordDeriv a phi) (f p) -
    fderiv ℝ phi (f p) (connectionContract oldGamma a a)
  change coordDeriv a (coordDeriv a phi) (f p) + _ = 0 at hs
  linarith

/-- A convex phase gives the negative tangential coefficient required by
`exists_projected_collar_frame`, in the actual smooth inverse phase chart. -/
theorem negative_acceleration_in_phase_chart {F : RField 4} {phi : Base → ℝ}
    (hF : ContDiff ℝ ∞ F) (hphi : ContDiff ℝ ∞ phi)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hphase : ∀ x, (e x).1 = phi x)
    (hImm : ∀ x ∈ e.source, Function.Injective (fderiv ℝ F x))
    (hHess : ∀ x ∈ e.source, ∀ v : Base, v ≠ 0 →
      0 < coordinateMetricHessian (inducedCoordinateMetric F) phi x v v)
    {p : Base} (hp : p ∈ e.target) :
    ∃ mu nu : ℝ, mu < 0 ∧ coordDeriv dy (coordDeriv dy (F ∘ e.symm)) p =
      mu • coordDeriv dx (F ∘ e.symm) p + nu • coordDeriv dy (F ∘ e.symm) p +
        realSecondForm (F ∘ e.symm) dy dy p := by
  have hcomp : phi ∘ e.symm =ᶠ[𝓝 p] Prod.fst := by
    filter_upwards [e.open_target.mem_nhds hp] with x hx
    change phi (e.symm x) = x.1
    rw [← hphase,e.right_inv hx]
  have hdet : coordDet (fderiv ℝ e.symm p) ≠ 0 :=
    coordDet_fderiv_ne_zero_of_local_inverse e.open_target e.open_source
      hi.contDiffOn he.contDiffOn (fun _ hx => e.map_target hx) (fun x hx => e.right_inv hx) hp
  apply negative_acceleration_of_positive_hessian (hF.comp hi) p
  rw [phase_chart_hessian_dy hF hphi hi p hcomp (hImm _ (e.map_target hp)) hdet]
  apply hHess _ (e.map_target hp)
  intro hz
  have hzero := inverse_chart_derivative_injective e he hi hp
    (hz.trans (map_zero (fderiv ℝ e.symm p)).symm)
  have hy : (dy : Base) ≠ 0 := by simp [dy]
  exact hy hzero

end ClosedSurfaceR4.RealModes

end

end OAI
