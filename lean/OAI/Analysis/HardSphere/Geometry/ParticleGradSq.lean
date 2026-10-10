import Mathlib
import OAI.Analysis.HardSphere.Geometry.RadialIndicator

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open Filter
open scoped Topology BigOperators

def particleGradSq {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (Fin n → Point) → E) (i : Fin n) (X : Fin n → Point) : ℝ :=
  ‖fderiv ℝ F X (Pi.single i axis0)‖^2+
  ‖fderiv ℝ F X (Pi.single i axis1)‖^2+
  ‖fderiv ℝ F X (Pi.single i axis2)‖^2

lemma insertNth_affine {n : ℕ} (i : Fin (n+1)) (Y : Fin n → Point) (x : Point) :
    i.insertNth x Y=(ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) ↦ Point) i) x+i.insertNth 0 Y := by
  funext k
  induction k using i.succAboveCases with
  | x => simp
  | p k => simp [Fin.succAbove_ne]

lemma contDiff_coordinate_slice {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F) (i : Fin (n+1)) (Y : Fin n → Point) :
    ContDiff ℝ 1 (fun x ↦ F (i.insertNth x Y)) := by
  have he : (fun x : Point ↦ i.insertNth x Y)=fun x ↦
      (ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) ↦ Point) i) x+i.insertNth 0 Y := funext (insertNth_affine i Y)
  change ContDiff ℝ 1 (F ∘ fun x : Point ↦ i.insertNth x Y)
  rw [he]
  exact hF.comp ((ContinuousLinearMap.contDiff _).add contDiff_const)

lemma fderiv_coordinate_slice {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F)
    (i : Fin (n+1)) (Y : Fin n → Point) (x : Point) :
    fderiv ℝ (fun z ↦ F (i.insertNth z Y)) x=
      (fderiv ℝ F (i.insertNth x Y)).comp (ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) ↦ Point) i) := by
  have hi : HasFDerivAt (fun z : Point ↦ i.insertNth z Y)
      (ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) ↦ Point) i) x := by
    have he : (fun x : Point ↦ i.insertNth x Y)=fun x ↦
        (ContinuousLinearMap.single ℝ (fun _ : Fin (n+1) ↦ Point) i) x+i.insertNth 0 Y := funext (insertNth_affine i Y)
    rw [he]
    exact (ContinuousLinearMap.hasFDerivAt _).add_const _
  have hf := ((hF.differentiable (by norm_num) (i.insertNth x Y)).hasFDerivAt).comp x hi
  simpa only [Function.comp_def] using hf.fderiv

lemma gradSq_coordinate_slice {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F)
    (i : Fin (n+1)) (Y : Fin n → Point) (x : Point) :
    gradSq (fun z ↦ F (i.insertNth z Y)) x=particleGradSq F i (i.insertNth x Y) := by
  simp only [gradSq,fderiv_coordinate_slice hF,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.single_apply,particleGradSq]

lemma continuous_particleGradSq {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin n → Point) → E} (hF : ContDiff ℝ 1 F) (i : Fin n) :
    Continuous (particleGradSq F i) := by
  have hd := hF.continuous_fderiv (by norm_num)
  unfold particleGradSq
  exact (((hd.clm_apply continuous_const).norm.pow 2).add
    ((hd.clm_apply continuous_const).norm.pow 2)).add
    ((hd.clm_apply continuous_const).norm.pow 2)

lemma lintegral_insertNth {n : ℕ} (μ : Fin (n+1) → Measure Point) [∀i,SigmaFinite (μ i)]
    (i : Fin (n+1)) (H : (Fin (n+1) → Point) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ X, H X ∂Measure.pi μ)=
      ∫⁻ Y, ∫⁻ x, H (i.insertNth x Y) ∂μ i ∂Measure.pi (fun j ↦ μ (i.succAbove j)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Point) i
  have he := (measurePreserving_piFinSuccAbove μ i).symm
  rw [← he.lintegral_comp_emb e.symm.measurableEmbedding H]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Equiv.coe_fn_mk]
  apply lintegral_prod_symm
  exact (hH.comp e.symm.measurable).aemeasurable

lemma sector_coordinate_capacity {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n+1) → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0<r) (hl : 0≤l) (b : Fin (n+1) → Point)
    (i : Fin (n+1)) (j : Fin n) (hb : b (i.succAbove j)=b i)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c)≤r^2 → F X=0) :
    (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun a ↦ volume.restrict (cube (b a) l))) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*
        (∫⁻ X, ENNReal.ofReal (particleGradSq F i X) ∂Measure.pi (fun a ↦ volume.restrict (cube (b a) l))) := by
  have hm : Measurable (fun X ↦ ENNReal.ofReal (‖F X‖^2)) := by
    simpa only [Pi.pow_apply] using (hF.continuous.norm.pow 2).measurable.ennreal_ofReal
  rw [lintegral_insertNth _ i _ hm,lintegral_insertNth _ i _ (continuous_particleGradSq hF i).measurable.ennreal_ofReal,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  have hae : ∀ᵐ Y ∂Measure.pi (fun a : Fin n ↦ volume.restrict (cube (b (i.succAbove a)) l)),
      Y j∈cube (b (i.succAbove j)) l :=
    Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem isClosed_Icc.measurableSet)
  filter_upwards [hae] with Y hY
  rw [hb] at hY
  have h := cube_capacity (contDiff_coordinate_slice hF i Y) hr hl hY (by
    intro x hx
    apply hz (i.insertNth x Y) i (i.succAbove j) (Fin.ne_succAbove i j)
    simpa only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove] using hx)
  simp_rw [gradSq_coordinate_slice hF] at h
  exact h

end HardSphere.SphericalCoordinates

end

end OAI
