import Mathlib.Analysis.SpecialFunctions.Sqrt
import OAI.Geometry.NodalSets.Charts.PositiveMetric

namespace OAI

namespace Yau.Geometry
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def metricNormalize (g : E →L[ℝ] E →L[ℝ] ℝ) (v : E) : E :=
  (Real.sqrt (g v v))⁻¹ • v

lemma metricNormalize_unit (g : E →L[ℝ] E →L[ℝ] ℝ) (v : E) (hv : 0 < g v v) :
    g (metricNormalize g v) (metricNormalize g v) = 1 := by
  have hr : Real.sqrt (g v v) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  have hh := Real.sq_sqrt hv.le
  simp only [metricNormalize, map_smul, smul_apply, smul_eq_mul]
  field_simp
  nlinarith

lemma metricNormalize_fixed (g : E →L[ℝ] E →L[ℝ] ℝ) (v : E) (hv : g v v = 1) :
    metricNormalize g v = v := by simp [metricNormalize, hv]

lemma metricNormalize_orthogonal (g : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) (huv : g u v = 0) :
    g u (metricNormalize g v) = 0 := by simp [metricNormalize, huv]

variable {ι : Type*} [Fintype ι]
def removeFrame (g : E →L[ℝ] E →L[ℝ] ℝ) (e : ι → E) (v : E) : E :=
  v - ∑ i, g (e i) v • e i

lemma removeFrame_orthogonal [DecidableEq ι] (g : E →L[ℝ] E →L[ℝ] ℝ) (e : ι → E)
    (he : ∀ i j, g (e i) (e j) = if i = j then 1 else 0) (v : E) (i : ι) :
    g (e i) (removeFrame g e v) = 0 := by
  classical
  simp [removeFrame, map_sum, he, mul_ite]

lemma removeFrame_fixed (g : E →L[ℝ] E →L[ℝ] ℝ) (e : ι → E) (v : E)
    (hv : ∀ i, g (e i) v = 0) : removeFrame g e v = v := by simp [removeFrame, hv]

variable {T : Type*} [TopologicalSpace T]
lemma metricNormalize_continuousAt (g : T → E →L[ℝ] E →L[ℝ] ℝ) (v : T → E) {t : T}
    (hg : ContinuousAt g t) (hv : ContinuousAt v t) (hpos : 0 < g t (v t) (v t)) :
    ContinuousAt (fun s ↦ metricNormalize (g s) (v s)) t := by
  exact (((hg.clm_apply hv).clm_apply hv).sqrt.inv₀
    (ne_of_gt (Real.sqrt_pos.mpr hpos))).smul hv

lemma metricNormalize_continuous (g : T → E →L[ℝ] E →L[ℝ] ℝ) (v : T → E)
    (hg : Continuous g) (hv : Continuous v) (hpos : ∀ t, 0 < g t (v t) (v t)) :
    Continuous (fun s ↦ metricNormalize (g s) (v s)) :=
  continuous_iff_continuousAt.mpr (fun t ↦ metricNormalize_continuousAt g v hg.continuousAt hv.continuousAt (hpos t))

lemma removeFrame_continuousAt (g : T → E →L[ℝ] E →L[ℝ] ℝ) (e : T → ι → E) (v : T → E) {t : T}
    (hg : ContinuousAt g t) (he : ∀ i, ContinuousAt (fun s ↦ e s i) t) (hv : ContinuousAt v t) :
    ContinuousAt (fun s ↦ removeFrame (g s) (e s) (v s)) t := by
  classical
  apply hv.sub
  have hsum (s : Finset ι) : ContinuousAt (fun x ↦ ∑ i ∈ s, g x (e x i) (v x) • e x i) t := by
    induction s using Finset.induction_on with
    | empty => simpa using (show ContinuousAt (fun _ : T ↦ (0:E)) t from continuousAt_const)
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (((hg.clm_apply (he i)).clm_apply hv).smul (he i)).add ih
  exact hsum Finset.univ

lemma removeFrame_continuous (g : T → E →L[ℝ] E →L[ℝ] ℝ) (e : T → ι → E) (v : T → E)
    (hg : Continuous g) (he : ∀ i, Continuous (fun s ↦ e s i)) (hv : Continuous v) :
    Continuous (fun s ↦ removeFrame (g s) (e s) (v s)) :=
  continuous_iff_continuousAt.mpr (fun _ ↦ removeFrame_continuousAt g e v hg.continuousAt
    (fun i ↦ (he i).continuousAt) hv.continuousAt)

end
end Yau.Geometry

end OAI
