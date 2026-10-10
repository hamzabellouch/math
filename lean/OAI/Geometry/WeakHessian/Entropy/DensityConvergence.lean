import Mathlib
import OAI.Geometry.WeakHessian.Entropy.EntropySlope

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile8
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [MetricSpace X] [BorelSpace X] in
lemma integral_sq_sub_le {f g : X → ℝ} (hf : MemLp f 2 m) (hg : MemLp g 2 m) :
    (∫ x, |f x^2-g x^2| ∂m) ≤ ‖hf.toLp f-hg.toLp g‖*‖hf.toLp f+hg.toLp g‖ := by
  have H := integral_mul_le_sqrt_integral_sq (hf.sub hg).norm (hf.add hg).norm
  simp only [Pi.sub_apply,Pi.add_apply,Real.norm_eq_abs,sq_abs] at H
  have hi : (∫ x,|f x^2-g x^2| ∂m) = ∫ x,|f x-g x| *|f x+g x| ∂m := by
    congr 1
    funext x
    rw [← abs_mul]
    congr 1
    ring
  rw [hi]
  have hs : (∫ x,(f x-g x)^2 ∂m) = ‖hf.toLp f-hg.toLp g‖^2 := by
    rw [← MemLp.toLp_sub hf hg]
    exact (norm_toLp_sq_eq_integral (hf.sub hg)).symm
  have ha : (∫ x,(f x+g x)^2 ∂m) = ‖hf.toLp f+hg.toLp g‖^2 := by
    rw [← MemLp.toLp_add hf hg]
    exact (norm_toLp_sq_eq_integral (hf.add hg)).symm
  simpa only [hs,ha,Real.sqrt_sq (norm_nonneg _)] using H

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_L1_tendsto {ι : Type*} {l : Filter ι} {fs : ι → X → ℝ} {w : X → ℝ}
    (hfs : ∀ i, MemLp (fs i) 2 m) (hw : MemLp w 2 m)
    (hF : Tendsto (fun i => (hfs i).toLp (fs i)) l (𝓝 (hw.toLp w))) :
    Tendsto (fun i => ∫ x, |fs i x^2-w x^2| ∂m) l (𝓝 0) := by
  have H := ((hF.sub (tendsto_const_nhds (x := hw.toLp w))).norm).mul ((hF.add (tendsto_const_nhds (x := hw.toLp w))).norm)
  simp only [sub_self,norm_zero,zero_mul] at H
  exact squeeze_zero (fun i => integral_nonneg fun x => abs_nonneg _) (fun i => integral_sq_sub_le (hfs i) hw) H

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_pairing_bound {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 m) (hg2 : MemLp g 2 m) {φ : X → ℝ} (hφ : AEStronglyMeasurable φ m)
    {M : ℝ} (hM : ∀ᵐ x ∂m, ‖φ x‖ ≤ M) :
    |(∫ x,φ x ∂squareDensityMeasure m f)-(∫ x,φ x ∂squareDensityMeasure m g)| ≤
      M*(∫ x,|f x^2-g x^2| ∂m) := by
  rw [squareDensity_integral hf,squareDensity_integral hg]
  have hi : Integrable (fun x => f x^2) m := hf2.integrable_sq
  have hj : Integrable (fun x => g x^2) m := hg2.integrable_sq
  have hif : Integrable (fun x => f x^2*φ x) m := by simpa only [mul_comm] using hi.bdd_mul hφ hM
  have hig : Integrable (fun x => g x^2*φ x) m := by simpa only [mul_comm] using hj.bdd_mul hφ hM
  rw [← integral_sub hif hig,← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x,‖f x^2*φ x-g x^2*φ x‖ ∂m := norm_integral_le_integral_norm _
    _ ≤ ∫ x,M*|f x^2-g x^2| ∂m := by
      apply integral_mono_ae (hif.sub hig).norm ((hi.sub hj).abs.const_mul M)
      filter_upwards [hM] with x hx
      simp only [Pi.sub_apply,← sub_mul,norm_mul,Real.norm_eq_abs] at *
      nlinarith [abs_nonneg (f x^2-g x^2)]
    _ = _ := integral_const_mul _ _

def squareDensityProbability (m : Measure X) (w : X → ℝ)
    (h : IsProbabilityMeasure (squareDensityMeasure m w)) : ProbabilityMeasure X :=
  ⟨squareDensityMeasure m w,h⟩

lemma squareDensity_tendsto_probability {fs : ℕ → X → ℝ} {w : X → ℝ}
    (hfm : ∀ n, Measurable (fs n)) (hwm : Measurable w)
    (hfs : ∀ n, MemLp (fs n) 2 m) (hw : MemLp w 2 m)
    (hP : ∀ n, IsProbabilityMeasure (squareDensityMeasure m (fs n)))
    (hW : IsProbabilityMeasure (squareDensityMeasure m w))
    (hF : Tendsto (fun n => (hfs n).toLp (fs n)) atTop (𝓝 (hw.toLp w))) :
    Tendsto (β := ProbabilityMeasure X) (fun n => squareDensityProbability m (fs n) (hP n)) atTop
      (𝓝 (squareDensityProbability m w hW)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro φ
  have H := (squareDensity_L1_tendsto hfs hw hF).const_mul ‖φ‖
  simp only [mul_zero] at H
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) _ H
  intro n
  exact squareDensity_pairing_bound (hfm n) hwm (hfs n) hw φ.continuous.aestronglyMeasurable
    (ae_of_all _ fun x => φ.norm_coe_le_norm x)
end WeakHessian

end
end InlinedFile8

end OAI
