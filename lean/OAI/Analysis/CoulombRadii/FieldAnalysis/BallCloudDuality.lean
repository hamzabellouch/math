import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.UniformBall
import OAI.Analysis.CoulombRadii.ThomasFermi.TFCountTest

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

variable {Ω : Set Space} (hΩ : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]

include hΩ

lemma raw_coulomb_cauchy {f g : Space → ℝ}
    (hf : MemLp f TFExponent (volume.restrict Ω))
    (hg : MemLp g TFExponent (volume.restrict Ω))
    (hfs : ∀ x∉Ω, f x=0) (hgs : ∀ x∉Ω, g x=0) :
    (coulombBilinear f g)^2≤coulombBilinear f f*coulombBilinear g g := by
  have he := tfExtend_toLp hΩ hf hfs
  have he' := tfExtend_toLp hΩ hg hgs
  have hh := tfCoulomb_cauchy hΩ (hf.toLp f) (hg.toLp g)
  change (coulombBilinear (tfExtend Ω (hf.toLp f)) (tfExtend Ω (hg.toLp g)))^2≤
    coulombBilinear (tfExtend Ω (hf.toLp f)) (tfExtend Ω (hf.toLp f))*
      coulombBilinear (tfExtend Ω (hg.toLp g)) (tfExtend Ω (hg.toLp g)) at hh
  rwa [coulombBilinear_congr_ae he he',coulombBilinear_congr_ae he he,
    coulombBilinear_congr_ae he' he'] at hh

lemma raw_coulomb_ballCloud_duality {f : Space → ℝ}
    (hf : MemLp f TFExponent (volume.restrict Ω)) (hfs : ∀ x∉Ω, f x=0)
    (y : Space) {a : ℝ} (ha : 0<a) (hb : Metric.ball y a⊆Ω) :
    (coulombBilinear f (ballCloud y a 1))^2≤(5/(2*a))*coulombBilinear f f := by
  have hg : MemLp (ballCloud y a 1) TFExponent (volume.restrict Ω) :=
    MemLp.of_bound (ballCloud_measurable a 1 y).aestronglyMeasurable
      (1/(4*Real.pi/3*a^3)) (Eventually.of_forall (fun z => by
        change ‖uniformBall a 1 (z-y)‖≤_
        rw [Real.norm_of_nonneg (uniformBall_nonneg ha zero_le_one (z-y))]
        exact uniformBall_le ha zero_le_one _))
  have hgs : ∀ x∉Ω, ballCloud y a 1 x=0 := by
    intro x hx
    change (Metric.ball (0:Space) a).indicator (fun _ => 1/(4*Real.pi/3*a^3)) (x-y)=0
    apply indicator_of_notMem
    intro hh
    apply hx
    apply hb
    simpa only [Metric.mem_ball,dist_zero_right,dist_eq_norm,sub_zero] using hh
  have H := raw_coulomb_cauchy hΩ hf hg hfs hgs
  have hq := raw_coulomb_nonneg hΩ hf hfs
  have HG := mul_le_mul_of_nonneg_left (ballCloud_coulombBilinear_bound ha zero_le_one y) hq
  apply H.trans
  convert HG using 1
  ring

end Coulomb
end

end
end

end OAI
