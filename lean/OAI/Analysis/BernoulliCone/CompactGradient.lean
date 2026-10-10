import OAI.Analysis.BernoulliCone.HalfspaceDifferential

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli
open scoped _root_.Bernoulli
variable {d : ℕ}

lemma integral_gradient_compact {q : Space d → ℝ} {K : ℝ≥0}
    (hq : LipschitzWith K q) (hc : HasCompactSupport q) (e : Space d) :
    (∫ x, inner ℝ (gradient q x) e) = 0 := by
  have hh := (LipschitzWith.const (1:ℝ)).integral_lineDeriv_mul_eq
    (μ:=volume) hq hc (-e)
  have he : (fun x => lineDeriv ℝ q x (-(-e)) * (1:ℝ)) =ᵐ[volume]
      (fun x => inner ℝ (gradient q x) e) := by
    filter_upwards [hq.ae_differentiableAt] with x hx
    simp only [neg_neg,mul_one,hx.lineDeriv_eq_fderiv,inner_gradient_left]
  rw [integral_congr_ae he] at hh
  have hz (x : Space d) : lineDeriv ℝ (fun _ : Space d => (1:ℝ)) x (-e)=0 := by
    rw [(differentiableAt_const (1:ℝ)).lineDeriv_eq_fderiv]
    simp
  simpa only [hz,zero_mul,integral_zero] using hh.symm

lemma setIntegral_gradient_compact {q : Space d → ℝ} {K : ℝ≥0}
    (hq : LipschitzWith K q) (hc : HasCompactSupport q)
    {D : Set (Space d)} (hD : tsupport q ⊆ D) (e : Space d) :
    (∫ x in D, inner ℝ (gradient q x) e) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_gradient_compact hq hc e
  · intro x hx
    have hn : x∉tsupport q := fun hh => hx (hD hh)
    simp [gradient,fderiv_of_notMem_tsupport ℝ hn]
end Bernoulli

end
end

end OAI
