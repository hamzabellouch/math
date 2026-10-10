import Mathlib
import OAI.Analysis.HardSphere.Geometry.GroundPathWeight
import OAI.Analysis.HardSphere.Geometry.JoinConfiguration

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace HardSphere
open MeasureTheory Wiener Set Filter
noncomputable section

lemma killed_endpoint_quadratic {N : ℕ} {L : Length} (a t : ℝ) (f g : ScalarL2 N L) :
    (∫ ω : ConfigurationPath N L, ‖f (ω 0)‖*‖g (ω 1)‖ ∂killedPathLaw N L a t) ≤
      (‖killedTransition N L a t‖/2)*(‖f‖^2+‖g‖^2) := by
  have h := re_inner_le_norm (𝕜:=ℂ) (modulusScalar f) (killedTransition N L a t (modulusScalar g))
  change (inner ℂ (modulusScalar f) (killedTransition N L a t (modulusScalar g))).re ≤ _ at h
  rw [modulus_killed_pairing,Complex.ofReal_re,norm_modulusScalar] at h
  have hh := (killedTransition N L a t).le_opNorm (modulusScalar g)
  rw [norm_modulusScalar] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (norm_nonneg f)
  have hAM := mul_nonneg (norm_nonneg (killedTransition N L a t)) (sq_nonneg (‖f‖-‖g‖))
  nlinarith

lemma killed_endpoint_quadratic_function {N : ℕ} {L : Length} (a t : ℝ)
    {f g : Configuration N L → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (∫⁻ ω : ConfigurationPath N L, ENNReal.ofReal (‖f (ω 0)‖*‖g (ω 1)‖)
      ∂killedPathLaw N L a t) ≤
      ENNReal.ofReal (‖killedTransition N L a t‖/2)*
        (ENNReal.ofReal (∫ x, ‖f x‖^2 ∂volume)+ENNReal.ofReal (∫ x, ‖g x‖^2 ∂volume)) := by
  let F := hf.toLp f
  let G := hg.toLp g
  have heq : (fun ω : ConfigurationPath N L ↦ ‖F (ω 0)‖*‖G (ω 1)‖) =ᵐ[killedPathLaw N L a t]
      (fun ω ↦ ‖f (ω 0)‖*‖g (ω 1)‖) := by
    filter_upwards [((freePathLaw_marginal N L t 0).quasiMeasurePreserving.ae_eq_comp
        (MemLp.coeFn_toLp hf)).filter_mono (ae_mono Measure.restrict_le_self),
      ((freePathLaw_marginal N L t 1).quasiMeasurePreserving.ae_eq_comp
        (MemLp.coeFn_toLp hg)).filter_mono (ae_mono Measure.restrict_le_self)] with ω hF hG
    simp only [Function.comp_def] at hF hG
    rw [show F (ω 0)=f (ω 0) from hF,show G (ω 1)=g (ω 1) from hG]
  have hnf : ‖F‖^2=∫ x, ‖f x‖^2 ∂volume := by
    rw [IndicatorStrong.norm_sq_integral]
    exact integral_congr_ae ((MemLp.coeFn_toLp hf).fun_comp (fun z : ℂ ↦ ‖z‖^2))
  have hng : ‖G‖^2=∫ x, ‖g x‖^2 ∂volume := by
    rw [IndicatorStrong.norm_sq_integral]
    exact integral_congr_ae ((MemLp.coeFn_toLp hg).fun_comp (fun z : ℂ ↦ ‖z‖^2))
  have heql := lintegral_congr_ae (heq.fun_comp ENNReal.ofReal)
  simp only [Function.comp_def] at heql
  rw [← heql,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_norm_endpoints N L a t F G 0 1)
      (Eventually.of_forall fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    ← hnf,← hng,← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← ENNReal.ofReal_mul (div_nonneg (norm_nonneg _) (by norm_num))]
  exact ENNReal.ofReal_le_ofReal (killed_endpoint_quadratic a t F G)

def sliceNormSq {m n : ℕ} {L : Length} (u : ScalarL2 (m+n) L) (y : Configuration m L) : ℝ :=
  ∫ x : Configuration n L, ‖u (joinConfiguration m n L (y,x))‖^2 ∂volume

lemma sliceNormSq_nonneg {m n : ℕ} {L : Length} (u : ScalarL2 (m+n) L) (y : Configuration m L) :
    0 ≤ sliceNormSq u y := integral_nonneg fun _ ↦ sq_nonneg _

lemma sliceNormSq_measurable {m n : ℕ} {L : Length} (u : ScalarL2 (m+n) L) :
    Measurable (sliceNormSq u) := by
  have h : StronglyMeasurable (fun p : Configuration m L × Configuration n L ↦
      ‖u (joinConfiguration m n L p)‖^2) :=
    (((Lp.stronglyMeasurable u).comp_measurable (joinConfiguration_continuous m n L).measurable).norm).pow 2
  exact h.integral_prod_right'.measurable

lemma memLp_slice_ae {m n : ℕ} {L : Length} (u : ScalarL2 (m+n) L) :
    ∀ᵐ y : Configuration m L ∂volume,
      MemLp (fun x : Configuration n L ↦ u (joinConfiguration m n L (y,x))) 2 volume := by
  have h := ((Lp.memLp u).comp_measurePreserving (joinConfiguration_preserving m n L)).integrable_norm_pow
    (show (2:ℕ)≠0 by norm_num)
  filter_upwards [h.prod_right_ae] with y hy
  apply (memLp_two_iff_integrable_sq_norm _).mpr hy
  exact (Lp.stronglyMeasurable u).comp_measurable
    ((joinConfiguration_continuous m n L).measurable.comp measurable_prodMk_left) |>.aestronglyMeasurable

lemma bath_slice_quadratic_ae {m n : ℕ} {L : Length} (u : ScalarL2 (m+n) L) (a t : ℝ) :
    ∀ᵐ ω : ConfigurationPath m L ∂freePathLaw m L t,
      (∫⁻ η : ConfigurationPath n L,
        ENNReal.ofReal (‖u (joinConfiguration m n L (ω 0,η 0))‖*
          ‖u (joinConfiguration m n L (ω 1,η 1))‖) ∂killedPathLaw n L a t) ≤
        ENNReal.ofReal (‖killedTransition n L a t‖/2)*
          (ENNReal.ofReal (sliceNormSq u (ω 0))+ENNReal.ofReal (sliceNormSq u (ω 1))) := by
  filter_upwards [(freePathLaw_marginal m L t 0).quasiMeasurePreserving.ae (memLp_slice_ae u),
    (freePathLaw_marginal m L t 1).quasiMeasurePreserving.ae (memLp_slice_ae u)] with ω h0 h1
  exact killed_endpoint_quadratic_function a t h0 h1
end
end HardSphere

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

end
end
end
end

end OAI
