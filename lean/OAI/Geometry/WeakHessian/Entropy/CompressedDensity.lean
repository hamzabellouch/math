import Mathlib
import OAI.Geometry.WeakHessian.Transport.DensityMeasure
import OAI.Geometry.WeakHessian.Calculus.RnDerivSmul

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]

omit [MetricSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
lemma toReal_rnDeriv_bounded {B : ℝ≥0} (hμ : μ ≤ (B : ℝ≥0∞) • m) :
    ∀ᵐ x ∂m, |(μ.rnDeriv m x).toReal| ≤ B := by
  filter_upwards [rnDeriv_le_of_le_smul hμ] with x hx
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono ENNReal.coe_ne_top hx).trans_eq (ENNReal.coe_toReal B)

omit [MetricSpace X] [BorelSpace X] in
lemma toReal_rnDeriv_memLp {B : ℝ≥0} (hμ : μ ≤ (B : ℝ≥0∞) • m) :
    MemLp (fun x => (μ.rnDeriv m x).toReal) 2 m := by
  have hm : AEStronglyMeasurable (fun x => (μ.rnDeriv m x).toReal) m :=
    (μ.measurable_rnDeriv m).ennreal_toReal.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply ((Measure.integrable_toReal_rnDeriv (μ := μ) (ν := m)).const_mul (B : ℝ)).mono' (hm.pow 2)
  filter_upwards [toReal_rnDeriv_bounded hμ] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hn : 0 ≤ (μ.rnDeriv m x).toReal := ENNReal.toReal_nonneg
  rw [abs_of_nonneg hn] at hx
  simp only [Pi.pow_apply]
  nlinarith

omit [MetricSpace X] [BorelSpace X] in
lemma exists_compressedDensity {B : ℝ≥0} (hμ : μ ≤ (B : ℝ≥0∞) • m) :
    ∃ u : Lp ℝ 2 m, (∀ᵐ x ∂m, 0 ≤ u x) ∧ (∀ᵐ x ∂m, |u x| ≤ B) ∧
      Integrable u m ∧ (∫ x, u x ∂m) = μ.real univ ∧
      densityMeasure m u = μ ∧ ‖u‖^2 ≤ (B : ℝ)*μ.real univ := by
  let hd := toReal_rnDeriv_memLp hμ
  let u := hd.toLp (fun x => (μ.rnDeriv m x).toReal)
  have he : (u : X → ℝ) =ᵐ[m] (fun x => (μ.rnDeriv m x).toReal) := hd.coeFn_toLp
  have hn : ∀ᵐ x ∂m, 0 ≤ u x := he.mono fun _ hx => hx ▸ ENNReal.toReal_nonneg
  have hb : ∀ᵐ x ∂m, |u x| ≤ B := by
    filter_upwards [he,toReal_rnDeriv_bounded hμ] with x hx hb
    rwa [hx]
  have hi : Integrable u m := Measure.integrable_toReal_rnDeriv.congr he.symm
  have hac : μ ≪ m := Measure.absolutelyContinuous_of_le_smul hμ
  have hmass : (∫ x, u x ∂m) = μ.real univ :=
    (integral_congr_ae he).trans (Measure.integral_toReal_rnDeriv hac)
  refine ⟨u,hn,hb,hi,hmass,?_,?_⟩
  · calc
      densityMeasure m u = m.withDensity (μ.rnDeriv m) := by
        apply withDensity_congr_ae
        filter_upwards [he,Measure.rnDeriv_ne_top μ m] with x hx ht
        rw [hx,ENNReal.ofReal_toReal ht]
      _ = μ := Measure.withDensity_rnDeriv_eq μ m hac
  · have hs : ‖u‖^2 = ∫ x, (u x)^2 ∂m := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      congr 1; funext x
      simp only [RCLike.inner_apply,conj_trivial,pow_two]
    rw [hs,← hmass,← integral_const_mul]
    apply integral_mono_ae (Lp.memLp u).integrable_sq (hi.const_mul (B : ℝ))
    filter_upwards [hn,hb] with x hn hb
    rw [abs_of_nonneg hn] at hb
    nlinarith

end WeakHessian

end
end

end OAI
