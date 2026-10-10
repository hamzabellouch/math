import Mathlib
import OAI.Geometry.WeakHessian.Transport.DensityMeasure

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile92
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma densityMeasure_ac_of_pos (u : Lp ℝ 2 m) (hu : ∀ᵐ x ∂m,0 < u x) :
    m ≪ densityMeasure m u := by
  apply withDensity_absolutelyContinuous' (Lp.stronglyMeasurable u |>.measurable.ennreal_ofReal.aemeasurable)
  exact hu.mono fun _ hx => (ENNReal.ofReal_pos.mpr hx).ne'

lemma restrict_le_densityMeasure (u : Lp ℝ 2 m) {S : Set X} (hS : MeasurableSet S)
    {c : ℝ} (hc : 0 < c) (hu : ∀ᵐ x ∂m,x ∈ S → c ≤ u x) :
    m.restrict S ≤ ENNReal.ofReal c⁻¹ • densityMeasure m u := by
  rw [← withDensity_indicator_one hS,densityMeasure,
    ← withDensity_smul _ (Lp.stronglyMeasurable u |>.measurable.ennreal_ofReal)]
  apply withDensity_mono
  filter_upwards [hu] with x hx
  by_cases hs : x ∈ S
  · simp only [indicator_of_mem hs,Pi.one_apply,Pi.smul_apply,smul_eq_mul]
    have H : (1:ℝ) ≤ c⁻¹*u x := by
      rw [inv_mul_eq_div]; exact (le_div_iff₀ hc).mpr (by simpa using hx hs)
    simpa only [ENNReal.ofReal_one,ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)] using ENNReal.ofReal_le_ofReal H
  · simp [hs]

variable [MetricSpace X]

lemma densityMeasure_locally_le (u : Lp ℝ 2 m) {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ᵐ x ∂m,u x ≤ B) :
    ∀ o : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      (densityMeasure m u).restrict (Metric.ball o R) ≤ (C:ℝ≥0∞) • m := by
  intro o R hR
  refine ⟨⟨B,hB⟩,?_⟩
  apply Measure.restrict_le_self.trans
  rw [densityMeasure,← withDensity_const]
  apply withDensity_mono
  filter_upwards [hu] with x hx
  exact (ENNReal.ofReal_le_ofReal hx).trans_eq (ENNReal.ofReal_eq_coe_nnreal hB)

variable (o : X) {a : ℝ} (ha : 0 < a)
variable (hw : MemLp (fun x => Real.exp (-(a*dist x o))) 2 m)

def positiveProbe (u : Lp ℝ 2 m) (ε : ℝ) : Lp ℝ 2 m :=
  u+ε • hw.toLp (fun x => Real.exp (-(a*dist x o)))

lemma positiveProbe_coe (u : Lp ℝ 2 m) (ε : ℝ) :
    positiveProbe o hw u ε =ᵐ[m] (fun x => u x+ε*Real.exp (-(a*dist x o))) := by
  filter_upwards [Lp.coeFn_add u (ε • hw.toLp _),Lp.coeFn_smul ε (hw.toLp _),hw.coeFn_toLp] with x h1 h2 h3
  simp only [positiveProbe,h1,Pi.add_apply,h2,Pi.smul_apply,smul_eq_mul,h3]

lemma positiveProbe_pos (u : Lp ℝ 2 m) (hu : ∀ᵐ x ∂m,0 ≤ u x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂m,0 < positiveProbe o hw u ε x := by
  filter_upwards [positiveProbe_coe o hw u ε,hu] with x hx hn
  rw [hx]
  positivity

lemma positiveProbe_integrable (u : Lp ℝ 2 m) (hu : Integrable u m)
    (hwi : Integrable (fun x => Real.exp (-(a*dist x o))) m) (ε : ℝ) :
    Integrable (positiveProbe o hw u ε) m :=
  (hu.add (hwi.const_mul ε)).congr (positiveProbe_coe o hw u ε).symm

include ha

lemma positiveProbe_le (u : Lp ℝ 2 m) {B : ℝ} (hu : ∀ᵐ x ∂m,u x ≤ B)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ x ∂m,positiveProbe o hw u ε x ≤ B+ε := by
  have haa := ha
  filter_upwards [positiveProbe_coe o hw u ε,hu] with x hx hn
  rw [hx]
  have hsmall : Real.exp (-(a*dist x o)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha.le dist_nonneg))
  nlinarith

variable [BorelSpace X]

lemma positiveProbe_locally_dominates (u : Lp ℝ 2 m) (hu : ∀ᵐ x ∂m,0 ≤ u x)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ p : X,∀ R : ℝ,0 < R → ∃ C : ℝ≥0,
      m.restrict (Metric.ball p R) ≤ (C:ℝ≥0∞) • densityMeasure m (positiveProbe o hw u ε) := by
  intro p R hR
  let c := ε*Real.exp (-(a*(R+dist p o)))
  have hc : 0 < c := mul_pos hε (Real.exp_pos _)
  refine ⟨Real.toNNReal c⁻¹,?_⟩
  change m.restrict (Metric.ball p R) ≤ ENNReal.ofReal c⁻¹ • _
  apply restrict_le_densityMeasure _ Metric.isOpen_ball.measurableSet hc
  filter_upwards [positiveProbe_coe o hw u ε,hu] with x hx hn hs
  rw [hx]
  have hd : dist x o ≤ R+dist p o := by
    have hs' := Metric.mem_ball.mp hs
    linarith [dist_triangle x p o]
  have he : Real.exp (-(a*(R+dist p o))) ≤ Real.exp (-(a*dist x o)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hd ha.le))
  dsimp [c]
  nlinarith
end WeakHessian

end
end InlinedFile92

end OAI
