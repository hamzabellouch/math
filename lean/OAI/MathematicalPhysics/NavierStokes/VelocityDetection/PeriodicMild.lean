import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.WeakVolterra
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.HeatKernelsIntegrableOnInvSqrt
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.PeriodicHeat

namespace OAI

noncomputable section
namespace VelocityDetection.PeriodicMild
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators
open HeatKernels PeriodicSpace.Jets WeakVolterra

abbrev E (a : ℕ) := compatibleJets 2 a

abbrev TimeCurve (T : ℝ) (a : ℕ) := Curve T (E a)

end VelocityDetection.PeriodicMild
end

noncomputable section
namespace VelocityDetection.PeriodicMild
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators
open HeatKernels PeriodicSpace.Jets WeakVolterra
variable {T : ℝ} {a : ℕ} (hT : 0 ≤ T) {ν : ℝ} (hν : 0 < ν)
variable (W : Fin 2 → TimeCurve T a)

def driftKernel (s r : ℝ) : E a →L[ℝ] E a :=
  -∑ i : Fin 2, (heatGradient ν s i).comp (productL 2 a (extend hT (W i) r))

@[simp] theorem driftKernel_apply (s r : ℝ) (J : E a) :
    driftKernel hT (ν := ν) W s r J =
      -∑ i : Fin 2, heatGradient ν s i (product (extend hT (W i) r) J) := by
  simp [driftKernel]

include hν in

theorem continuousOn_driftKernel :
    ContinuousOn (fun p : ℝ × ℝ × E a => driftKernel hT (ν := ν) W p.1 p.2.1 p.2.2)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  simp only [driftKernel_apply]
  apply ContinuousOn.neg
  apply continuousOn_finsetSum
  intro i _
  have hmul : Continuous (fun p : ℝ × ℝ × E a =>
      product (extend hT (W i) p.2.1) p.2.2) :=
    ((productL 2 a).continuous.comp
      ((continuous_extend hT (W i)).comp continuous_snd.fst)).clm_apply continuous_snd.snd
  apply (continuousOn_heatGradient_joint hν i).comp
    (continuous_fst.prodMk hmul).continuousOn
  intro p hp
  exact ⟨hp.1, mem_univ _⟩

def driftConstant : ℝ :=
  ∑ i : Fin 2, (absoluteMoment i / Real.sqrt (2 * ν)) * ((2 : ℝ)^a * ‖W i‖)

def driftBound (s : ℝ) : ℝ := driftConstant (ν := ν) W * (Real.sqrt s)⁻¹

theorem driftConstant_nonneg : 0 ≤ driftConstant (ν := ν) W := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (div_nonneg (absoluteMoment_nonneg i) (Real.sqrt_nonneg _)) (by positivity)

theorem driftBound_nonneg (s : ℝ) : 0 ≤ driftBound (ν := ν) W s :=
  mul_nonneg (driftConstant_nonneg W) (inv_nonneg.mpr (Real.sqrt_nonneg s))

include hT in

theorem integrableOn_driftBound : IntegrableOn (driftBound (ν := ν) W) (Ioc (0 : ℝ) T) :=
  (integrableOn_inv_sqrt hT).const_mul _

include hν in

theorem norm_driftKernel_le {s : ℝ} (hs : 0 < s) (r : ℝ) (J : E a) :
    ‖driftKernel hT (ν := ν) W s r J‖ ≤ driftBound (ν := ν) W s * ‖J‖ := by
  rw [driftKernel_apply, norm_neg]
  apply (norm_sum_le _ _).trans
  calc
    (∑ i : Fin 2, ‖heatGradient ν s i (product (extend hT (W i) r) J)‖) ≤
        ∑ i : Fin 2, ((absoluteMoment i / Real.sqrt (2 * ν)) *
          ((2 : ℝ)^a * ‖W i‖)) * (Real.sqrt s)⁻¹ * ‖J‖ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ‖heatGradient ν s i (product (extend hT (W i) r) J)‖ ≤
            (absoluteMoment i / Real.sqrt (2 * ν)) * (Real.sqrt s)⁻¹ *
              ‖product (extend hT (W i) r) J‖ := norm_heatGradient_le hν hs i _
        _ ≤ (absoluteMoment i / Real.sqrt (2 * ν)) * (Real.sqrt s)⁻¹ *
              ((2 : ℝ)^a * ‖W i‖ * ‖J‖) := by
          apply mul_le_mul_of_nonneg_left
          · apply (norm_product_le _ _).trans
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (norm_extend_le hT (W i) r) (by positivity)) (norm_nonneg J)
          · exact mul_nonneg (div_nonneg (absoluteMoment_nonneg i) (Real.sqrt_nonneg _)) (by positivity)
        _ = _ := by ring
    _ = driftBound (ν := ν) W s * ‖J‖ := by simp only [driftBound, driftConstant, Finset.sum_mul]

def sourceKernel (ν s _r : ℝ) : E a →L[ℝ] E a := heat (a := a) ν s

theorem continuous_sourceKernel (ν : ℝ) :
    Continuous (fun p : ℝ × ℝ × E a => sourceKernel (a := a) ν p.1 p.2.1 p.2.2) := by
  change Continuous ((fun r : ℝ × E a => heat ν r.1 r.2) ∘
    (fun p : ℝ × ℝ × E a => (p.1, p.2.2)))
  apply Continuous.comp
  · exact continuous_heat_joint (a := a) ν
  · exact continuous_fst.prodMk continuous_snd.snd

def sourceCurve (g : TimeCurve T a) : TimeCurve T a :=
  operator hT (sourceKernel ν) (fun _ => 1) (continuous_sourceKernel ν).continuousOn
    (integrableOn_const (measure_Ioc_lt_top).ne) (fun _ _ => zero_le_one)
    (fun s _ _ J => by simpa only [one_mul, sourceKernel] using norm_heat_le (a := a) ν s J) g

theorem sourceCurve_apply (g : TimeCurve T a) (t : Icc (0 : ℝ) T) :
    sourceCurve hT (ν := ν) g t =
      ∫ s in Ioc (0 : ℝ) t.val, heat ν s (extend hT g (t.val - s)) :=
  raw_eq_integral hT (sourceKernel ν) g t.property

include hν in

theorem existsUnique_mild (g : TimeCurve T a) :
    ∃! q : TimeCurve T a, ∀ t : Icc (0 : ℝ) T,
      q t = (∫ s in Ioc (0 : ℝ) t.val, heat ν s (extend hT g (t.val - s))) -
        ∫ s in Ioc (0 : ℝ) t.val,
          ∑ i : Fin 2, heatGradient ν s i
            (product (extend hT (W i) (t.val - s)) (extend hT q (t.val - s))) := by
  have heq (q : TimeCurve T a) : (∀ t : Icc (0 : ℝ) T,
        q t = sourceCurve hT (ν := ν) g t +
          ∫ s in Ioc (0 : ℝ) t.val,
            driftKernel hT (ν := ν) W s (t.val - s) (extend hT q (t.val - s))) ↔
      (∀ t : Icc (0 : ℝ) T,
        q t = (∫ s in Ioc (0 : ℝ) t.val, heat ν s (extend hT g (t.val - s))) -
          ∫ s in Ioc (0 : ℝ) t.val,
            ∑ i : Fin 2, heatGradient ν s i
              (product (extend hT (W i) (t.val - s)) (extend hT q (t.val - s)))) := by
    simp only [sourceCurve_apply, driftKernel_apply, integral_neg, sub_eq_add_neg]
  exact (existsUnique_congr heq).mp (existsUnique_pointwise hT (driftKernel hT (ν := ν) W)
    (driftBound (ν := ν) W) (continuousOn_driftKernel hT hν W)
    (integrableOn_driftBound hT W) (fun s _ => driftBound_nonneg W s)
    (fun s hs r J => norm_driftKernel_le hT hν W hs.1 r J) (sourceCurve hT (ν := ν) g))

end VelocityDetection.PeriodicMild
end

end OAI
