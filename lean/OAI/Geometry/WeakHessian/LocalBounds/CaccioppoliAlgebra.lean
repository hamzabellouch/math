import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.LocalSobolevLipschitz
import OAI.Geometry.WeakHessian.LocalBounds.GammaAddConstLeft

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile166
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma gamma_caccioppoli_identity (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {w η : X → ℝ} (hw : Sobolev m w) {L : ℝ≥0} (hη : LipschitzWith L η)
    (hη1 : ∀ x,|η x| ≤ 1) :
    ∀ᵐ x ∂m,gamma m w (fun y => w y*(η y*η y)) x + w x^2*(weakGradient m η x)^2 =
      (weakGradient m (fun y => w y*η y) x)^2 := by
  have hηs := localSobolev_of_lipschitz hfin hη
  have hηB := ae_of_all m hη1
  have hηD : ∀ᵐ x ∂m,|weakGradient m η x| ≤ (L:ℝ) := by
    filter_upwards [weakGradient_nonneg (m := m) η,weakGradient_le_lipschitz hfin hη] with x hn hb
    rwa [abs_of_nonneg hn]
  have hus := hw.mul_bounded hfin hηs hηB hηD
  have hηsq : LipschitzWith (L+L) (fun x => η x*η x) := by
    simpa using lipschitz_mul_bounded hη hη hη1 hη1
  have hηsqB : ∀ᵐ x ∂m,|η x*η x| ≤ 1 := ae_of_all _ fun x => by
    simpa only [abs_mul,one_mul] using mul_le_mul (hη1 x) (hη1 x) (abs_nonneg _) zero_le_one
  have hηsqD : ∀ᵐ x ∂m,|weakGradient m (fun x => η x*η x) x| ≤ ((L+L:ℝ≥0):ℝ) := by
    filter_upwards [weakGradient_nonneg (m := m) (fun x => η x*η x),weakGradient_le_lipschitz hfin hηsq] with x hn hb
    rwa [abs_of_nonneg hn]
  filter_upwards [gamma_mul_left hfin hpar hw.2.1 (localSobolev_of_lipschitz hfin hηsq) hw.2.1 hηsqB hηsqD,
    gamma_mul_left hfin hpar hηs hηs hw.2.1 hηB hηD,
    gamma_mul_left hfin hpar hw.2.1 hηs hus.2.1 hηB hηD,
    gamma_mul_left hfin hpar hw.2.1 hηs hηs hηB hηD,
    gamma_mul_left hfin hpar hw.2.1 hηs hw.2.1 hηB hηD,
    gamma_comm (m := m) w (fun y => w y*(η y*η y)),
    gamma_comm (m := m) η (fun y => w y*η y),
    gamma_comm (m := m) w (fun y => w y*η y),gamma_comm (m := m) η w,
    gamma_self (m := m) η,gamma_self (m := m) (fun y => w y*η y)]
    with x h1 h2 h3 h4 h5 hc1 hc2 hc3 hc4 hs1 hs2
  rw [hc1,h1,h2,← hs2,h3,hc2,hc3,h4,h5,hs1,hc4]
  ring

lemma integral_gamma_caccioppoli_lower (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {w η : X → ℝ} (hw : Sobolev m w) {L : ℝ≥0} (hη : LipschitzWith L η)
    (hη1 : ∀ x,|η x| ≤ 1) :
    -((L:ℝ)^2*(∫ x,w x^2 ∂m)) ≤ ∫ x,gamma m w (fun y => w y*(η y*η y)) x ∂m := by
  have hηsq : LipschitzWith (L+L) (fun x => η x*η x) := by
    simpa using lipschitz_mul_bounded hη hη hη1 hη1
  have hB : ∀ᵐ x ∂m,|η x*η x| ≤ 1 := ae_of_all _ fun x => by
    simpa only [abs_mul,one_mul] using mul_le_mul (hη1 x) (hη1 x) (abs_nonneg _) zero_le_one
  have hD : ∀ᵐ x ∂m,|weakGradient m (fun x => η x*η x) x| ≤ ((L+L:ℝ≥0):ℝ) := by
    filter_upwards [weakGradient_nonneg (m := m) (fun x => η x*η x),weakGradient_le_lipschitz hfin hηsq] with x hn hb
    rwa [abs_of_nonneg hn]
  have hv := hw.mul_bounded hfin (localSobolev_of_lipschitz hfin hηsq) hB hD
  have hpoint : ∀ᵐ x ∂m,-((L:ℝ)^2*w x^2) ≤ gamma m w (fun y => w y*(η y*η y)) x := by
    filter_upwards [gamma_caccioppoli_identity hfin hpar hw hη hη1,
      weakGradient_le_lipschitz hfin hη,weakGradient_nonneg (m := m) η] with x he hl hn
    have hsq := sq_le_sq₀ hn L.coe_nonneg |>.mpr hl
    have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg (w x))
    nlinarith only [he,hm,sq_nonneg (weakGradient m (fun y => w y*η y) x)]
  simpa only [Pi.neg_apply,integral_neg,integral_const_mul] using
    integral_mono_ae ((hw.1.integrable_sq.const_mul ((L:ℝ)^2)).neg) (integrable_gamma hfin hw hv) hpoint
end WeakHessian

end
end InlinedFile166

end OAI
