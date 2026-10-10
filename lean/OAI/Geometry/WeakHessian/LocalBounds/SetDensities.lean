import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile76
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

def setDensity (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) : Lp ℝ 2 m :=
  (memLp_indicator_const 2 hS ((m S).toReal⁻¹) (Or.inr hfin)).toLp _

lemma setDensity_coe (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) :
    setDensity S hS hfin =ᵐ[m] S.indicator (fun _ => (m S).toReal⁻¹) := MemLp.coeFn_toLp _

lemma setDensity_nonneg (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) :
    ∀ᵐ x ∂m,0 ≤ setDensity S hS hfin x :=
  (setDensity_coe S hS hfin).mono fun x hx => hx ▸ indicator_nonneg (fun _ _ => by positivity) x

lemma setDensity_bounded (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) :
    ∀ᵐ x ∂m,|setDensity S hS hfin x| ≤ (m S).toReal⁻¹ := by
  filter_upwards [setDensity_coe S hS hfin] with x hx
  rw [hx]
  by_cases hs : x ∈ S <;> simp [hs,abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg),inv_nonneg.mpr ENNReal.toReal_nonneg]

lemma setDensity_mass (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) (hpos : m S ≠ 0) :
    (∫ x,setDensity S hS hfin x ∂m) = 1 := by
  rw [integral_congr_ae (setDensity_coe S hS hfin),integral_indicator hS,integral_const,measureReal_def,Measure.restrict_apply_univ,smul_eq_mul]
  exact mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hpos,hfin⟩)

lemma setDensity_pairing (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞) (f : Lp ℝ 2 m) :
    (∫ x,setDensity S hS hfin x*f x ∂m) = (m S).toReal⁻¹*(∫ x in S,f x ∂m) := by
  rw [← integral_const_mul,← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [setDensity_coe S hS hfin] with x hx
  rw [hx]
  by_cases hs : x ∈ S <;> simp [hs]

lemma setDensity_supported [MetricSpace X] (S : Set X) (hS : MeasurableSet S) (hfin : m S ≠ ∞)
    (a : X) {r : ℝ} (hs : S ⊆ Metric.closedBall a r) :
    ∀ᵐ x ∂m,r < dist x a → setDensity S hS hfin x = 0 := by
  filter_upwards [setDensity_coe S hS hfin] with x hx hr
  rw [hx,indicator_of_notMem]
  exact fun hmem => (not_le_of_gt hr) (hs hmem)
end WeakHessian

end
end InlinedFile76

end OAI
