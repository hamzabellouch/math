import OAI.GroupTheory.PolycyclicRecognition.Algebra.BilateralDifference

namespace OAI

/-! # Removing the coefficient twist from a bilateral shift -/

noncomputable section
namespace PolycyclicRecognition

open Representation
variable (k M : Type*) [CommRing k] [AddCommGroup M] [Module k M]

def bilateralPowerMap (e : M ≃ₗ[k] M) : (ℤ →₀ M) →ₗ[k] (ℤ →₀ M) :=
  Finsupp.lsum k fun i => (Finsupp.lsingle i).comp (e ^ i).toLinearMap

@[simp] theorem bilateralPowerMap_single (e : M ≃ₗ[k] M) (i : ℤ) (m : M) :
    bilateralPowerMap k M e (Finsupp.single i m) = Finsupp.single i ((e ^ i) m) := by
  simp [bilateralPowerMap]

theorem bilateralPowerMap_inv_comp (e : M ≃ₗ[k] M) :
    (bilateralPowerMap k M e⁻¹).comp (bilateralPowerMap k M e) = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro i
  apply LinearMap.ext
  intro m
  change bilateralPowerMap k M e⁻¹ (bilateralPowerMap k M e (Finsupp.single i m)) = _
  simp only [bilateralPowerMap_single]
  rw [← LinearEquiv.mul_apply, inv_zpow, inv_mul_cancel]
  rfl

def bilateralGauge (e : M ≃ₗ[k] M) : (ℤ →₀ M) ≃ₗ[k] (ℤ →₀ M) :=
  LinearEquiv.ofLinearMap (bilateralPowerMap k M e⁻¹) (bilateralPowerMap k M e)
    (bilateralPowerMap_inv_comp k M e)
    (by simpa only [inv_inv] using bilateralPowerMap_inv_comp k M e⁻¹)

@[simp] theorem bilateralGauge_single (e : M ≃ₗ[k] M) (i : ℤ) (m : M) :
    bilateralGauge k M e (Finsupp.single i m) = Finsupp.single i ((e ^ (-i)) m) := by
  change bilateralPowerMap k M e⁻¹ (Finsupp.single i m) = _
  rw [bilateralPowerMap_single, inv_zpow, zpow_neg]

def twistedBilateralShift (e : M ≃ₗ[k] M) : (ℤ →₀ M) →ₗ[k] (ℤ →₀ M) :=
  (Finsupp.mapRange.linearMap e.toLinearMap).comp
    (bilateralTranslation k M (Multiplicative.ofAdd 1))

@[simp] theorem twistedBilateralShift_single (e : M ≃ₗ[k] M) (i : ℤ) (m : M) :
    twistedBilateralShift k M e (Finsupp.single i m) = Finsupp.single (i + 1) (e m) := by
  simp [twistedBilateralShift, add_comm]

theorem bilateralGauge_shift (e : M ≃ₗ[k] M) (f : ℤ →₀ M) :
    bilateralGauge k M e (twistedBilateralShift k M e f) =
      bilateralTranslation k M (Multiplicative.ofAdd 1) (bilateralGauge k M e f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single i m =>
      rw [twistedBilateralShift_single, bilateralGauge_single, bilateralGauge_single,
        bilateralTranslation_single]
      have he : (e ^ (-(i + 1))) (e m) = (e ^ (-i)) m := by
        rw [← LinearEquiv.mul_apply, ← zpow_add_one]
        congr 2
        omega
      simpa only [toAdd_ofAdd, add_comm] using congrArg (Finsupp.single (i + 1)) he

def twistedBilateralDifference (e : M ≃ₗ[k] M) : (ℤ →₀ M) →ₗ[k] (ℤ →₀ M) :=
  twistedBilateralShift k M e - LinearMap.id

def twistedBilateralSum (e : M ≃ₗ[k] M) : (ℤ →₀ M) →ₗ[k] M :=
  (bilateralSum k M).comp (bilateralGauge k M e).toLinearMap

theorem bilateralGauge_difference (e : M ≃ₗ[k] M) (f : ℤ →₀ M) :
    bilateralGauge k M e (twistedBilateralDifference k M e f) =
      bilateralDifference k M (bilateralGauge k M e f) := by
  change bilateralGauge k M e (twistedBilateralShift k M e f - f) = _
  rw [map_sub, bilateralGauge_shift]
  rfl

theorem twistedBilateralDifference_injective (e : M ≃ₗ[k] M) :
    Function.Injective (twistedBilateralDifference k M e) := by
  intro f g h
  apply (bilateralGauge k M e).injective
  apply bilateralDifference_injective k M
  simpa only [bilateralGauge_difference] using congrArg (bilateralGauge k M e) h

theorem twistedBilateralSum_surjective (e : M ≃ₗ[k] M) :
    Function.Surjective (twistedBilateralSum k M e) :=
  (bilateralSum_surjective k M).comp (bilateralGauge k M e).surjective

theorem twistedBilateralSum_ker_eq_range (e : M ≃ₗ[k] M) :
    LinearMap.ker (twistedBilateralSum k M e) =
      LinearMap.range (twistedBilateralDifference k M e) := by
  ext f
  change bilateralSum k M (bilateralGauge k M e f) = 0 ↔ _
  rw [← LinearMap.mem_ker, bilateralSum_ker_eq_range]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨(bilateralGauge k M e).symm g, ?_⟩
    apply (bilateralGauge k M e).injective
    rw [bilateralGauge_difference, LinearEquiv.apply_symm_apply, hg]
  · rintro ⟨g, rfl⟩
    exact ⟨bilateralGauge k M e g, (bilateralGauge_difference k M e g).symm⟩

end PolycyclicRecognition

end

end OAI
