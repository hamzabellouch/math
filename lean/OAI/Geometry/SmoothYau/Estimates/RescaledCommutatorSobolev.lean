import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.SobolevRepresentativeOrderCongr

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

def rescaledCommutatorSobolev {s : ℝ} (hs : Module.finrank ℝ E < 2 * s)
    (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (p : E) (r : ℝ) (hr : r ≠ 0) :
    FourierSobolevSpace E ℂ (s + 1) →L[ℂ] FourierSobolevSpace E ℂ s :=
  firstOrderSobolev hs
    (affineSchwartz (euclideanElliptic b a c χ) (contDiff_euclideanElliptic b a c ha hc hχ)
      (hasCompactSupport_euclideanElliptic b a c hχc) p r hr)
    (fun ij : ι × ι => (r : ℂ)⁻¹ • affineSchwartz
      (cutoffDerivativeSchwartz hχ hχc (ha ij.1 ij.2) (b ij.1))
      ((cutoffDerivativeSchwartz hχ hχc (ha ij.1 ij.2) (b ij.1)).smooth ⊤)
      (by exact (hχc.fderiv_apply ℝ (b ij.1)).mul_left) p r hr)
    (fun ij : ι × ι => b ij.2) +
  firstOrderSobolev hs 0
    (fun ij : ι × ι => (r : ℂ)⁻¹ • affineSchwartz
      (cutoffDerivativeSchwartz hχ hχc (ha ij.1 ij.2) (b ij.2))
      ((cutoffDerivativeSchwartz hχ hχc (ha ij.1 ij.2) (b ij.2)).smooth ⊤)
      (by exact (hχc.fderiv_apply ℝ (b ij.2)).mul_left) p r hr)
    (fun ij : ι × ι => b ij.1)

lemma rescaledCommutatorSobolev_representative {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * (s + 1))
    (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (p : E) (r : ℝ) (hr : r ≠ 0)
    (u : FourierSobolevSpace E ℂ (s + 1)) (y : E) :
    sobolevRepresentative hs (rescaledCommutatorSobolev hs b a c ha hc χ hχ hχc p r hr u) y =
      euclideanElliptic b a c χ (p + r • y) * sobolevRepresentative ht u y +
        ∑ i, ∑ j, (r : ℂ)⁻¹ * (a i j (p + r • y) : ℂ) *
          (fderiv ℝ χ (p + r • y) (b i) *
              fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b j) +
            fderiv ℝ χ (p + r • y) (b j) *
              fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b i)) := by
  simp only [rescaledCommutatorSobolev, add_apply, map_add,
    BoundedContinuousFunction.add_apply, firstOrderSobolev_representative hs ht,
    affineSchwartz_apply,
    smul_apply, smul_eq_mul, zero_apply, zero_mul,
    zero_add, Fintype.sum_prod_type]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change (r : ℂ)⁻¹ * ((a i j (p + r • y) : ℂ) * fderiv ℝ χ (p + r • y) (b i)) *
      fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b j) +
    (r : ℂ)⁻¹ * ((a i j (p + r • y) : ℂ) * fderiv ℝ χ (p + r • y) (b j)) *
      fderiv ℝ (sobolevRepresentative ht u : E → ℂ) y (b i) = _
  ring

lemma rescaledCommutatorSobolev_physical {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * s) (ht : Module.finrank ℝ E < 2 * (s + 1))
    (b : ι → E) (a : ι → ι → E → ℝ) (c : ι → E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (χ : E → ℂ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (p : E) (r : ℝ) (hr : r ≠ 0)
    (u : FourierSobolevSpace E ℂ (s + 1)) (x : E) :
    sobolevRepresentative hs (rescaledCommutatorSobolev hs b a c ha hc χ hχ hχc p r hr u)
        (r⁻¹ • (x - p)) =
      ellipticCommutator b a c χ
        (fun y => sobolevRepresentative ht u (r⁻¹ • (y - p))) x := by
  have hi : p + r • (r⁻¹ • (x - p)) = x := by
    simp only [smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
  have hu : Differentiable ℝ (sobolevRepresentative ht u : E → ℂ) :=
    (contDiff_sobolevRepresentative 1 (by norm_num; linarith) ht u).differentiable (by simp)
  rw [rescaledCommutatorSobolev_representative hs ht]
  simp only [hi, ellipticCommutator, fderiv_inverseScalarAffine p r _ _ (hu _),
    Complex.ofReal_inv]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
end YauCounterexamples


end

end OAI
