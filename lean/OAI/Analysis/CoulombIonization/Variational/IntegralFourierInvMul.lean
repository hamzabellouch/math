import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.WeakDirectionalDerivative

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap FourierTransform ENNReal
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace CoulombAtom
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma integral_fourierInv_mul {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ, (𝓕⁻ f) ξ * g ξ) = ∫ x, f x * (𝓕⁻ g) x := by
  have he := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := -(innerₗ V)) Real.continuous_fourierChar
    ((innerSL ℝ).continuous₂.neg) hf hg
  have hflip : (-(innerₗ V)).flip = -(innerₗ V) := by
    ext x y
    exact congrArg Neg.neg (real_inner_comm x y)
  change (∫ ξ, VectorFourier.fourierIntegral Real.fourierChar volume (-(innerₗ V)) f ξ * g ξ) =
    ∫ x, f x * VectorFourier.fourierIntegral Real.fourierChar volume (-(innerₗ V)) g x
  simpa only [smul_eq_mul, hflip] using he

lemma l2_fourierInv_ae_classical {f : V → ℂ} (hf : MemLp f 2) (hfi : Integrable f) :
    (fun ξ => (𝓕⁻ (hf.toLp f) : Lp ℂ 2 volume) ξ) =ᵐ[volume] (𝓕⁻ f) := by
  have hc : Continuous (𝓕⁻ f) := by
    have he : 𝓕⁻ f = fun x => (𝓕 f) (-x) := funext (Real.fourierInv_eq_fourier_neg f)
    rw [he]
    exact (classical_fourier_continuous hfi).comp continuous_neg
  apply ae_eq_of_integral_contDiff_smul_eq
    (Lp.memLp (𝓕⁻ (hf.toLp f)) |>.locallyIntegrable (by norm_num))
    hc.locallyIntegrable
  intro φ hφ hcompact
  let ψ : 𝓢(V, ℂ) := (hcompact.comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ)
  have hd := congrArg (fun d : 𝓢'(V, ℂ) => d ψ)
    (Lp.fourierInv_toTemperedDistribution_eq (hf.toLp f))
  simp only [TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at hd
  simp only [Complex.real_smul]
  change (∫ ξ, ψ ξ * (𝓕⁻ (hf.toLp f) : Lp ℂ 2 volume) ξ) = ∫ ξ, ψ ξ * (𝓕⁻ f) ξ
  rw [← hd]
  calc
    _ = ∫ x, (𝓕⁻ (ψ : V → ℂ)) x * f x := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]
      simp only [SchwartzMap.fourierInv_coe]
    _ = _ := integral_fourierInv_mul ψ.integrable hfi
end CoulombAtom

end

end OAI
