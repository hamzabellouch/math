import Mathlib
import OAI.Geometry.PrescribedRicci.TameRoughInverse

namespace OAI

/-! Rough Elliptic Gain. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff Classical ComplexOrder MatrixOrder
namespace FrozenPoisson
open SobolevChart EllipticKernel
variable {n : ℕ} {ι : Type*} [Fintype ι]

lemma parameterResolvent_forward (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {t : ℝ} (ht : 0 < t) (u : 𝓢'(EC n,ℂ)) :
    parameterResolvent H t (parameterForward H t u) = u := by
  rw [parameterResolvent,parameterForward,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (parameterForward_temperate H hH t)
      (parameterSymbol_temperate H hH ht)]
  have he : (fun ξ => ((t^2+symbol H ξ : ℝ):ℂ)) * parameterSymbol H t = fun _ => (1:ℂ) := by
    funext ξ
    simp only [Pi.mul_apply,parameterSymbol,← Complex.ofReal_mul]
    have hp := symbol_nonneg H hH ξ
    rw [mul_inv_cancel₀ (by positivity : t^2+symbol H ξ ≠ 0),Complex.ofReal_one]
  rw [he,fourierMultiplierCLM_const]
  simp

lemma fixed_of_differential_equation (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (a : ι → ι → EC n →ᵇ ℂ)
    (u f : L2 (EC n))
    (he : (t^2:ℂ) • realize 2 u - frozenDifferential H (realize 2 u) -
      ((perturbation v a u : L2 (EC n)) : 𝓢'(EC n,ℂ)) = (f : 𝓢'(EC n,ℂ))) :
    u = parameterHilbert H hH t ht (f+perturbation v a u) := by
  apply realize_injective 2
  have hr := parameterHilbert_realize H hH t ht 0 (f+perturbation v a u)
  simp only [zero_add] at hr
  rw [hr]
  have hf : realize 0 (f+perturbation v a u) =
      (f : 𝓢'(EC n,ℂ)) + ((perturbation v a u : L2 (EC n)) : 𝓢'(EC n,ℂ)) := by
    simp [realize, ← Lp.toTemperedDistributionCLM_apply, map_add]
  rw [hf,← sub_eq_iff_eq_add.mp he,← parameterForward_eq H hH]
  exact (parameterResolvent_forward H hH (lt_of_lt_of_le zero_lt_one ht) _).symm

 

theorem rough_equation_memSobolev (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (t : ℝ) (ht : 1 ≤ t) (v : ι → EC n) (k : ℕ)
    (hk : Module.finrank ℝ (EC n)+1 < k)
    (hs : (Module.finrank ℝ (EC n):ℝ) < 2*(k:ℝ))
    (a : ι → ι → L2 (EC n)) (f u : L2 (EC n))
    (hsmall : perturbationBound v (fun i j => strongEmbedding (k:ℝ) hs (a i j))*ellipticBound H hH < 1)
    (he : (t^2:ℂ) • realize 2 u - frozenDifferential H (realize 2 u) -
      ((perturbation v (fun i j => strongEmbedding (k:ℝ) hs (a i j)) u : L2 (EC n)) : 𝓢'(EC n,ℂ)) =
        realize (k:ℝ) f) :
    MemSobolev ((k:ℝ)+2) 2 (realize 2 u) := by
  let f0 := lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k) f
  have hf0 : (f0 : 𝓢'(EC n,ℂ)) = realize (k:ℝ) f := by
    have hh := realize_lowerCoord (k:ℝ) 0 (Nat.cast_nonneg k) f
    simpa [realize,f0] using hh
  have hu := fixed_of_differential_equation H hH t ht v _ u f0 (he.trans hf0.symm)
  have heq := ParameterRegularity.fixed_unique H hH t ht v _ hsmall u
    (parameterLocal H hH t ht v _ hsmall f0) f0 hu
    (ParameterRegularity.parameterLocal_fixed H hH t ht v _ hsmall f0)
  rw [heq]
  exact ParameterRegularity.rough_local_memSobolev H hH t ht v k hk hs a f hsmall

end FrozenPoisson

end
end

end OAI
