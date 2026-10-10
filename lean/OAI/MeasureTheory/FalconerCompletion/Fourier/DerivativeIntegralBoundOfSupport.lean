import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Fourier.SchwartzNormMonomialIntegrable

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open MeasureTheory Set
open scoped SchwartzMap FourierTransform
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma derivative_integral_bound_of_support (φ : 𝓢(V,ℂ)) (j : ℕ)
    {K : Set V} (hK : IsCompact K) (hsupp : tsupport (φ : V → ℂ) ⊆ K)
    {D : ℝ} (hD : ∀ x : V, ‖iteratedFDeriv ℝ j φ x‖ ≤ D) :
    (∫ x : V, ‖iteratedFDeriv ℝ j φ x‖) ≤ D * volume.real K := by
  have hz (x : V) (hx : x ∉ K) : ‖iteratedFDeriv ℝ j φ x‖ = 0 := by
    rw [norm_eq_zero]
    by_contra h
    exact hx (hsupp (support_iteratedFDeriv_subset j h))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  calc
    _ ≤ ∫ x in K, D := integral_mono
      ((show Integrable (fun x : V => ‖iteratedFDeriv ℝ j φ x‖) from by
        simpa using φ.integrable_pow_mul_iteratedFDeriv volume 0 j).restrict) (integrable_const D)
      (fun x => hD x)
    _ = D * volume.real K := by simp [mul_comm,measureReal_def]

lemma fourierDerivativeND_L1_uniform (φ : 𝓢(V,ℂ)) (n M : ℕ) (hnM : n ≤ M)
    {K : Set V} (hK : IsCompact K) (hsupp : tsupport (φ : V → ℂ) ⊆ K)
    {C A : ℝ} (hC : 0 ≤ C) (hA : 1 ≤ A)
    (hderiv : ∀ j ≤ M, ∀ x : V, ‖iteratedFDeriv ℝ j φ x‖ ≤ C*A^j) :
    fourierDerivativeND_L1 φ n ≤
      (2^n * (n+1) * (C * volume.real K)) * A^M := by
  have hbound (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∫ x : V, ‖iteratedFDeriv ℝ j φ x‖) ≤ (C * volume.real K) * A^M := by
    have hjM : j ≤ M := (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hnM
    calc
      _ ≤ (C*A^j) * volume.real K := derivative_integral_bound_of_support φ j hK hsupp (hderiv j hjM)
      _ ≤ (C*A^M) * volume.real K := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA hjM) hC) ENNReal.toReal_nonneg
      _ = _ := by ring
  unfold fourierDerivativeND_L1
  calc
    _ ≤ 2^n * ∑ _j ∈ Finset.range (n+1), (C * volume.real K) * A^M :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hbound) (by positivity)
    _ = _ := by simp; ring

lemma quadratic_decay_factor {b : ℝ} (hb : 0 < b) (p : ℝ) (n : ℕ) :
    (Real.pi/b)^p * ((Real.pi^2/b)^n/(n.factorial:ℝ)) =
      (Real.pi^p * (Real.pi^2)^n/(n.factorial:ℝ)) * b^(-p-(n:ℝ)) := by
  rw [sub_eq_add_neg, Real.rpow_add hb, Real.rpow_neg hb.le,
    Real.rpow_neg hb.le, Real.rpow_natCast, Real.div_rpow Real.pi_pos.le hb.le, div_pow]
  simp only [div_eq_mul_inv]
  ring

theorem quadratic_stationaryND_uniform (K : Set V) (hK : IsCompact K)
    (C : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (φ : 𝓢(V,ℂ)) (A b : ℝ),
      tsupport (φ : V → ℂ) ⊆ K → 1 ≤ A → 0 < b →
      (∀ j ≤ 2*(n+1)+Module.finrank ℝ V+3, ∀ x : V,
        ‖iteratedFDeriv ℝ j φ x‖ ≤ C*A^j) →
      ‖(∫ x : V, Complex.exp (-((b:ℂ)*Complex.I)*(‖x‖:ℂ)^2)*φ x) -
          fresnelCoefficientND V b * quadraticExpansionND φ n b‖ ≤
        D * b^(-(Module.finrank ℝ V/2:ℝ)-(n+1:ℕ)) *
          A^(2*(n+1)+Module.finrank ℝ V+3) := by
  let m := Module.finrank ℝ V+3
  let M := 2*(n+1)+m
  let c₁ : ℝ := 2^(2*(n+1)) * (2*(n+1)+1) * (C * volume.real K)
  let c₂ : ℝ := 2^M * (M+1) * (C * volume.real K)
  let I : ℝ := ∫ ξ : V, ((1+‖ξ‖)^m)⁻¹
  let D : ℝ := (Real.pi^(Module.finrank ℝ V/2:ℝ) * (Real.pi^2)^(n+1) /
        (n.factorial:ℝ)) * (2^m * (c₁+c₂)) * I
  refine ⟨D, by dsimp [D,I,c₁,c₂]; positivity, ?_⟩
  intro φ A b hsupp hA hb hderiv
  have hM : M = 2*(n+1)+Module.finrank ℝ V+3 := by dsimp [M,m]; omega
  have h₁ : fourierDerivativeND_L1 φ (2*(n+1)) ≤ c₁*A^M := by
    simpa [c₁, Nat.cast_mul, Nat.cast_add] using
      fourierDerivativeND_L1_uniform φ (2*(n+1)) M (by dsimp [M]; omega) hK hsupp hC hA
        (by simpa [hM] using hderiv)
  have h₂ : fourierDerivativeND_L1 φ M ≤ c₂*A^M :=
    fourierDerivativeND_L1_uniform φ M M le_rfl hK hsupp hC hA
      (by simpa [hM] using hderiv)
  have hI : 0 ≤ I := by dsimp [I]; positivity
  have hc : fourierDerivativeND_L1 φ (2*(n+1)) + fourierDerivativeND_L1 φ M ≤
      (c₁+c₂)*A^M := by nlinarith
  have hbase := quadratic_stationaryND_expansion_L1 hb φ n (m := m) (by dsimp [m]; omega)
  calc
    _ ≤ ((Real.pi/b)^(Module.finrank ℝ V/2:ℝ) * ((Real.pi^2/b)^(n+1)/(n.factorial:ℝ))) *
        ((2^m*(fourierDerivativeND_L1 φ (2*(n+1))+fourierDerivativeND_L1 φ M)) * I) := hbase
    _ ≤ ((Real.pi/b)^(Module.finrank ℝ V/2:ℝ) * ((Real.pi^2/b)^(n+1)/(n.factorial:ℝ))) *
        ((2^m*((c₁+c₂)*A^M)) * I) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by positivity)) hI
    _ = D * b^(-(Module.finrank ℝ V/2:ℝ)-(n+1:ℕ)) *
          A^(2*(n+1)+Module.finrank ℝ V+3) := by
      have he : (Real.pi/b)^(Module.finrank ℝ V/2:ℝ) * ((Real.pi^2/b)^(n+1)/(n.factorial:ℝ)) =
          (Real.pi^(Module.finrank ℝ V/2:ℝ) * (Real.pi^2)^(n+1)/(n.factorial:ℝ)) *
            b^(-(Module.finrank ℝ V/2:ℝ)-(n+1:ℕ)) := by
        rw [sub_eq_add_neg, Real.rpow_add hb, Real.rpow_neg hb.le,
          Real.rpow_neg hb.le, Real.rpow_natCast,
          Real.div_rpow Real.pi_pos.le hb.le, div_pow]
        simp only [div_eq_mul_inv]
        ring
      rw [he, ← hM]
      dsimp [D]
      ring

lemma quadraticExpansionND_eq_laplacian_series {b : ℝ} (hb : b ≠ 0)
    (φ : 𝓢(V,ℂ)) (n : ℕ) :
    quadraticExpansionND φ n b =
      ∑ k ∈ Finset.range (n+1),
        ((-Complex.I/(4*(b:ℂ)))^k/(k.factorial:ℂ)) * iteratedLaplacianND φ k 0 := by
  rw [quadraticExpansionND_eq_local]
  apply Finset.sum_congr rfl
  intro k _
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hb' : (b:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  have he : ((Real.pi:ℂ)^2/(b:ℂ))*Complex.I*((-(2*(Real.pi:ℂ))^2)⁻¹) =
      -Complex.I/(4*(b:ℂ)) := by field_simp; ring
  push_cast
  rw [← inv_pow]
  have he' := congrArg (fun z : ℂ => z^k) he
  simp only [mul_pow] at he'
  calc
    _ = ((k.factorial:ℂ))⁻¹ *
        (((Real.pi:ℂ)^2/(b:ℂ))^k * Complex.I^k * ((-(2*(Real.pi:ℂ))^2)⁻¹)^k) *
          iteratedLaplacianND φ k 0 := by ring
    _ = _ := by simp only [mul_pow]; rw [he']; ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
