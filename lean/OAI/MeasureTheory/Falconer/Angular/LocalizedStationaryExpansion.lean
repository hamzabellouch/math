import OAI.MeasureTheory.Falconer.Angular.StationaryChartIntegral
import OAI.MeasureTheory.Falconer.Geometry.CompactQuadraticExpansion

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff SchwartzMap

noncomputable def stationaryDerivativeExpansion (f : ℝ → ℂ) (n : ℕ) (Λ : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1),
    ((((k.factorial:ℝ)⁻¹*(Real.pi^2/(Λ/2))^k):ℝ):ℂ)*Complex.I^k *
      (((-2*(Real.pi:ℂ)*Complex.I)^(2*k))⁻¹ * iteratedDeriv (2*k) (stationaryAmplitude f) 0)

 theorem localized_stationary_expansion {Λ C D : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (h₀ : ∀ x, ‖iteratedDeriv (2*(n+1)) (stationaryAmplitude f) x‖ ≤ C*D^(2*(n+1)))
    (h₂ : ∀ x, ‖iteratedDeriv (2*(n+1)+2) (stationaryAmplitude f) x‖ ≤ C*D^(2*(n+1)+2)) :
    ‖localizedCircleIntegral Λ f - Complex.exp (Complex.I*(Λ:ℂ)) *
      (fresnelCoefficient (Λ/2) * stationaryDerivativeExpansion f n Λ)‖ ≤
    ((Real.pi/(Λ/2))^(1/2:ℝ) * ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))) *
      ((C*2*D^(2*(n+1))/(2*Real.pi)^(2*(n+1)) +
        C*2*D^(2*(n+1)+2)/(2*Real.pi)^(2*(n+1)+2)) *
        ∫ ξ : ℝ, (1+ξ^2)⁻¹) := by
  obtain ⟨φ,hφ⟩ := stationaryAmplitude_schwartz hf
  have hs : tsupport (φ : ℝ → ℂ) ⊆ Icc (-1:ℝ) 1 := by
    rw [hφ]
    exact stationaryAmplitude_tsupport f
  have h₀' : ∀ x, ‖iteratedDeriv (2*(n+1)) (φ : ℝ → ℂ) x‖ ≤ C*D^(2*(n+1)) := by simpa [hφ] using h₀
  have h₂' : ∀ x, ‖iteratedDeriv (2*(n+1)+2) (φ : ℝ → ℂ) x‖ ≤ C*D^(2*(n+1)+2) := by simpa [hφ] using h₂
  have hh := compact_quadratic_stationary_expansion (half_pos hΛ) (by norm_num : (-1:ℝ) ≤ 1)
    φ hs n h₀' h₂'
  have he : quadraticExpansion φ n (Λ/2) = stationaryDerivativeExpansion f n Λ := by
    unfold quadraticExpansion stationaryDerivativeExpansion
    rw [hφ]
  have hn : ‖Complex.exp (Complex.I*(Λ:ℂ))‖ = 1 := by simp [Complex.norm_exp]
  rw [localizedCircleIntegral_quadratic Λ hf.continuous,← mul_sub,norm_mul,hn,one_mul]
  have hφ' : ∀ x, φ x = stationaryAmplitude f x := congrFun hφ
  simpa only [hφ',he,show (1:ℝ)- -1 = 2 by norm_num] using hh

 theorem localized_stationary_uniform_remainder (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    ∀ {Λ C D : ℝ}, 0 < Λ → 0 ≤ C → 1 ≤ D →
    (∀ k ≤ 2*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖localizedCircleIntegral Λ f - Complex.exp (Complex.I*(Λ:ℂ)) *
      (fresnelCoefficient (Λ/2) * stationaryDerivativeExpansion f n Λ)‖ ≤
    ((Real.pi/(Λ/2))^(1/2:ℝ) * ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))) *
      (A*C*D^(2*(n+1)+2)) := by
  obtain ⟨A₀,hA₀,h₀⟩ := stationaryAmplitude_uniform_derivatives (2*(n+1))
  obtain ⟨A₂,hA₂,h₂⟩ := stationaryAmplitude_uniform_derivatives (2*(n+1)+2)
  let B := max A₀ A₂
  let V : ℝ := ∫ ξ : ℝ, (1+ξ^2)⁻¹
  let A : ℝ := (B*2*((2*Real.pi)^(2*(n+1)))⁻¹ + B*2*((2*Real.pi)^(2*(n+1)+2))⁻¹)*V
  have hB : 0 ≤ B := hA₀.trans (le_max_left _ _)
  have hV : 0 ≤ V := integral_nonneg (fun _ => by positivity)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  intro f hf Λ C D hΛ hC hD hb
  have hD_nonneg : 0 ≤ D := zero_le_one.trans hD
  have hb₀ (x : ℝ) : ‖iteratedDeriv (2*(n+1)) (stationaryAmplitude f) x‖ ≤ (B*C)*D^(2*(n+1)) :=
    (h₀ f hf C D hC hD (fun k hk => hb k (by omega)) x).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left A₀ A₂) hC) (pow_nonneg hD_nonneg _))
  have hb₂ (x : ℝ) : ‖iteratedDeriv (2*(n+1)+2) (stationaryAmplitude f) x‖ ≤ (B*C)*D^(2*(n+1)+2) :=
    (h₂ f hf C D hC hD hb x).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right A₀ A₂) hC) (pow_nonneg hD_nonneg _))
  apply (localized_stationary_expansion hΛ hf n hb₀ hb₂).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hh := compact_quadratic_derivative_scale (by norm_num : (-1:ℝ) ≤ 1)
    (mul_nonneg hB hC) hD n
  have he : ((B*C)*2*D^(2*(n+1))/(2*Real.pi)^(2*(n+1)) +
      (B*C)*2*D^(2*(n+1)+2)/(2*Real.pi)^(2*(n+1)+2)) ≤
      ((B*C)*2*((2*Real.pi)^(2*(n+1)))⁻¹ +
      (B*C)*2*((2*Real.pi)^(2*(n+1)+2))⁻¹)*D^(2*(n+1)+2) := by
    simpa only [show (1:ℝ)- -1 = 2 by norm_num] using hh
  calc
    _ ≤ (((B*C)*2*((2*Real.pi)^(2*(n+1)))⁻¹ +
        (B*C)*2*((2*Real.pi)^(2*(n+1)+2))⁻¹)*D^(2*(n+1)+2))*V :=
      mul_le_mul_of_nonneg_right he hV
    _ = _ := by dsimp [A]; ring

end PlanarFalconer

end OAI
