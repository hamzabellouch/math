import OAI.MeasureTheory.Falconer.Angular.FullCircleDecomposition
import OAI.MeasureTheory.Falconer.Angular.CircleDirectCoefficients

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def fullCircleStationaryExpansion (Λ : ℝ) (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  Complex.exp (Complex.I*(Λ:ℂ))*(fresnelCoefficient (Λ/2)*stationaryDerivativeExpansion f n Λ) +
    conj (Complex.exp (Complex.I*(Λ:ℂ))*(fresnelCoefficient (Λ/2)*
      stationaryDerivativeExpansion (fun θ => conj (f (θ+Real.pi))) n Λ))

 theorem full_circle_stationary_expansion (n M : ℕ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    Function.Periodic f (2*Real.pi) → ∀ {Λ C D : ℝ}, 0 < Λ → 0 ≤ C → 1 ≤ D →
    (∀ k ≤ max (2*(n+1)+2) M, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖(∫ θ in (-Real.pi)..Real.pi, cosineOscillator Λ θ*f θ) - fullCircleStationaryExpansion Λ f n‖ ≤
      ((Real.pi/(Λ/2))^(1/2:ℝ) * ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))) *
        (A*C*D^(2*(n+1)+2)) + B*C*D^M/Λ^M := by
  obtain ⟨A₀,hA₀,h₀⟩ := localized_stationary_uniform_remainder n
  obtain ⟨Aπ,hAπ,hπ⟩ := localized_stationary_opposite_remainder n
  obtain ⟨B,hB,hr⟩ := circle_residual_uniform_decay M
  refine ⟨A₀+Aπ,B,add_nonneg hA₀ hAπ,hB,?_⟩
  intro f hf hp Λ C D hΛ hC hD hb
  have hbf : ∀ k ≤ 2*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k :=
    fun k hk => hb k (hk.trans (le_max_left _ _))
  have hbs : ∀ k ≤ 2*(n+1)+2, ∀ x, ‖iteratedDeriv k (fun θ => f (θ+Real.pi)) x‖ ≤ C*D^k := by
    intro k hk x
    rw [iteratedDeriv_comp_add_const]
    exact hbf k hk _
  have hfs : ContDiff ℝ ∞ (fun θ => f (θ+Real.pi)) := hf.comp (contDiff_id.add contDiff_const)
  have hh₀ := h₀ hf hΛ hC hD hbf
  have hhπ := hπ hfs hΛ hC hD hbs
  have hhr := hr hf hC hD hΛ (fun k hk => hb k (hk.trans (le_max_right _ _)))
  rw [full_circle_decomposition Λ hf.continuous hp]
  unfold fullCircleStationaryExpansion
  have he (a b r x y : ℂ) : a+b+r-(x+y) = ((a-x)+(b-y))+r := by ring
  rw [he]
  have hn (a b r : ℂ) : ‖a+b+r‖ ≤ ‖a‖+‖b‖+‖r‖ :=
    (norm_add_le (a+b) r).trans (add_le_add (norm_add_le a b) (le_refl ‖r‖))
  apply (hn _ _ _).trans
  calc
    _ ≤ ((Real.pi/(Λ/2))^(1/2:ℝ) * ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))) *
        (A₀*C*D^(2*(n+1)+2)) +
        ((Real.pi/(Λ/2))^(1/2:ℝ) * ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))) *
        (Aπ*C*D^(2*(n+1)+2)) + B*C*D^M/Λ^M := add_le_add (add_le_add hh₀ hhπ) hhr
    _ = _ := by ring

 theorem fullCircleStationaryExpansion_operators {Λ : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    fullCircleStationaryExpansion Λ f n =
      Complex.exp (Complex.I*(Λ:ℂ))*((Λ^(-1/2:ℝ):ℝ):ℂ)*
        (∑ j ∈ Finset.range (n+1), ((Λ⁻¹:ℝ):ℂ)^j*directStationaryOperator j f 0) +
      conj (Complex.exp (Complex.I*(Λ:ℂ))*((Λ^(-1/2:ℝ):ℝ):ℂ)*
        (∑ j ∈ Finset.range (n+1), ((Λ⁻¹:ℝ):ℂ)^j*
          directStationaryOperator j (fun θ => conj (f (θ+Real.pi))) 0)) := by
  have hfs : ContDiff ℝ ∞ (fun θ => conj (f (θ+Real.pi))) :=
    Complex.conjCLE.contDiff.comp (hf.comp (contDiff_id.add contDiff_const))
  unfold fullCircleStationaryExpansion
  rw [stationary_expansion_direct_operators hΛ hf,stationary_expansion_direct_operators hΛ hfs]
  simp only [mul_assoc]

end PlanarFalconer

end OAI
