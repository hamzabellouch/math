import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.InverseAngularTerms
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereInverseArbitraryPower

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory
open scoped ContDiff Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma sphereAxisSmooth_integrableND (Λ : ℝ) (e : V) (ψ : V → ℂ) (hψ : Continuous ψ)
    (f : SmoothFunctionND V) :
    Integrable (fun w => Complex.exp (Complex.I*Λ*(inner ℝ w e : ℂ))*(ψ w*f.1 w))
      (canonicalSphereMeasureND V) := by
  apply integrable_canonicalSphereMeasureND
  exact (by fun_prop : Continuous (fun w => Complex.exp (Complex.I*Λ*(inner ℝ w e : ℂ)))).mul
    (hψ.mul (smoothFunctionND_contDiff f).continuous)

noncomputable def sphereAxisFunctionalND (Λ : ℝ) (e : V) (ψ : V → ℂ) (hψ : Continuous ψ) :
    SmoothFunctionND V →ₗ[ℂ] ℂ where
  toFun f := sphereAxisIntegralND Λ e (fun w => ψ w*f.1 w)
  map_add' f g := by
    change (∫ w, Complex.exp (Complex.I*Λ*(inner ℝ w e : ℂ))*(ψ w*(f.1 w+g.1 w))
      ∂canonicalSphereMeasureND V)=_
    simp only [mul_add]
    exact integral_add (sphereAxisSmooth_integrableND Λ e ψ hψ f)
      (sphereAxisSmooth_integrableND Λ e ψ hψ g)
  map_smul' z f := by
    change sphereAxisIntegralND Λ e (fun w => ψ w*(z*f.1 w)) =
      z*sphereAxisIntegralND Λ e (fun w => ψ w*f.1 w)
    simpa only [mul_left_comm _ z] using sphereAxisIntegralND_const_mul Λ e
      (fun w => ψ w*f.1 w) z

lemma sphereAxisFunctionalND_apply (Λ : ℝ) (e : V) (ψ : V → ℂ) (hψ : Continuous ψ)
    (f : SmoothFunctionND V) :
    sphereAxisFunctionalND Λ e ψ hψ f = sphereAxisIntegralND Λ e (fun w => ψ w*f.1 w) := rfl

variable {n : ℕ} {α : Type*} [DecidableEq α]

lemma sphereAxisInverse_productND (j : ℕ) (S : Finset α)
    (f : α → SmoothFunctionND (SphereAmbientND n)) (D : α → ℝ) (hD : ∀ i ∈ S, D i ≠ 0)
    (Λ : ℝ) (e : SphereAmbientND n) (ψ : SphereAmbientND n → ℂ) (hψ : Continuous ψ) :
    sphereAxisIntegralND Λ e (fun w => ψ w*(sphereBND j (smoothFinsetProductND S f)).1 w) =
      ((inverseAngularTermsND j S).map (fun a =>
        (a.1*((∏ i ∈ S, D i^(a.2 i).length:ℝ):ℂ)) *
          sphereAxisIntegralND Λ e (fun w => ψ w*
            (smoothFinsetProductND S (fun i => normalizedAngularWordND (D i) (a.2 i) (f i))).1 w))).sum := by
  have hh := congrArg (sphereAxisFunctionalND Λ e ψ hψ)
    (inverseAngularTermsND_normalized_expansion j S f D hD)
  simpa only [map_list_sum,List.map_map,Function.comp_def,map_smul,smul_eq_mul,
    sphereAxisFunctionalND_apply] using hh

theorem sphere_inverse_fixed_productND (ψ : SphereAmbientND n → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (κ T C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) :
    ∃ J : ℕ, ∃ E : ℝ, 0 ≤ E ∧ ∀ (S : Finset α)
      (f : α → SmoothFunctionND (SphereAmbientND n)) (D : α → ℝ)
      (R A Λ : ℝ) (e : SphereAmbientND n),
      (∀ i ∈ S, D i ≠ 0) → 1 ≤ R → 1 ≤ A → R^κ ≤ Λ → A ≤ R^2 →
      A^2/Λ ≤ R^(-κ) → ‖e‖=1 →
      ψ =ᶠ[𝓝 e] (fun _ => 1) → ψ =ᶠ[𝓝 (-e)] (fun _ => 0) →
      (∀ k ≤ 2*(J+1)+n+3, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ k (smoothFinsetProductND S f).1 w‖ ≤ C*A^k) →
      ‖Complex.exp (Complex.I*Λ)*(smoothFinsetProductND S f).1 e -
        ((Λ^((n:ℝ)/2):ℝ):ℂ) *
          (∑ j ∈ Finset.range (J+1), (Λ:ℂ)^(-(j:ℤ)) *
            ((inverseAngularTermsND j S).map (fun a =>
              (a.1*((∏ i ∈ S, D i^(a.2 i).length:ℝ):ℂ)) *
                sphereAxisIntegralND Λ e (fun w => ψ w*
                  (smoothFinsetProductND S (fun i =>
                    normalizedAngularWordND (D i) (a.2 i) (f i))).1 w))).sum)‖ ≤ E*R^(-T) := by
  obtain ⟨J,E,hE,hEb⟩ := sphere_inverse_fixed_arbitrary_powerND ψ hψ κ T C hκ hC
  refine ⟨J,E,hE,?_⟩
  intro S f D R A Λ e hD hR hA hΛ hup hratio he hplus hminus hb
  simpa only [sphereAxisInverse_productND _ S f D hD Λ e ψ hψ.continuous] using
    hEb (smoothFinsetProductND S f) R A Λ e hR hA hΛ hup hratio he hplus hminus hb

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
