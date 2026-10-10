import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.EuclideanPairDirection
import OAI.MeasureTheory.FalconerCompletion.Graphs.ProfileChildCard

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real Attempt4FarGrid
open scoped ContDiff ComplexConjugate Topology ENNReal RealInnerProductSpace

section GeneralSphere
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma sphereAxisIntegralND_norm_bound_general (Λ : ℝ) (e : V)
    {b : V → ℂ} {C : ℝ} (hb : ∀ w, ‖w‖=1 → ‖b w‖≤C) :
    ‖sphereAxisIntegralND Λ e b‖≤C*(canonicalSphereMeasureND V).real univ := by
  apply norm_integral_le_of_norm_le_const
  filter_upwards [canonicalSphereMeasureND_ae_norm] with w hw
  change ‖spherePlaneWaveND Λ e w*b w‖≤C
  simpa only [norm_mul,spherePlaneWaveND_norm,one_mul] using hb w hw

lemma sphereAxisIntegralND_stronglyMeasurable {α : Type*} [MeasurableSpace α]
    (Λ : α → ℝ) (e : α → V) (b : α → V → ℂ)
    (hΛ : Measurable Λ) (he : Measurable e) (hb : Measurable (Function.uncurry b)) :
    StronglyMeasurable (fun x => sphereAxisIntegralND (Λ x) (e x) (b x)) := by
  unfold sphereAxisIntegralND
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  change Measurable (fun x : α×V => Complex.exp (Complex.I*(Λ x.1)*(inner ℝ x.2 (e x.1):ℂ))*b x.1 x.2)
  have hb' : Measurable (fun x : α×V => b x.1 x.2) := hb
  fun_prop
end GeneralSphere

lemma euclideanPairDirectionND_measurable {n : ℕ} :
    Measurable (euclideanPairDirectionND (n := n)) := by
  unfold euclideanPairDirectionND
  fun_prop

noncomputable def euclideanFarKernelND {n : ℕ} (Ψ : ℝ → ℝ) (v : ℝ)
    (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (x : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
      (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)))) : ℂ :=
  ∫ u : ℝ, (Ψ u:ℂ)*
    sphereAxisIntegralND (((2:ℝ)^v*dist x.1.1 x.1.2)*u) (euclideanPairDirectionND x.1) (b x.1)*
      conj (sphereAxisIntegralND (((2:ℝ)^v*dist x.2.1 x.2.2)*u) (euclideanPairDirectionND x.2) (c x.2))

lemma euclideanFarKernelND_stronglyMeasurable {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ)
    (v : ℝ) (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c)) :
    StronglyMeasurable (euclideanFarKernelND Ψ v b c) := by
  let V := EuclideanSpace ℝ (Fin (n+1))
  have hsph (b : (V×V) → V → ℂ) (hb : Measurable (Function.uncurry b)) :
      StronglyMeasurable (fun z : (V×V)×ℝ =>
        sphereAxisIntegralND (((2:ℝ)^v*dist z.1.1 z.1.2)*z.2) (euclideanPairDirectionND z.1) (b z.1)) := by
    apply sphereAxisIntegralND_stronglyMeasurable
    · fun_prop
    · exact euclideanPairDirectionND_measurable.comp measurable_fst
    · exact hb.comp (show Measurable (fun z : ((V×V)×ℝ)×V => (z.1.1,z.2)) by fun_prop)
  unfold euclideanFarKernelND
  apply StronglyMeasurable.integral_prod_right
  apply Measurable.stronglyMeasurable
  have h₁ := (hsph b hb).measurable.comp
    (show Measurable (fun z : ((V×V)×(V×V))×ℝ => (z.1.1,z.2)) by fun_prop)
  have h₂ := (hsph c hc).measurable.comp
    (show Measurable (fun z : ((V×V)×(V×V))×ℝ => (z.1.2,z.2)) by fun_prop)
  change Measurable (fun z : ((V×V)×(V×V))×ℝ => (Ψ z.2:ℂ)*
    sphereAxisIntegralND (((2:ℝ)^v*dist z.1.1.1 z.1.1.2)*z.2) (euclideanPairDirectionND z.1.1) (b z.1.1)*
      conj (sphereAxisIntegralND (((2:ℝ)^v*dist z.1.2.1 z.1.2.2)*z.2) (euclideanPairDirectionND z.1.2) (c z.1.2)))
  exact ((Complex.continuous_ofReal.measurable.comp (hΨ.comp measurable_snd)).mul h₁).mul
    (Complex.continuous_conj.measurable.comp h₂)

lemma euclideanFarKernelND_bound {n : ℕ} {Ψ : ℝ → ℝ}
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) {P C : ℝ} (hP : 0≤P) (hC : 0≤C)
    (hΨ : ∀ u, |Ψ u|≤P) (v : ℝ)
    (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (x : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
      (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))))
    (hb : ∀ w, ‖w‖=1 → ‖b x.1 w‖≤C) (hc : ∀ w, ‖w‖=1 → ‖c x.2 w‖≤C) :
    ‖euclideanFarKernelND Ψ v b c x‖≤
      (15/4:ℝ)*P*(C*(canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))).real univ)^2 := by
  have hh := radial_cutoff_integral_bound (f := fun u =>
    sphereAxisIntegralND (((2:ℝ)^v*dist x.1.1 x.1.2)*u) (euclideanPairDirectionND x.1) (b x.1)*
      conj (sphereAxisIntegralND (((2:ℝ)^v*dist x.2.1 x.2.2)*u) (euclideanPairDirectionND x.2) (c x.2)))
    (E := (C*(canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))).real univ)^2) hs hP hΨ (by
      intro u _
      rw [norm_mul,Complex.norm_conj,pow_two]
      exact mul_le_mul (sphereAxisIntegralND_norm_bound_general _ _ hb)
        (sphereAxisIntegralND_norm_bound_general _ _ hc) (norm_nonneg _) (by positivity))
  simpa only [euclideanFarKernelND,mul_assoc] using hh

theorem euclideanFarKernelND_integrable {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : Continuous Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (v : ℝ)
    (b c : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) → EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    (η : Measure ((EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) ×
      (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))))) [IsFiniteMeasure η]
    {C : ℝ} (hC : 0≤C)
    (hbd : ∀ᵐ x ∂η, (∀ w, ‖w‖=1 → ‖b x.1 w‖≤C) ∧ (∀ w, ‖w‖=1 → ‖c x.2 w‖≤C)) :
    Integrable (euclideanFarKernelND Ψ v b c) η := by
  obtain ⟨P,hP⟩ := (isCompact_Icc (a := (1/4:ℝ)) (b := 4)).exists_bound_of_continuousOn hΨ.continuousOn
  have hPa : ∀ u, |Ψ u| ≤ max P 0 := by
    intro u
    by_cases hu : u∈Icc (1/4:ℝ) 4
    · exact (hP u hu).trans (le_max_left _ _)
    · rw [radial_cutoff_mem_of_ne_zero hs hu,abs_zero]
      exact le_max_right _ _
  refine (integrable_const ((15/4:ℝ)*(max P 0)*
    (C*(canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))).real univ)^2)).mono'
    (euclideanFarKernelND_stronglyMeasurable hΨ.measurable v b c hb hc).aestronglyMeasurable ?_
  filter_upwards [hbd] with x hx
  exact euclideanFarKernelND_bound hs (le_max_right _ _) hC hPa v b c x hx.1 hx.2

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
