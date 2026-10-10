import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialNaturality

namespace OAI

/-! # Differential information at the identity of a Lie homomorphism -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {E G F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [ChartedSpace F H] [Group H] [LieGroup (𝓘(ℝ, F)) ⊤ H]

/-- Differentiability at the identity suffices for a group homomorphism. -/
theorem mdifferentiable_hom_of_mdifferentiableAt_one (φ : G →* H)
    (hφ : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1) :
    MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ := by
  intro g
  have hleft : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun x : G => g⁻¹ * x) g :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := g⁻¹) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ⊤ (fun x : G => g⁻¹ * x)).mdifferentiableAt (by simp)
  have hbase := hφ.comp_of_eq g hleft (inv_mul_cancel g)
  have hright : MDifferentiableAt (𝓘(ℝ, F)) (𝓘(ℝ, F))
      (fun y : H => φ g * y) ((φ ∘ fun x : G => g⁻¹ * x) g) :=
    (contMDiff_mul_left (I := 𝓘(ℝ, F)) (a := φ g) :
      ContMDiff (𝓘(ℝ, F)) (𝓘(ℝ, F)) ⊤ (fun y : H => φ g * y)).mdifferentiableAt (by simp)
  have h := hright.comp g hbase
  have heq : (fun y : H => φ g * y) ∘ (φ ∘ fun x : G => g⁻¹ * x) = φ := by
    ext x
    simp only [Function.comp_apply, map_mul, map_inv, mul_inv_cancel_left]
  rw [heq] at h
  exact h

/-- The same translation argument propagates smoothness from the identity. -/
theorem contMDiff_hom_of_contMDiffAt_one (φ : G →* H)
    (hφ : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ φ 1) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ φ := by
  intro g
  have hleft : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : G => g⁻¹ * x) g :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (a := g⁻¹) :
      ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun x : G => g⁻¹ * x)).contMDiffAt
  have hbase := hφ.comp_of_eq hleft (inv_mul_cancel g)
  have hright : ContMDiffAt (𝓘(ℝ, F)) (𝓘(ℝ, F)) ∞
      (fun y : H => φ g * y) ((φ ∘ fun x : G => g⁻¹ * x) g) :=
    (contMDiff_mul_left (I := 𝓘(ℝ, F)) (a := φ g) :
      ContMDiff (𝓘(ℝ, F)) (𝓘(ℝ, F)) ∞ (fun y : H => φ g * y)).contMDiffAt
  have h := hright.comp g hbase
  have heq : (fun y : H => φ g * y) ∘ (φ ∘ fun x : G => g⁻¹ * x) = φ := by
    ext x
    simp only [Function.comp_apply, map_mul, map_inv, mul_inv_cancel_left]
  rw [heq] at h
  exact h

theorem IsGroupExponential.map_of_mdifferentiableAt_one [T2Space H]
    {ExpG : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    {ExpH : GroupLieAlgebra (𝓘(ℝ, F)) H → H}
    (hG : IsGroupExponential ExpG) (hH : IsGroupExponential ExpH)
    (φ : G →* H) (hφ : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    φ (ExpG v) = ExpH ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1) v) :=
  hG.map_of_mdifferentiable hH φ (mdifferentiable_hom_of_mdifferentiableAt_one φ hφ) v

/-- In exponential coordinates, a homomorphism is determined by its
differential at the identity. -/
theorem hom_eq_of_exponential_surjective [T2Space H]
    {ExpG : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    {ExpH : GroupLieAlgebra (𝓘(ℝ, F)) H → H}
    (hG : IsGroupExponential ExpG) (hH : IsGroupExponential ExpH)
    (hExpG : Function.Surjective ExpG)
    (φ ψ : G →* H)
    (hφ : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1)
    (hψ : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) ψ 1)
    (hderiv : ∀ v, mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) φ 1 v =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) ψ 1 v) : φ = ψ := by
  ext g
  obtain ⟨v, rfl⟩ := hExpG g
  rw [hG.map_of_mdifferentiableAt_one hH φ hφ,
    hG.map_of_mdifferentiableAt_one hH ψ hψ, hderiv]

end PolycyclicRecognition

end

end OAI
