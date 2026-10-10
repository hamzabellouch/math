import OAI.GroupTheory.PolycyclicRecognition.Geometry.RepresentedAdjoint

namespace OAI

/-! # A faithful Lie representation detects the adjoint action of its group kernel -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem adjointLinearMap_eq_id_of_representation_kernel
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A) (hj : Function.Injective j)
    (ρ : G →* Aˣ) (he : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (g : G) (hg : ρ g = 1) :
    adjointLinearMap (E := E) g = ContinuousLinearMap.id ℝ E := by
  ext x
  apply hj
  have hcurve (t : ℝ) :
      NormedSpace.exp (t • j (adjointLinearMap (E := E) g x)) =
        NormedSpace.exp (t • j x) := by
    have hc : Exp (t • adjointLinearMap (E := E) g x) =
        g * Exp (t • x) * g⁻¹ := by
      exact (congrArg Exp (map_smul (adjointLinearMap (E := E) g) t x).symm).trans
        (conjugation_exponential hExp g (t • x)).symm
    have h := congrArg ρ hc
    rw [map_mul, map_mul, map_inv, hg, inv_one, one_mul, mul_one] at h
    have hv := congrArg (fun u : Aˣ => (u : A)) ((he _).symm.trans (h.trans (he _)))
    simp only [coe_algebraExpUnit] at hv
    exact (congrArg NormedSpace.exp (j.map_smul t (adjointLinearMap (E := E) g x))).symm.trans
      (hv.trans (congrArg NormedSpace.exp (j.map_smul t x)))
  have hd₁ : HasDerivAt (fun t : ℝ => NormedSpace.exp
      (t • j (adjointLinearMap (E := E) g x))) (j (adjointLinearMap (E := E) g x)) 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const (j (adjointLinearMap (E := E) g x)) (0 : ℝ)
  have hd₂ : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • j x)) (j x) 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const (j x) (0 : ℝ)
  rw [show (fun t : ℝ => NormedSpace.exp (t • j (adjointLinearMap (E := E) g x))) =
    (fun t : ℝ => NormedSpace.exp (t • j x)) from funext hcurve] at hd₁
  exact hd₁.unique hd₂

/-- Exponential compatibility also intertwines the full adjoint action. -/
theorem lieHom_adjoint_of_exponential_intertwining
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A)
    (ρ : G →* Aˣ) (he : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (g : G) (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    j (adjointLinearMap (E := E) g x) = (ρ g : A) * j x * (ρ g)⁻¹ := by
  let y : A := (ρ g : A) * j x * (ρ g)⁻¹
  have hcurve (t : ℝ) : NormedSpace.exp (t • j (adjointLinearMap (E := E) g x)) =
      NormedSpace.exp (t • y) := by
    have hc : Exp (t • adjointLinearMap (E := E) g x) = g * Exp (t • x) * g⁻¹ := by
      exact (congrArg Exp (map_smul (adjointLinearMap (E := E) g) t x).symm).trans
        (conjugation_exponential hExp g (t • x)).symm
    have h := congrArg ρ hc
    rw [map_mul, map_mul, map_inv] at h
    have hu := (he _).symm.trans (h.trans
      ((congrArg (fun u : Aˣ => ρ g * u * (ρ g)⁻¹) (he (t • x))).trans
        (algebraExpUnit_conj (ρ g) (j (t • x))).symm))
    have hv := congrArg (fun u : Aˣ => (u : A)) hu
    simp only [coe_algebraExpUnit] at hv
    have hs : (ρ g : A) * j (t • x) * (ρ g)⁻¹ = t • y := by
      calc
        (ρ g : A) * j (t • x) * (ρ g)⁻¹ = (ρ g : A) * (t • j x) * (ρ g)⁻¹ :=
          congrArg (fun a : A => (ρ g : A) * a * (ρ g)⁻¹) (j.map_smul t x)
        _ = t • y := by simp only [mul_smul_comm, smul_mul_assoc]; rfl
    exact (congrArg NormedSpace.exp (j.map_smul t (adjointLinearMap (E := E) g x))).symm.trans
      (hv.trans (congrArg NormedSpace.exp hs))
  have hd₁ : HasDerivAt (fun t : ℝ => NormedSpace.exp
      (t • j (adjointLinearMap (E := E) g x))) (j (adjointLinearMap (E := E) g x)) 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const (j (adjointLinearMap (E := E) g x)) (0 : ℝ)
  have hd₂ : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • y)) y 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      hasDerivAt_exp_smul_const y (0 : ℝ)
  rw [show (fun t : ℝ => NormedSpace.exp (t • j (adjointLinearMap (E := E) g x))) =
    (fun t : ℝ => NormedSpace.exp (t • y)) from funext hcurve] at hd₁
  exact hd₁.unique hd₂

end PolycyclicRecognition

end

end OAI
