import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieConjugationDifferential

namespace OAI

/-! # Right translation of an invariant vector field

The change in a left-invariant field under right multiplication is the
actual differential of conjugation. No representation is used.
-/

noncomputable section
namespace PolycyclicRecognition

open Function
open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem mfderiv_mul_right_invariant (a g : G) (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => h * a) g
        (mulInvariantVectorField v g) =
      mulInvariantVectorField (conjugationDifferentialHom a⁻¹ v) (g * a) := by
  have hL : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g * h) :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ⊤)).mdifferentiable (by simp)
  have hR : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => h * a) :=
    (contMDiff_mul_right (I := 𝓘(ℝ, E)) (n := ⊤)).mdifferentiable (by simp)
  have hL' : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => (g * a) * h) :=
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ⊤)).mdifferentiable (by simp)
  have hC := (contMDiff_conjugation (E := E) a⁻¹).mdifferentiable (by simp)
  have heq : (fun h : G => h * a) ∘ (fun h : G => g * h) =
      (fun h : G => (g * a) * h) ∘ (MulAut.conj a⁻¹).toMonoidHom := by
    ext h
    simp only [comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, inv_inv]
    group
  have h₁ := mfderiv_comp (I' := 𝓘(ℝ, E)) (1 : G) (hR (g * 1)) (hL 1)
  have h₂ := mfderiv_comp (I' := 𝓘(ℝ, E)) (1 : G)
    (hL' ((MulAut.conj a⁻¹).toMonoidHom 1)) (hC 1)
  rw [heq] at h₁
  have hh := congrArg (fun D : E →L[ℝ] E => D v) (h₁.symm.trans h₂)
  have hbase : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => h * a) (g * 1) : E →L[ℝ] E) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => h * a) g := by
    congr 1
    exact mul_one g
  have htarget : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => (g * a) * h)
      ((MulAut.conj a⁻¹).toMonoidHom 1) : E →L[ℝ] E) =
      mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => (g * a) * h) 1 := by
    congr 1
    exact map_one _
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => h * a) (g * 1))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => g * h) 1) v) =
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => (g * a) * h)
      ((MulAut.conj a⁻¹).toMonoidHom 1))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (MulAut.conj a⁻¹).toMonoidHom 1) v) at hh
  rw [hbase, htarget] at hh
  exact hh

theorem mfderiv_mul_right_inverse_invariant (a g : G)
    (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => h * a⁻¹) (g * a)
        (mulInvariantVectorField v (g * a)) =
      mulInvariantVectorField (conjugationDifferentialHom a v) g := by
  have hh := mfderiv_mul_right_invariant a⁻¹ (g * a) v
  simp only [inv_inv] at hh
  let B : G → E := fun h => mulInvariantVectorField (conjugationDifferentialHom a v) h
  exact hh.trans (congrArg B (by group))

end PolycyclicRecognition

end

end OAI
