import OAI.GroupTheory.PolycyclicRecognition.Geometry.RepresentationKernelAdjoint
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicCanonicalHeight
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Group.Units

namespace OAI

/-! # Recovering canonical height continuously from a faithful representation -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem exists_local_height_factor_of_representation
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A) (hj : Function.Injective j)
    (ρ : G →* Aˣ) (he : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (π : G →* Multiplicative W) (P : (Fin a → ℝ) →L[ℝ] W)
    (hP : ∀ g, (π g).toAdd = P (fun i => Real.log (adjointMatrixHom T.basis g i i))) :
    ∃ f : Aˣ → Multiplicative W, ContinuousAt f 1 ∧ f 1 = 1 ∧ ∀ g, f (ρ g) = π g := by
  obtain ⟨p, hp⟩ := j.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hj)
  have hpj (x : GroupLieAlgebra (𝓘(ℝ, E)) G) : p (j x) = x := LinearMap.congr_fun hp x
  let diag : Aˣ → Fin a → ℝ := fun u i =>
    T.basis.coord i (p ((u : A) * j (T.basis i) * (u⁻¹ : Aˣ)))
  have hd1 (i : Fin a) : diag 1 i = 1 := by
    change T.basis.coord i (p ((1 : A) * j (T.basis i) * 1)) = 1
    rw [one_mul, mul_one, hpj]
    simp
  have hdc (i : Fin a) : Continuous (fun u => diag u i) := by
    let c := (T.basis.coord i).comp p
    exact c.continuous_of_finiteDimensional.comp
      ((Units.continuous_val.mul continuous_const).mul
        (Units.continuous_val.comp continuous_inv))
  have hdg (g : G) (i : Fin a) : diag (ρ g) i = adjointMatrixHom T.basis g i i := by
    change T.basis.coord i (p ((ρ g : A) * j (T.basis i) * (ρ g)⁻¹)) = _
    rw [← lieHom_adjoint_of_exponential_intertwining hExp j ρ he]
    apply (congrArg (T.basis.coord i) (hpj (adjointLinearMap (E := E) g (T.basis i)))).trans
    change T.basis.repr (adjointLinearMap (E := E) g (T.basis i)) i =
      LinearMap.toMatrix T.basis T.basis (adjointLinearMap (E := E) g).toLinearMap i i
    exact (LinearMap.toMatrix_apply T.basis T.basis
      (adjointLinearMap (E := E) g).toLinearMap i i).symm
  let f : Aˣ → Multiplicative W := fun u =>
    Multiplicative.ofAdd (P (fun i => Real.log (diag u i)))
  refine ⟨f, ?_, ?_, ?_⟩
  · apply P.continuous.continuousAt.comp
    apply continuousAt_pi.mpr
    intro i
    exact (hdc i).continuousAt.log (by rw [hd1]; exact one_ne_zero)
  · apply Multiplicative.ext
    change P (fun i => Real.log (diag 1 i)) = 0
    simp only [hd1, Real.log_one]
    exact map_zero P
  · intro g
    apply Multiplicative.ext
    change P (fun i => Real.log (diag (ρ g) i)) = (π g).toAdd
    simp only [hdg]
    exact (hP g).symm

end PolycyclicRecognition

end

end OAI
