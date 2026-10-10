import OAI.GroupTheory.PolycyclicRecognition.Algebra.ComplexCharacterLift
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexTriangularExponential

namespace OAI

/-! # Simultaneous additive lifts of triangular matrix characters -/

noncomputable section
namespace PolycyclicRecognition

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SimplyConnectedSpace G] [LocallyPathConnectedSpace G]
  [AddCommGroup V] [Module ℝ V] {n : ℕ}

def complexMatrixDiagonalHom (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hu : ∀ g, (ρ g).IsUpperTriangular) (i : Fin n) : G →* ℂ where
  toFun g := ρ g i i
  map_one' := by simp
  map_mul' g h := by rw [map_mul, complex_triangular_mul_diag _ _ (hu g) (hu h)]

/-- Simply connectedness lifts all diagonal characters, preserving the
specified linear weights on exponential curves. -/
theorem exists_lifted_complex_matrix_weights
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (hu : ∀ g, (ρ g).IsUpperTriangular)
    (d : V →ₗ[ℝ] (Fin n → ℂ)) (Exp : V → G)
    (hExp0 : Exp 0 = 1) (hcurve : ∀ x, Continuous (fun t : ℝ => Exp (t • x)))
    (he : ∀ x i, ρ (Exp x) i i = Complex.exp (d x i)) :
    ∃ π : G →* Multiplicative (Fin n → ℂ),
      Continuous (fun g => (π g).toAdd) ∧ ∀ x, (π (Exp x)).toAdd = d x := by
  let χ (i : Fin n) := (complexMatrixDiagonalHom ρ hu i).toHomUnits
  have hc (i : Fin n) : Continuous (fun g => (χ i g : ℂ)) :=
    (continuous_apply i).comp ((continuous_apply i).comp hρ)
  choose p hp heq using fun i => exists_additive_lift_complex_character (χ i) (hc i)
  have hex (i : Fin n) (x : V) : (p i (Exp x)).toAdd = d x i := by
    have h := additive_lift_complex_character_on_curve (χ i) (p i) (hp i) (heq i)
      (fun t : ℝ => Exp (t • x)) (hcurve x) (by simpa using hExp0) (d x i)
      (fun t => by
        change ρ (Exp (t • x)) i i = _
        rw [he, map_smul]
        rfl) 1
    simpa only [one_smul, Complex.ofReal_one, one_mul] using h
  let π : G →* Multiplicative (Fin n → ℂ) :=
    { toFun := fun g => Multiplicative.ofAdd (fun i => (p i g).toAdd)
      map_one' := by apply Multiplicative.ext; ext i; exact congrArg Multiplicative.toAdd (map_one (p i))
      map_mul' := by
        intro g h
        apply Multiplicative.ext
        ext i
        exact congrArg Multiplicative.toAdd (map_mul (p i) g h) }
  refine ⟨π, continuous_pi hp, fun x => ?_⟩
  funext i
  exact hex i x

end PolycyclicRecognition

end

end OAI
