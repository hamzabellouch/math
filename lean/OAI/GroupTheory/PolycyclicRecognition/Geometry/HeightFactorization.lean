import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularChainPacking
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Algebra.Group.Subgroup.Basic

namespace OAI

/-!
# Factoring matrix height through the canonical quotient

A continuous vector-valued homomorphism killing the kernel of an open quotient
homomorphism factors continuously, hence real-linearly, through that quotient.
For triangular representations, unipotence on the kernel supplies this condition.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator

variable {G W V : Type*} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Quotient factorization is linear, not only an abstract additive map. -/
theorem exists_continuousLinearMap_of_quotient_kernel
    (π : G →* Multiplicative W) (τ : G →* Multiplicative V)
    (hπ : Function.Surjective π)
    (hquot : Topology.IsQuotientMap (fun g => (π g).toAdd))
    (hτ : Continuous (fun g => (τ g).toAdd)) (hker : π.ker ≤ τ.ker) :
    ∃ T : W →L[ℝ] V, ∀ g, T (π g).toAdd = (τ g).toAdd := by
  let F : Multiplicative W →* Multiplicative V := π.liftOfSurjective hπ ⟨τ, hker⟩
  have hF (g : G) : F (π g) = τ g := by
    simp only [F, MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply]
  let φ : W →+ V :=
    { toFun := fun w => (F (Multiplicative.ofAdd w)).toAdd
      map_zero' := by change (F 1).toAdd = 0; rw [map_one]; rfl
      map_add' := by
        intro a b
        change (F (Multiplicative.ofAdd a * Multiplicative.ofAdd b)).toAdd = _
        rw [map_mul, toAdd_mul] }
  have hφ : Continuous φ := by
    apply hquot.continuous_iff.mpr
    have heq : (fun g => φ (π g).toAdd) = (fun g => (τ g).toAdd) := by
      funext g
      change (F (π g)).toAdd = (τ g).toAdd
      rw [hF]
    change Continuous (fun g => φ (π g).toAdd)
    rw [heq]
    exact hτ
  exact ⟨φ.toRealLinearMap hφ, fun g => congrArg Multiplicative.toAdd (hF g)⟩

open PositiveTriangular

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Continuity of the matrix representation gives continuity of logarithmic
height, since the diagonal entries remain positive. -/
theorem continuous_triangular_height {n : ℕ} (ρ : G →* positiveTriangular n)
    (hρ : Continuous (fun g => matrix (ρ g))) :
    Continuous (fun g => (height (ρ g)).toAdd) := by
  apply continuous_pi
  intro i
  change Continuous (fun g => Real.log (matrix (ρ g) i i))
  exact (hρ.matrix_elem i i).log (fun g => (diagonal_pos (ρ g) i).ne')

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- A representation unipotent on the height kernel has diagonal height
factoring through the height quotient by a continuous linear map. -/
theorem exists_linear_height_factor_of_kernel_unipotent
    {n : ℕ} (π : G →* Multiplicative W) (ρ : G →* positiveTriangular n)
    (hπ : Function.Surjective π)
    (hquot : Topology.IsQuotientMap (fun g => (π g).toAdd))
    (hρheight : Continuous (fun g => (height (ρ g)).toAdd))
    (hker : ∀ g, π g = 1 → StrictUpper (matrix (ρ g) - 1)) :
    ∃ T : W →L[ℝ] (Fin n → ℝ), ∀ g, (height (ρ g)).toAdd = T (π g).toAdd := by
  have hk : π.ker ≤ ((height (n := n)).comp ρ).ker := by
    intro g hg
    apply MonoidHom.mem_ker.mpr
    apply Multiplicative.ext
    funext i
    have hi := hker g (MonoidHom.mem_ker.mp hg) i i le_rfl
    have hdiag : matrix (ρ g) i i = 1 := by
      change matrix (ρ g) i i - (1 : Matrix (Fin n) (Fin n) ℝ) i i = 0 at hi
      simpa only [Matrix.one_apply_eq] using sub_eq_zero.mp hi
    change Real.log (matrix (ρ g) i i) = 0
    rw [hdiag, Real.log_one]
  obtain ⟨T, hT⟩ := exists_continuousLinearMap_of_quotient_kernel π (height.comp ρ) hπ hquot hρheight hk
  exact ⟨T, fun g => (hT g).symm⟩

/-- The complete packing bridge needs only an open height quotient and a
compatible triangular representation unipotent on its kernel. -/
theorem polynomialBoundedChainPacking_of_unipotent_kernel
    {G W : Type*} [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MetricSpace G] [IsIsometricSMul G G] [ProperSpace G] [DecidableEq G]
    {n : ℕ} [NeZero n]
    (π : G →* Multiplicative W) (ρ : G →* positiveTriangular n)
    (hπ : Function.Surjective π)
    (hquot : Topology.IsQuotientMap (fun g => (π g).toAdd))
    (hρ : Topology.IsInducing (fun g => matrix (ρ g)))
    (hker : ∀ g, π g = 1 → StrictUpper (matrix (ρ g) - 1)) :
    PolynomialBoundedChainPacking (fun g => (π g).toAdd) := by
  obtain ⟨T, hT⟩ := exists_linear_height_factor_of_kernel_unipotent π ρ hπ hquot
    (continuous_triangular_height ρ hρ.continuous) hker
  exact polynomialBoundedChainPacking_of_factored_triangular_representation
    (fun g => (π g).toAdd) ρ hρ T hT

end PolycyclicRecognition

end

end OAI
