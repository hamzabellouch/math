import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMatrixGroup
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalEigencharacters
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SeparateFiniteIndexDensity
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace OAI

/-! # Closed linear stabilizers in the polynomial matrix topology

Membership of a matrix translate in a subspace is a family of polynomial
equations, obtained from its annihilating linear functionals. Consequently
the finite-index common eigenspace stabilizer is dense and fixes that
eigenspace under a connected matrix group.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

variable {K : Type*} [Field K] {n : ℕ}

def linearAction : PolynomialMatrixGroup K n ≃*
    ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
  mulEquivGL.trans (Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K)))

theorem linearAction_apply (g : PolynomialMatrixGroup K n) (v : Fin n → K) :
    linearAction g v = Matrix.mulVec (entries g) v := rfl

def functionalPolynomial (φ : Module.Dual K (Fin n → K)) (v : Fin n → K) :
    MvPolynomial (Coord n) K :=
  ∑ i, ∑ j, MvPolynomial.C (φ (fun k => if i = k then 1 else 0)) *
    MvPolynomial.X (false, i, j) * MvPolynomial.C (v j)

theorem eval_functionalPolynomial (φ : Module.Dual K (Fin n → K))
    (v : Fin n → K) (g : PolynomialMatrixGroup K n) :
    MvPolynomial.eval (coordinates g).coord (functionalPolynomial φ v) =
      φ (linearAction g v) := by
  rw [linearAction_apply, LinearMap.pi_apply_eq_sum_univ]
  simp [functionalPolynomial, coordinates, Matrix.mulVec, dotProduct,
    Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]

theorem isClosed_linearAction_mem (W : Submodule K (Fin n → K)) (v : Fin n → K) :
    IsClosed {g : PolynomialMatrixGroup K n | linearAction g v ∈ W} := by
  have he : {g : PolynomialMatrixGroup K n | linearAction g v ∈ W} =
      ⋂ (φ : Module.Dual K (Fin n → K)) (_ : φ ∈ W.dualAnnihilator),
        {g | φ (linearAction g v) = 0} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).symm
  rw [he]
  apply isClosed_iInter
  intro φ
  apply isClosed_iInter
  intro _
  have hc := (AffinePolynomialPoint.isClosed_zeroSet (functionalPolynomial φ v)).preimage
    inducing_coordinates.continuous
  simpa only [Set.preimage_ofPred_eq, eval_functionalPolynomial] using hc

theorem isClosed_preserves_subspace (W : Submodule K (Fin n → K)) :
    IsClosed {g : PolynomialMatrixGroup K n | ∀ v ∈ W, linearAction g v ∈ W} := by
  have he : {g : PolynomialMatrixGroup K n | ∀ v ∈ W, linearAction g v ∈ W} =
      ⋂ (v : Fin n → K) (_ : v ∈ W), {g | linearAction g v ∈ W} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [he]
  exact isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_linearAction_mem W v

theorem connected_invariant_commonEigenspace
    {G : Type*} [Group G] [TopologicalSpace G] [PreconnectedSpace G]
    [SeparatelyContinuousMul G] [ContinuousInv G]
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι)
    (A : Subgroup G) [A.Normal] (χ : A → K)
    (hχ : normalCommonEigenspace A (linearAction.toMonoidHom.comp ι) χ ≠ ⊥) :
    ∀ g : G, ∀ v ∈ normalCommonEigenspace A (linearAction.toMonoidHom.comp ι) χ,
      linearAction (ι g) v ∈ normalCommonEigenspace A (linearAction.toMonoidHom.comp ι) χ := by
  let ρ := linearAction.toMonoidHom.comp ι
  obtain ⟨H, hH, hpres⟩ := exists_finiteIndex_preserving_commonEigenspace A ρ χ hχ
  let := hH
  let W := normalCommonEigenspace A ρ χ
  have hclosed : IsClosed {g : G | ∀ v ∈ W, ρ g v ∈ W} :=
    (isClosed_preserves_subspace W).preimage hι
  have hcontains : closure (H : Set G) ⊆ {g : G | ∀ v ∈ W, ρ g v ∈ W} :=
    closure_minimal hpres hclosed
  have he := separateClosure_eq_top_of_finiteIndex H
  intro g
  apply hcontains
  change g ∈ separateClosure H
  rw [he]
  trivial

theorem connected_normal_invariant_eigenspace (D : Subgroup (PolynomialMatrixGroup K n))
    [PreconnectedSpace D] (A : Subgroup D) [A.Normal] (χ : A → K)
    (hχ : normalCommonEigenspace A (linearAction.toMonoidHom.comp D.subtype) χ ≠ ⊥) :
    ∀ g : D, ∀ v ∈ normalCommonEigenspace A (linearAction.toMonoidHom.comp D.subtype) χ,
      linearAction (g : PolynomialMatrixGroup K n) v ∈
        normalCommonEigenspace A (linearAction.toMonoidHom.comp D.subtype) χ := by
  let : SeparatelyContinuousMul D :=
    Topology.IsInducing.subtypeVal.separatelyContinuousMul D.subtype
  let : ContinuousInv D := Topology.IsInducing.subtypeVal.continuousInv (fun _ => rfl)
  exact connected_invariant_commonEigenspace D.subtype continuous_subtype_val A χ hχ

open scoped IsMulCommutative in
theorem connected_normalAbelian_invariant_eigenspace [IsAlgClosed K]
    [Nontrivial (Fin n → K)] (D : Subgroup (PolynomialMatrixGroup K n))
    [PreconnectedSpace D] (A : Subgroup D) [A.Normal] [IsMulCommutative A] :
    ∃ χ : A → K,
      normalCommonEigenspace A (linearAction.toMonoidHom.comp D.subtype) χ ≠ ⊥ ∧
      ∀ g : D, ∀ v ∈ normalCommonEigenspace A (linearAction.toMonoidHom.comp D.subtype) χ,
        linearAction (g : PolynomialMatrixGroup K n) v ∈
          normalCommonEigenspace A (linearAction.toMonoidHom.comp D.subtype) χ := by
  obtain ⟨χ, _, _, hχ, _⟩ := exists_finiteIndex_nonzero_commonEigenspace A
    (linearAction.toMonoidHom.comp D.subtype)
  exact ⟨χ, hχ, connected_normal_invariant_eigenspace D A χ hχ⟩

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
