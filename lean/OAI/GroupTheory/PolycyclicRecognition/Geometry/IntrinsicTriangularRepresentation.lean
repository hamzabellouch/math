import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicCartanFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicCanonicalHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FaithfulTriangularRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RepresentationKernelAdjoint
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularAdjointSolvable
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularExponentialInjective

namespace OAI

/-! # A faithful triangular group representation without Dixmier

The intrinsic height kernel makes the Cartan construction and its overlap
faithful. A kernel element of the resulting representation acts trivially
on the Lie algebra, hence has zero intrinsic height and lies in the known
nilpotent kernel, where faithfulness follows from the finite logarithm.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

theorem exists_intrinsic_faithful_triangular_representation
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp) :
    ∃ m : ℕ, 0 < m ∧
      ∃ j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ,
      ∃ ρ : G →* (Matrix (Fin m) (Fin m) ℝ)ˣ,
        Function.Injective j ∧ (∀ x, (j x).IsUpperTriangular) ∧
        (∀ x ∈ T.kernelIdeal, IsNilpotent (j x)) ∧
        Continuous ρ ∧ Function.Injective ρ ∧
        ∀ x, ρ (Exp x) = algebraExpUnit (j x) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace E G
  let := T.lieAlgebra_isSolvable
  let W := Fin (Module.finrank ℝ (HeightSpace T.character)) → ℝ
  let q : HeightSpace T.character ≃ₗ[ℝ] W := (Module.finBasis ℝ (HeightSpace T.character)).equivFun
  obtain ⟨π, hπ, hπExp, _, _, _, hkill, _⟩ := exists_intrinsic_canonical_height_with_kernel T q hExp
  have hπc : Continuous π := hπ
  obtain ⟨H, hH, hn, _, hspan, _⟩ := exists_cartan_model T
  let := hH
  obtain ⟨F⟩ := nonempty_intrinsic_cartanFactorModel T q Exp hExp π hπc hπExp H
  obtain ⟨m, hm, j, hj, hu, hnrep⟩ := exists_positive_faithful_triangular_representation T
  have hsN : Function.Surjective F.ExpN := by
    obtain ⟨c, hc⟩ := ((nilpotentPublishedInputs.haar _ F.N).2 F.ExpN F.isExpN
      (F.N.tangent_nilpotent hn)).1
    intro n
    obtain ⟨x, hx⟩ := c.surjective n
    exact ⟨x, (hc x).symm.trans hx⟩
  have hsD : Function.Surjective F.ExpD := by
    obtain ⟨c, hc⟩ := ((nilpotentPublishedInputs.haar _ F.D).2 F.ExpD F.isExpD
      (F.D.tangent_nilpotent inferInstance)).1
    intro d
    obtain ⟨x, hx⟩ := c.surjective d
    exact ⟨x, (hc x).symm.trans hx⟩
  obtain ⟨ρ, hρ, he⟩ := F.exists_integrated_representation_of_root_preimages hExp
    (fun x hx y hxy => exponential_eq_of_mem_intrinsic_height_kernel T q Exp hExp π hπc hπExp
      (cartanRootIdeal_le_kernel H T hx) hxy) hn hspan hsN hsD j
  obtain ⟨K, ExpK, hExpK, κ, _, _, hκExp, hrange⟩ :=
    exists_closed_intrinsic_height_kernel T q Exp hExp π hπc hπExp
  obtain ⟨cK, hcK⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal K).2 ExpK hExpK
    (K.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  have hfaithful : Function.Injective ρ := by
    apply (MonoidHom.ker_eq_bot_iff ρ).mp
    apply le_antisymm _ bot_le
    intro g hg
    change ρ g = 1 at hg
    change g = 1
    have had := adjointLinearMap_eq_id_of_representation_kernel hExp j hj ρ he g hg
    have hmatrix : adjointMatrixHom T.basis g = 1 := by
      change LinearMap.toMatrix T.basis T.basis
        (adjointLinearMap (E := E) g).toLinearMap = 1
      rw [had]
      exact map_one (LinearMap.toMatrixAlgEquiv T.basis)
    have hheight : π g = 1 := hkill g hmatrix
    have hgrange : g ∈ Set.range κ := by
      rw [hrange]
      exact hheight
    obtain ⟨k, hk⟩ := hgrange
    obtain ⟨v, hv⟩ := cK.surjective k
    have hexpg : Exp (K.equiv.symm v) = g := by
      rw [← hκExp, K.equiv.apply_symm_apply, ← hcK, hv, hk]
    have hexp : NormedSpace.exp (j (K.equiv.symm v)) = 1 := by
      have h := congrArg Units.val (show ρ (Exp (K.equiv.symm v)) = 1 by rw [hexpg, hg])
      simp only [he, coe_algebraExpUnit, Units.val_one] at h
      exact h
    have hz : (K.equiv.symm v : GroupLieAlgebra (𝓘(ℝ, E)) G) = 0 := by
      apply hj
      exact ((triangular_exp_eq_one_iff _ (hu _)).mp hexp).trans (map_zero j).symm
    rw [← hexpg, hz, hExp.map_zero]
  exact ⟨m, hm, j, ρ, hj, hu, hnrep, hρ, hfaithful, he⟩

/-- The real triangular exponential and the faithful group representation
make the intrinsic exponential injective, without assuming a global chart. -/
theorem intrinsic_exponential_injective
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp) :
    Function.Injective Exp := by
  obtain ⟨m, _, j, ρ, hj, hu, _, _, _, he⟩ :=
    exists_intrinsic_faithful_triangular_representation T Exp hExp
  let S := Matrix.blockTriangularSubalgebra ℝ ℝ (id : Fin m → Fin m)
  let jS : E →ₗ[ℝ] S := j.toLinearMap.codRestrict S.toSubmodule hu
  intro x y hxy
  apply hj
  have h := congrArg (fun g => (ρ g : Matrix (Fin m) (Fin m) ℝ)) hxy
  simp only [he, coe_algebraExpUnit] at h
  have heq : NormedSpace.exp (jS x) = NormedSpace.exp (jS y) := by
    apply Subtype.ext
    change ((NormedSpace.exp (jS x) : RealTriangularAlgebra m) :
      Matrix (Fin m) (Fin m) ℝ) = (NormedSpace.exp (jS y) : RealTriangularAlgebra m)
    rw [realTriangularAlgebra_coe_exp, realTriangularAlgebra_coe_exp]
    exact h
  exact congrArg Subtype.val (realTriangularAlgebra_exp_injective m heq)

end PolycyclicRecognition

end

end OAI
