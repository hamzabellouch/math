import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexWeightFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntegratedNilradicalRotations
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealTorusAdjoint
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorAutomorphismDescent

namespace OAI

/-! # Compact Cartan rotations on the original simply connected group -/

noncomputable section
namespace PolycyclicRecognition
open Set
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

include hExp in
omit [H.IsCartanSubalgebra] in
/- The actual tangent conjugation preserves the nilpotent ideal. -/
theorem cartan_conjugation_mem (h : H) (x : T.kernelIdeal) :
    adjointLinearMap (E := E) (G := G) (Exp h) (x : GroupLieAlgebra (𝓘(ℝ,E)) G) ∈ T.kernelIdeal := by
  have he := adjointLinearMap_exponential hExp (h : GroupLieAlgebra (𝓘(ℝ, E)) G) 1
  simp only [one_smul] at he
  rw [he]
  let U : Submodule ℝ E := T.kernelIdeal.toSubmodule
  exact exp_apply_mem_of_stable U U.closed_of_finiteDimensional
    (groupAdjointOperator (E := E) (G := G) h)
    (fun w hw => T.kernelIdeal.lie_mem hw) x.property

/- Conjugation in the factorization agrees with the actual adjoint map
on nilpotent exponential coordinates. -/
omit [H.IsCartanSubalgebra] in
theorem action_cartan_exponential (h : H) (x : T.kernelIdeal) :
    F.action (F.ExpD (F.D.equiv h)) (F.ExpN (F.N.equiv x)) =
      F.ExpN (F.N.equiv ⟨adjointLinearMap (E := E) (G := G) (Exp h) (x : GroupLieAlgebra (𝓘(ℝ,E)) G),
        cartan_conjugation_mem hExp h x⟩) := by
  apply F.closedN.injective
  rw [F.conjugation, F.compatibleD, F.compatibleN, F.compatibleN]
  exact conjugation_exponential hExp (Exp h) (x : GroupLieAlgebra (𝓘(ℝ,E)) G)

omit [H.IsCartanSubalgebra] in
theorem expN_surjective :
    Function.Surjective (fun x : T.kernelIdeal => F.ExpN (F.N.equiv x)) := by
  obtain ⟨c,hc⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal F.N).2
    F.ExpN F.isExpN (F.N.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  intro n
  obtain ⟨x,hx⟩ := c.surjective n
  refine ⟨F.N.equiv.symm x,?_⟩
  change F.ExpN (F.N.equiv (F.N.equiv.symm x)) = n
  rw [F.N.equiv.apply_symm_apply]
  rwa [hc] at hx

theorem expD_surjective :
    Function.Surjective (fun h : H => F.ExpD (F.D.equiv h)) := by
  obtain ⟨c,hc⟩ := ((nilpotentPublishedInputs.haar H F.D).2
    F.ExpD F.isExpD (F.D.tangent_nilpotent inferInstance)).1
  intro d
  obtain ⟨x,hx⟩ := c.surjective d
  refine ⟨F.D.equiv.symm x,?_⟩
  change F.ExpD (F.D.equiv (F.D.equiv.symm x)) = d
  rw [F.D.equiv.apply_symm_apply]
  rwa [hc] at hx

/- The compact nilradical rotations commute with the actual Cartan
conjugation, including away from the identity. -/
include hExp in
theorem rotation_commutes_action
    (α : realRotationTorus (GroupLieAlgebra (𝓘(ℝ, E)) G) H →* MulAut F.N.carrier)
    (hα : ∀ z x, α z (F.ExpN (F.N.equiv x)) =
      F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) :
    ∀ z d n, α z (F.action d n) = F.action d (α z n) := by
  intro z
  apply commutes_of_surjective_coordinates
    (fun x : T.kernelIdeal => F.ExpN (F.N.equiv x))
    (fun h : H => F.ExpD (F.D.equiv h)) F.expN_surjective F.expD_surjective
    (α z) (fun d => F.action d) (T.nilradicalRotation H z)
    (fun h x => ⟨adjointLinearMap (E := E) (G := G) (Exp h)
      (x : GroupLieAlgebra (𝓘(ℝ,E)) G),cartan_conjugation_mem hExp h x⟩)
    (hα z) (F.action_cartan_exponential hExp)
  intro h x
  apply Subtype.ext
  exact realTorusOperator_commutes_cartan_conjugation H hExp z h
    (x : GroupLieAlgebra (𝓘(ℝ,E)) G)

/- The compact rotations fix the entire overlap of the two actual factors. -/
theorem rotation_fixes_overlap
    (α : realRotationTorus (GroupLieAlgebra (𝓘(ℝ, E)) G) H →* MulAut F.N.carrier)
    (hα : ∀ z x, α z (F.ExpN (F.N.equiv x)) =
      F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) :
    ∀ z n d, F.inclusionN n = F.inclusionD d → α z n = n := by
  intro z n d hnd
  have ho : F.inclusionN n ∈ Set.range F.inclusionN ∩ Set.range F.inclusionD :=
    ⟨⟨n,rfl⟩,⟨d,hnd.symm⟩⟩
  rw [F.overlap] at ho
  obtain ⟨x,hx,hex⟩ := ho
  have hn : F.ExpN (F.N.equiv ⟨x,hx.1⟩) = n :=
    F.closedN.injective ((F.compatibleN ⟨x,hx.1⟩).trans hex)
  rw [← hn,hα]
  congr 2
  apply Subtype.ext
  exact realTorusOperator_fixes_cartan _ H z ⟨x,hx.2⟩

/- The compact rotations descend to a jointly continuous action on the
original group, fixing its Cartan factor and acting as prescribed on its
closed nilpotent factor. No group integration premise is used. -/
include hExp in
theorem exists_compact_rotation_action :
    ∃ β : realRotationTorus (GroupLieAlgebra (𝓘(ℝ, E)) G) H →* MulAut G,
      Continuous (fun p : realRotationTorus (GroupLieAlgebra (𝓘(ℝ, E)) G) H × G =>
        β p.1 p.2) ∧
      ∀ z (x : T.kernelIdeal) d,
        β z (F.inclusionN (F.ExpN (F.N.equiv x)) * F.inclusionD d) =
          F.inclusionN (F.ExpN (F.N.equiv (T.nilradicalRotation H z x))) *
            F.inclusionD d := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ,E)) ⊤
  let α := nilradicalRotations T H F.N F.ExpN F.isExpN
  have hα := continuous_nilradicalRotations T H F.N F.ExpN F.isExpN
  have heα := nilradicalRotations_exp T H F.N F.ExpN F.isExpN
  let β := descendedFactorAction F.inclusionN F.inclusionD F.action F.conjugation
    F.surjective α (F.rotation_commutes_action hExp α heα) (F.rotation_fixes_overlap α heα)
  refine ⟨β,continuous_descendedFactorAction F.inclusionN F.inclusionD F.action F.conjugation
    F.surjective α (F.rotation_commutes_action hExp α heα) (F.rotation_fixes_overlap α heα)
    F.closedN.continuous F.closedD.continuous hα F.openProduct,?_⟩
  intro z x d
  change descendedFactorAction _ _ _ _ _ _ _ _ _ _ = _
  rw [descendedFactorAction_product,heα]

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI
