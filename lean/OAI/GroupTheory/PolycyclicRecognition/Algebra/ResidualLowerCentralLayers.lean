import OAI.GroupTheory.PolycyclicRecognition.Lattices.JointFixedLayerAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialLowerCentralProjection
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionConjugation
import OAI.GroupTheory.PolycyclicRecognition.Algebra.EndomorphismCommutatorFiltration

namespace OAI

/-! # Group commutators on the joint-fixed lower-central layers -/

noncomputable section
namespace PolycyclicRecognition
open LieModule
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q] [IsMulCommutative Q]
  {E : GroupExtension L G Q}
  {hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g)} {qs : List Q}

namespace JointFixedReductionData
variable (D : JointFixedReductionData E hsmooth qs)

abbrev residualKernelLayer (k : ℕ) : Subgroup (jointFixedLieSubalgebra D.operators) :=
  polynomialLieIdealSubgroup _ (lowerCentralSeries ℝ _ _ k)

def residualLayer (k : ℕ) : Subgroup (FactorExtension D.residualSystem) :=
  (D.residualKernelLayer k).map (FactorExtension.inl D.residualSystem)

instance residualLayer_normal (k : ℕ) : (D.residualLayer k).Normal where
  conj_mem g hg a := by
    obtain ⟨x, hx, rfl⟩ := hg
    let E₀ := FactorExtension.groupExtension D.residualSystem
    refine ⟨E₀.conjAct a x, ?_, ?_⟩
    · rw [FactorExtension.conjugation_inl]
      exact polynomialSubalgebra_conjugate_mem _ _ _
        (jointFixed_action_preserves_lowerCentral D.operators (D.action a.right)
          (fun S hS => D.action_commutes S hS _) k x hx) a.left
    · exact E₀.inl_conjAct_comm

def residualLayerEquiv (k : ℕ) : D.residualKernelLayer k ≃* D.residualLayer k :=
  (D.residualKernelLayer k).equivMapOfInjective _ (FactorExtension.inl_injective _)

def residualLayerProjection (k : ℕ) : D.residualLayer k →*
    Multiplicative (D.lowerCentralLayer k) :=
  (polynomialLowerCentralProjection _ k).comp (D.residualLayerEquiv k).symm.toMonoidHom

omit [LieRing.IsNilpotent L] [IsMulCommutative Q] in
@[simp] theorem residualLayerProjection_equiv (k : ℕ) (x : D.residualKernelLayer k) :
    D.residualLayerProjection k (D.residualLayerEquiv k x) =
      polynomialLowerCentralProjection _ k x := by
  simp only [residualLayerProjection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

omit [LieRing.IsNilpotent L] [IsMulCommutative Q] in
theorem residualLayerProjection_kernel_le (k : ℕ) :
    (D.residualLayerProjection k).ker.map (D.residualLayer k).subtype ≤ D.residualLayer (k + 1) := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨x, rfl⟩ := (D.residualLayerEquiv k).surjective a
  have hx : (x : jointFixedLieSubalgebra D.operators) ∈ lowerCentralSeries ℝ
      (jointFixedLieSubalgebra D.operators) (jointFixedLieSubalgebra D.operators) (k + 1) := by
    apply (polynomialLowerCentralProjection_eq_one_iff _ k x).mp
    change D.residualLayerProjection k (D.residualLayerEquiv k x) = 1 at ha
    rwa [residualLayerProjection_equiv] at ha
  exact ⟨x, hx, rfl⟩

omit [LieRing.IsNilpotent L] [IsMulCommutative Q] in
theorem residualLayerProjection_equivariant (k : ℕ)
    (g : FactorExtension D.residualSystem) (a : D.residualLayer k) :
    (D.residualLayerProjection k (MulAut.conjNormal (H := D.residualLayer k) g a)).toAdd =
      D.layerAction k g.right (D.residualLayerProjection k a).toAdd := by
  obtain ⟨x, rfl⟩ := (D.residualLayerEquiv k).surjective a
  let E₀ := FactorExtension.groupExtension D.residualSystem
  let y : D.residualKernelLayer k := ⟨E₀.conjAct g x, by
    rw [FactorExtension.conjugation_inl]
    exact polynomialSubalgebra_conjugate_mem _ _ _
      (jointFixed_action_preserves_lowerCentral D.operators (D.action g.right)
        (fun S hS => D.action_commutes S hS _) k x x.property) g.left⟩
  have he : MulAut.conjNormal (H := D.residualLayer k) g (D.residualLayerEquiv k x) =
      D.residualLayerEquiv k y := by
    apply Subtype.ext
    exact E₀.inl_conjAct_comm.symm
  rw [he, residualLayerProjection_equiv, residualLayerProjection_equiv]
  apply (Submodule.Quotient.eq _).mpr
  change E₀.conjAct g x - D.residualSystem.action g.right x ∈
    lowerCentralSeries ℝ (jointFixedLieSubalgebra D.operators) _ (k + 1)
  rw [FactorExtension.conjugation_inl]
  exact polynomialSubalgebra_inner_difference _ g.left k _
    (jointFixed_action_preserves_lowerCentral D.operators (D.action g.right)
      (fun S hS => D.action_commutes S hS _) k x x.property)

omit [LieRing.IsNilpotent L] in
theorem residualLayer_commutator_bound
    (hgen : Subgroup.closure {q | q ∈ qs} = ⊤) (k : ℕ) :
    ∃ c, relativeCommutatorSeries ⊤ (D.residualLayer k) c ≤ D.residualLayer (k + 1) := by
  obtain ⟨c, hc⟩ := D.layer_action_filtration hgen k
  let ρ := (D.layerAction k).comp (FactorExtension.projection D.residualSystem)
  have hρ : linearActionFiltration
      (fun g : (⊤ : Subgroup (FactorExtension D.residualSystem)) => ρ g - 1) c = ⊥ := by
    apply eq_bot_iff.mpr
    exact (linearActionFiltration_comp_le (fun q => D.layerAction k q - 1)
      (fun g : (⊤ : Subgroup (FactorExtension D.residualSystem)) => g.val.right) c).trans
      (le_of_eq hc)
  exact ⟨c, (relativeCommutatorSeries_le_kernel_of_endFiltration ⊤ (D.residualLayer k)
    ρ (D.residualLayerProjection k) (D.residualLayerProjection_equivariant k) c hρ).trans
      (D.residualLayerProjection_kernel_le k)⟩

end JointFixedReductionData
end PolycyclicRecognition

end

end OAI
