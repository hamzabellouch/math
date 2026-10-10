import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectProductTopology
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangulableLieModel
import Mathlib.Topology.Algebra.Group.Subgroup

namespace OAI

/-! # Compact rotational modifications

An invariant character into a compact abelian automorphism group has a closed
graph inside the semidirect extension. The original group and this graph both
have proper cocompact inclusions.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Topology

variable {G K : Type*} [Group G] [CommGroup K]
  [TopologicalSpace G] [TopologicalSpace K]
  (α : K →* MulAut G) (τ : G →* K)
  (hinv : ∀ k g, τ (α k g) = τ g)

attribute [local instance] semidirectProductTopology

/-- The inverse-character graph, with the multiplication inherited from the
semidirect extension. The character is invariant under the compact action. -/
def rotationalTwist : Subgroup (G ⋊[α] K) where
  carrier := {p | p.right = (τ p.left)⁻¹}
  one_mem' := by simp
  mul_mem' := by
    intro p q hp hq
    change p.right * q.right = (τ (p.left * α p.right q.left))⁻¹
    rw [map_mul, hinv, hp, hq, mul_inv_rev, mul_comm]
  inv_mem' := by
    intro p hp
    change p.right⁻¹ = (τ (α p.right⁻¹ p.left⁻¹))⁻¹
    rw [hinv, map_inv, inv_inv, hp, inv_inv]

/-- Removing a rotation changes multiplication, while preserving the
underlying topological space. -/
def rotationalTwistHomeomorph [IsTopologicalGroup K] (hτ : Continuous τ) :
    rotationalTwist α τ hinv ≃ₜ G where
  toFun p := p.val.left
  invFun g := ⟨⟨g, (τ g)⁻¹⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact p.property.symm
  right_inv _ := rfl
  continuous_toFun := (continuous_semidirect_left α).comp continuous_subtype_val
  continuous_invFun :=
    ((semidirectProductHomeomorph α).symm.continuous.comp
      (continuous_id.prodMk hτ.inv)).subtype_mk (fun _ => rfl)

variable [IsTopologicalGroup G] [IsTopologicalGroup K] [T2Space K]

omit [IsTopologicalGroup G] in
include hinv in
theorem rotationalTwist_isClosed (hτ : Continuous τ) :
    IsClosed (rotationalTwist α τ hinv : Set (G ⋊[α] K)) :=
  isClosed_eq (continuous_semidirect_right α)
    (hτ.comp (continuous_semidirect_left α)).inv

omit [IsTopologicalGroup G] [IsTopologicalGroup K] in
/-- The original group has a proper inclusion into its semidirect extension. -/
theorem semidirect_inl_isProperMap :
    IsProperMap (SemidirectProduct.inl : G → G ⋊[α] K) := by
  have hc : IsClosed (range (fun g : G => (g, (1 : K)))) := by
    have he : range (fun g : G => (g, (1 : K))) = {p : G × K | p.2 = 1} := by
      ext ⟨g, k⟩
      simp [eq_comm]
    rw [he]
    exact isClosed_eq continuous_snd continuous_const
  exact ((semidirectProductHomeomorph α).symm.isClosedEmbedding.comp
    ⟨isEmbedding_prodMkLeft (1 : K), hc⟩).isProperMap

omit [IsTopologicalGroup G] in
/-- The modified group is likewise properly included. -/
theorem rotationalTwist_subtype_isProperMap (hτ : Continuous τ) :
    IsProperMap (rotationalTwist α τ hinv).subtype :=
  (rotationalTwist_isClosed α τ hinv hτ).isClosedEmbedding_subtypeVal.isProperMap

variable [CompactSpace K]

/-- The rotation subgroup is one fixed compact right-coset cover. -/
def semidirect_inl_properCocompact : ProperCocompactHom G (G ⋊[α] K) where
  hom := SemidirectProduct.inl
  proper := semidirect_inl_isProperMap α
  cover := ⟨range (SemidirectProduct.inr : K → G ⋊[α] K),
    isCompact_range (continuous_semidirect_inr α), fun p =>
      ⟨p.left, SemidirectProduct.inr p.right, mem_range_self _,
        SemidirectProduct.inl_left_mul_inr_right p⟩⟩

/-- The same compact subgroup covers the inverse-character graph, so no
metric estimate or triangulability assertion is hidden in this arrow. -/
def rotationalTwist_properCocompact (hτ : Continuous τ) :
    ProperCocompactHom (rotationalTwist α τ hinv) (G ⋊[α] K) where
  hom := (rotationalTwist α τ hinv).subtype
  proper := rotationalTwist_subtype_isProperMap α τ hinv hτ
  cover := by
    refine ⟨range (SemidirectProduct.inr : K → G ⋊[α] K),
      isCompact_range (continuous_semidirect_inr α), fun p => ?_⟩
    refine ⟨⟨⟨p.left, (τ p.left)⁻¹⟩, rfl⟩,
      SemidirectProduct.inr (τ p.left * p.right), mem_range_self _, ?_⟩
    apply SemidirectProduct.ext <;> simp

omit [IsTopologicalGroup G] in
/-- Compatible proper chain metrics turn a compact rotational modification
into an actual quasi-isometry by composing the two proved arrows. -/
theorem rotationalTwist_nonempty_metricQuasiEquivalence
    (hτ : Continuous τ) (dG : ProperChainMetric G)
    (dT : ProperChainMetric (rotationalTwist α τ hinv))
    (dS : ProperChainMetric (G ⋊[α] K)) :
    letI := dG.compatibleMetric
    letI := dT.compatibleMetric
    Nonempty (MetricQuasiEquivalence G (rotationalTwist α τ hinv)) := by
  let := dS.compatibleMetric
  let := dG.compatibleMetric
  let := dT.compatibleMetric
  obtain ⟨e₁⟩ := (semidirect_inl_properCocompact α).nonempty_metricQuasiEquivalence dG dS
  obtain ⟨e₂⟩ := (rotationalTwist_properCocompact α τ hinv hτ).nonempty_metricQuasiEquivalence dT dS
  exact ⟨@MetricQuasiEquivalence.trans _ _ _ dG.compatibleMetric.toPseudoMetricSpace
    dS.compatibleMetric.toPseudoMetricSpace dT.compatibleMetric.toPseudoMetricSpace e₁
    (@MetricQuasiEquivalence.symm _ _ dT.compatibleMetric.toPseudoMetricSpace
      dS.compatibleMetric.toPseudoMetricSpace e₂)⟩

end PolycyclicRecognition

end

end OAI
