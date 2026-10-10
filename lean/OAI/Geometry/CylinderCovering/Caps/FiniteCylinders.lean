import OAI.Geometry.CylinderCovering.Caps.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Convexity.AmbientCylinderBridge
import OAI.Geometry.CylinderCovering.Angular.Geometry

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace CylinderCovering.HalfheightFinite
open RuledApproximation

theorem intrinsic_base_realization {u : Space} {B : Set Space}
    (h : BaseProperties u B) :
    ∃ C : Cylinder, C.axis = u ∧ Subtype.val '' C.base = B ∧
      IsCompact C.base ∧ Convex ℝ C.base ∧
      C.carrier = RadialSweep.cylinder u B ∧ C.area = TriangularCovering.area B := by
  let C := Cylinder.fromAmbientBase u h.1 B
  refine ⟨C, rfl, Cylinder.fromAmbientBase_image u h.1 B h.2.2.2.2.2,
    Cylinder.fromAmbientBase_compact u h.1 B h.2.2.2.2.2 h.2.1, ?_,
    Cylinder.fromAmbientBase_carrier u h.1 B h.2.2.2.2.2,
    Cylinder.fromAmbientBase_area u h.1 B h.2.2.2.2.2⟩
  exact h.2.2.1.linear_preimage (Submodule.subtype _)

theorem intrinsic_two_families {δ : ℝ} {R : ℝ → ℝ}
    (h : FamilyConclusion δ R) (N : ℕ) (hN : 0 < N) :
    ∃ L U : Fin N → Cylinder,
      (∀ i,
        (L i).axis = firstAxis δ (midpoint N i) ∧
        (U i).axis = secondAxis δ (midpoint N i) ∧
        Subtype.val '' (L i).base = firstBase δ R N i ∧
        Subtype.val '' (U i).base = secondBase δ R N i ∧
        IsCompact (L i).base ∧ Convex ℝ (L i).base ∧
        IsCompact (U i).base ∧ Convex ℝ (U i).base) ∧
      tetrahedron ⊆ familySet L ∪ familySet U ∧
      familyArea L + familyArea U = totalArea δ R N := by
  have hlocal := (h.1 N hN).1
  choose L hL using (fun i => intrinsic_base_realization (hlocal i).1)
  choose U hU using (fun i => intrinsic_base_realization (hlocal i).2.1)
  refine ⟨L, U, ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hL i).1, (hU i).1, (hL i).2.1, (hU i).2.1,
      (hL i).2.2.1, (hL i).2.2.2.1, (hU i).2.2.1, (hU i).2.2.2.1⟩
  · intro z hz
    rcases (h.1 N hN).2 z hz with ⟨i, hi⟩ | ⟨i, hi⟩
    · left
      apply mem_iUnion.mpr
      exact ⟨i, (hL i).2.2.2.2.1.symm ▸ hi⟩
    · right
      apply mem_iUnion.mpr
      exact ⟨i, (hU i).2.2.2.2.1.symm ▸ hi⟩
  · unfold familyArea totalArea
    congr 1 <;> apply Finset.sum_congr rfl
    · intro i _
      exact (hL i).2.2.2.2.2
    · intro i _
      exact (hU i).2.2.2.2.2

theorem intrinsic_finite_realization {δ : ℝ} {R : ℝ → ℝ}
    (h : FamilyConclusion δ R) (N : ℕ) (hN : 0 < N) :
    ∃ C : Fin (2*N) → Cylinder,
      (∀ i, IsCompact (C i).base ∧ Convex ℝ (C i).base) ∧
      tetrahedron ⊆ familySet C ∧ familyArea C = totalArea δ R N := by
  obtain ⟨L, U, hprops, hcover, harea⟩ := intrinsic_two_families h N hN
  obtain ⟨C, hC, hset, hcost⟩ := AngularGeometry.pair_families
    (fun C : Cylinder => IsCompact C.base ∧ Convex ℝ C.base) L U
    (fun i => ⟨(hprops i).2.2.2.2.1, (hprops i).2.2.2.2.2.1⟩)
    (fun i => ⟨(hprops i).2.2.2.2.2.2.1, (hprops i).2.2.2.2.2.2.2⟩)
  exact ⟨C, hC, hset.symm ▸ hcover, hcost.trans harea⟩

end CylinderCovering.HalfheightFinite

end

end OAI
