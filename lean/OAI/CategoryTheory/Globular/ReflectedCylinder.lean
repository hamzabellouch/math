import OAI.CategoryTheory.Globular.CylinderPathLifting

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]
variable (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))

noncomputable def reflectedCylinder (Y : CutoffModels C q) : CutoffModels C q :=
  cutoffObject hC q (fullCylinder hC q n hnq H Y)

noncomputable def reflectedCylinderEndpoint (Y : CutoffModels C q) (ε : Bool) :
    reflectedCylinder hC q n hnq H Y ⟶ Y :=
  (cutoffEquiv hC q (fullCylinder hC q n hnq H Y) Y).symm
    (fullCylinderEndpoint hC q n hnq H Y ε)

theorem reflectedCylinderEndpoint_factor (Y : CutoffModels C q) (ε : Bool) :
    cutoffUnit hC q (fullCylinder hC q n hnq H Y) ≫
      (reflectedCylinderEndpoint hC q n hnq H Y ε).hom =
        fullCylinderEndpoint hC q n hnq H Y ε :=
  (cutoffEquiv hC q (fullCylinder hC q n hnq H Y) Y).apply_symm_apply _

theorem reflectedCylinderEndpoint_app (Y : CutoffModels C q) (ε : Bool) (j : ℕ)
    (a : (fullCylinder hC q n hnq H Y).underlying.Cell j) :
    (underlyingMap (reflectedCylinderEndpoint hC q n hnq H Y ε).hom).app j
      ((underlyingMap (cutoffUnit hC q (fullCylinder hC q n hnq H Y))).app j a) =
        (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)).app j a :=
  congrFun (congrArg (fun z => (underlyingMap z).app j)
    (reflectedCylinderEndpoint_factor hC q n hnq H Y ε)) a

theorem reflectedCylinderEndpoint_lifts (Y : CutoffModels C q) (ε : Bool) :
    (boundaryClass hC q 0).rlp (reflectedCylinderEndpoint hC q n hnq H Y ε) := by
  rw [boundaryClass_rlp_iff]
  intro j _
  by_cases hj : j ≤ q
  · rw [hasLiftingProperty_I_iff]
    intro bd y hy
    let η := underlyingMap (cutoffUnit hC q (fullCylinder hC q n hnq H Y))
    let p := underlyingMap (reflectedCylinderEndpoint hC q n hnq H Y ε).hom
    have hη := GlobularSet.Hom.boundaryMap_bijective_of_low η j
      (fun k hk => cutoffUnit_low_bijective hC q _ k (by omega))
    obtain ⟨bd',hbd'⟩ := hη.surjective bd
    have hf : η.comp p = underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε) :=
      congrArg underlyingMap (reflectedCylinderEndpoint_factor hC q n hnq H Y ε)
    have hy' : Y.obj.underlying.boundary j y =
        (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)).boundaryMap j bd' := by
      exact hy.trans ((congrArg (p.boundaryMap j) hbd'.symm).trans
        ((GlobularSet.Hom.boundaryMap_comp η p j bd').symm.trans
          (congrArg (fun f => f.boundaryMap j bd') hf)))
    obtain ⟨a,ha,hpa⟩ := fullCylinderEndpoint_liftsBoundary hC q n hnq H Y ε j bd' y hy'
    refine ⟨η.app j a, ?_, ?_⟩
    · exact (η.boundary_app j a).symm.trans
        ((congrArg (η.boundaryMap j) ha).trans hbd')
    · exact (reflectedCylinderEndpoint_app hC q n hnq H Y ε j a).trans hpa
  · exact hasLiftingProperty_I_of_unique _ j
      ((reflectedCylinder hC q n hnq H Y).property j (by omega)) (Y.property j (by omega))

theorem reflectedCylinder_joint_cells (Y : CutoffModels C q) (k : ℕ) (hk : n ≤ k)
    (t : (reflectedCylinder hC q n hnq H Y).obj.underlying.Cell k)
    (u : Bool → Y.obj.underlying.Cell (k+1))
    (hu : ∀ ε, (underlyingMap (reflectedCylinderEndpoint hC q n hnq H Y ε).hom).app k t =
      Y.obj.underlying.source k (u ε)) :
    ∃ l : (reflectedCylinder hC q n hnq H Y).obj.underlying.Cell (k+1),
      (reflectedCylinder hC q n hnq H Y).obj.underlying.source k l = t ∧
      ∀ ε, (underlyingMap (reflectedCylinderEndpoint hC q n hnq H Y ε).hom).app (k+1) l = u ε := by
  by_cases hkq : k ≤ q
  · let η := underlyingMap (cutoffUnit hC q (fullCylinder hC q n hnq H Y))
    obtain ⟨t',ht'⟩ := (cutoffUnit_low_bijective hC q (fullCylinder hC q n hnq H Y) k hkq).surjective t
    have hu' ε : (underlyingMap (fullCylinderEndpoint hC q n hnq H Y ε)).app k t' =
        Y.obj.underlying.source k (u ε) := by
      rw [← reflectedCylinderEndpoint_app, ht']
      exact hu ε
    obtain ⟨l,hl,hpl⟩ := fullCylinder_joint hC q n hnq H Y k hk t' u hu'
    refine ⟨η.app (k+1) l, ?_, ?_⟩
    · exact (η.source_app k l).symm.trans ((congrArg (η.app k) hl).trans ht')
    · intro ε
      exact (reflectedCylinderEndpoint_app hC q n hnq H Y ε (k+1) l).trans (hpl ε)
  · let R := reflectedCylinder hC q n hnq H Y
    refine ⟨R.obj.unitCell hC k t, R.obj.unitCell_source hC k t, ?_⟩
    intro ε
    apply (Y.obj.underlying.source_bijective_of_coskeletal q k Y.property (by omega)).injective
    rw [← (underlyingMap (reflectedCylinderEndpoint hC q n hnq H Y ε).hom).source_app,
      R.obj.unitCell_source]
    exact hu ε

noncomputable def cylinderPathData (Y : CutoffModels C q) : CutoffPathData hC q n Y where
  P := reflectedCylinder hC q n hnq H Y
  p₀ := reflectedCylinderEndpoint hC q n hnq H Y false
  p₁ := reflectedCylinderEndpoint hC q n hnq H Y true
  lifts₀ := reflectedCylinderEndpoint_lifts hC q n hnq H Y false
  lifts₁ := reflectedCylinderEndpoint_lifts hC q n hnq H Y true
  joint k hk t u₀ u₁ h₀ h₁ := by
    let R := reflectedCylinder hC q n hnq H Y
    let u : Bool → Y.obj.underlying.Cell (k+1) := fun ε =>
      if ε then cutoffCellEquiv hC q Y (k+1) u₁ else cutoffCellEquiv hC q Y (k+1) u₀
    have hu ε : (underlyingMap (reflectedCylinderEndpoint hC q n hnq H Y ε).hom).app k
        (cutoffCellEquiv hC q R k t) = Y.obj.underlying.source k (u ε) := by
      cases ε
      · have h := congrArg (cutoffCellEquiv hC q Y k) h₀
        erw [cutoffCellEquiv_comp, ← cutoffDiskFrame_source, cutoffCellEquiv_source] at h
        exact h
      · have h := congrArg (cutoffCellEquiv hC q Y k) h₁
        erw [cutoffCellEquiv_comp, ← cutoffDiskFrame_source, cutoffCellEquiv_source] at h
        exact h
    obtain ⟨l,hl,he⟩ := reflectedCylinder_joint_cells hC q n hnq H Y k hk
      (cutoffCellEquiv hC q R k t) u hu
    refine ⟨(cutoffCellEquiv hC q R (k+1)).symm l, ?_, ?_, ?_⟩
    · apply (cutoffCellEquiv hC q R k).injective
      erw [← cutoffDiskFrame_source,cutoffCellEquiv_source, Equiv.apply_symm_apply]
      exact hl
    · apply (cutoffCellEquiv hC q Y (k+1)).injective
      erw [cutoffCellEquiv_comp, Equiv.apply_symm_apply]
      exact he false
    · apply (cutoffCellEquiv hC q Y (k+1)).injective
      erw [cutoffCellEquiv_comp, Equiv.apply_symm_apply]
      exact he true

end GlobularTheory.Model
end Grothendieck

end OAI
