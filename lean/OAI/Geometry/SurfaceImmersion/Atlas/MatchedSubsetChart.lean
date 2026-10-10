import OAI.Geometry.SurfaceImmersion.Atlas.SubmersionFiberLineChart

namespace OAI

/-! Restrict a local homeomorphism to matched subsets, with their induced
topologies. The subsets themselves need not be open. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem matched_subset_chart (e : OpenPartialHomeomorph X Y)
    (S : Set X) (T : Set Y) (p : X) (hp : p ∈ e.source) (hpS : p ∈ S)
    (hmatch : ∀ x ∈ e.source, x ∈ S ↔ e x ∈ T) :
    ∃ c : OpenPartialHomeomorph S T,
      (⟨p,hpS⟩ : S) ∈ c.source ∧ c.source = ((↑) ⁻¹' e.source) ∧
      c.target = ((↑) ⁻¹' e.target) ∧
      (∀ x ∈ c.source, (c x).val = e x.val) ∧
      (∀ y ∈ c.target, (c.symm y).val = e.symm y.val) := by
  classical
  have hpT : e p ∈ T := (hmatch p hp).mp hpS
  have hback (y : T) (hy : y.val ∈ e.target) : e.symm y.val ∈ S := by
    apply (hmatch _ (e.map_target hy)).mpr
    rw [e.right_inv hy]
    exact y.property
  let F : S → T := fun x => if hx : x.val ∈ e.source then
      ⟨e x.val,(hmatch x.val hx).mp x.property⟩ else ⟨e p,hpT⟩
  let G : T → S := fun y => if hy : y.val ∈ e.target then
      ⟨e.symm y.val,hback y hy⟩ else ⟨p,hpS⟩
  have hF (x : S) (hx : x.val ∈ e.source) : (F x).val = e x.val := by simp [F,hx]
  have hG (y : T) (hy : y.val ∈ e.target) : (G y).val = e.symm y.val := by simp [G,hy]
  let c : OpenPartialHomeomorph S T := {
    toFun := F
    invFun := G
    source := (↑) ⁻¹' e.source
    target := (↑) ⁻¹' e.target
    map_source' := by
      intro x hx
      change (F x).val ∈ e.target
      rw [hF x hx]
      exact e.map_source hx
    map_target' := by
      intro y hy
      change (G y).val ∈ e.source
      rw [hG y hy]
      exact e.map_target hy
    left_inv' := by
      intro x hx
      apply Subtype.ext
      have hy : (F x).val ∈ e.target := by rw [hF x hx]; exact e.map_source hx
      rw [hG _ hy,hF x hx,e.left_inv hx]
    right_inv' := by
      intro y hy
      apply Subtype.ext
      have hx : (G y).val ∈ e.source := by rw [hG y hy]; exact e.map_target hy
      rw [hF _ hx,hG y hy,e.right_inv hy]
    open_source := e.open_source.preimage continuous_subtype_val
    open_target := e.open_target.preimage continuous_subtype_val
    continuousOn_toFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      exact (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx)).congr hF
    continuousOn_invFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      exact (e.continuousOn_symm.comp continuous_subtype_val.continuousOn (fun _ hy => hy)).congr hG }
  exact ⟨c,hp,rfl,rfl,hF,hG⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
