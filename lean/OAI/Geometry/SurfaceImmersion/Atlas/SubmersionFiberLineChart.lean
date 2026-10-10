import OAI.Geometry.SurfaceImmersion.Whitney.DoubleLocusChart

namespace OAI

/-! Submersion coordinates induce a genuine open interval chart on the
zero fiber, with its subspace topology. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X E : Type*} [TopologicalSpace X] [TopologicalSpace E] [Zero E]

theorem submersion_fiber_line_chart (f : X → E)
    (e : OpenPartialHomeomorph X (E × ℝ)) (p : X) (hp : p ∈ e.source) (hf : f p = 0)
    (he : ∀ x ∈ e.source, (e x).1 = f x) :
    ∃ c : OpenPartialHomeomorph {x : X // f x = 0} ℝ,
      (⟨p,hf⟩ : {x : X // f x = 0}) ∈ c.source ∧
      c.source = ((↑) ⁻¹' e.source) ∧
      (∀ x, c x = (e x.val).2) ∧
      (∀ t ∈ c.target, ((c.symm t).val) = e.symm (0,t)) := by
  classical
  let T : Set ℝ := {t | (0,t) ∈ e.target}
  have hzero (t : ℝ) (ht : t ∈ T) : f (e.symm (0,t)) = 0 := by
    rw [← he _ (e.map_target ht),e.right_inv ht]
  let I : ℝ → {x : X // f x = 0} := fun t =>
    if ht : t ∈ T then ⟨e.symm (0,t),hzero t ht⟩ else ⟨p,hf⟩
  have hI (t : ℝ) (ht : t ∈ T) : (I t).val = e.symm (0,t) := by simp [I,ht]
  have hpair (x : {x : X // f x = 0}) (hx : x.val ∈ e.source) :
      (0,(e x.val).2) = e x.val := by
    apply Prod.ext
    · exact (he x.val hx).trans x.property |>.symm
    · rfl
  let c : OpenPartialHomeomorph {x : X // f x = 0} ℝ := {
    toFun := fun x => (e x.val).2
    invFun := I
    source := (↑) ⁻¹' e.source
    target := T
    map_source' := by
      intro x hx
      change (0,(e x.val).2) ∈ e.target
      rw [hpair x hx]
      exact e.map_source hx
    map_target' := by
      intro t ht
      change (I t).val ∈ e.source
      rw [hI t ht]
      exact e.map_target ht
    left_inv' := by
      intro x hx
      apply Subtype.ext
      have ht : (e x.val).2 ∈ T := by
        change (0,(e x.val).2) ∈ e.target
        rw [hpair x hx]
        exact e.map_source hx
      rw [hI _ ht,hpair x hx,e.left_inv hx]
    right_inv' := by
      intro t ht
      rw [hI t ht,e.right_inv ht]
    open_source := e.open_source.preimage continuous_subtype_val
    open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
    continuousOn_toFun := (e.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx)).snd
    continuousOn_invFun := by
      apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
      have hc : ContinuousOn (fun t : ℝ => e.symm (0,t)) T :=
        e.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ht)
      exact hc.congr (fun t ht => hI t ht) }
  exact ⟨c,hp,rfl,fun _ => rfl,hI⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
