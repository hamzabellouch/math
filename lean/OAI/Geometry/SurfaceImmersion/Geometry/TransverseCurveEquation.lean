import OAI.Geometry.SurfaceImmersion.Geometry.LocalDefiningFunction

namespace OAI

/-! A transverse embedded parametrized curve has a local smooth defining equation.
The construction uses the inverse of its first coordinate. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.TransverseSmallFunction

lemma embedded_curve_equation {γ : ℝ → Base} (hγ : ContDiff ℝ ∞ γ)
    (he : Topology.IsEmbedding γ) (t : ℝ)
    (ht : deriv (fun s => (γ s).1) t ≠ 0) :
    ∃ U : Set Base, IsOpen U ∧ γ t ∈ U ∧
      ∃ f : Base → ℝ, ContDiffOn ℝ ∞ f U ∧
        (∀ x ∈ Set.range γ ∩ U, f x = 0) ∧ fderiv ℝ f (γ t) (0, 1) = 1 := by
  let X : ℝ → ℝ := fun s => (γ s).1
  have hX : ContDiff ℝ ∞ X := contDiff_fst.comp hγ
  have hXt := hX.hasStrictDerivAt (x := t) (by simp)
  let e := (hXt.hasStrictFDerivAt_equiv ht).toOpenPartialHomeomorph X
  have heX : (e : ℝ → ℝ) = X := rfl
  have hts : t ∈ e.source := (hXt.hasStrictFDerivAt_equiv ht).mem_toOpenPartialHomeomorph_source
  let Z : Set ℝ := {s | deriv X s ≠ 0}
  have hZ : IsOpen Z := isOpen_ne.preimage (hX.continuous_deriv (by simp))
  let W : Set ℝ := e.target ∩ e.symm ⁻¹' Z
  have hW : IsOpen W := e.isOpen_inter_preimage_symm hZ
  have htW : X t ∈ W := by
    refine ⟨e.map_source hts, ?_⟩
    change deriv X (e.symm (e t)) ≠ 0
    rw [e.left_inv hts]
    exact ht
  have hi : ContDiffOn ℝ ∞ e.symm W := by
    intro y hy
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm_deriv hy.2 hy.1
    · rw [heX]
      exact (hX.differentiable (by simp) (e.symm y)).hasDerivAt
    · rw [heX]
      exact hX.contDiffAt
  obtain ⟨V, hV, hpre⟩ := he.isInducing.isOpen_iff.mp e.open_source
  have htV : γ t ∈ V := by
    have : t ∈ γ ⁻¹' V := by rw [hpre]; exact hts
    exact this
  let U : Set Base := V ∩ Prod.fst ⁻¹' W
  have hU : IsOpen U := hV.inter (hW.preimage continuous_fst)
  let f : Base → ℝ := fun x => x.2 - (γ (e.symm x.1)).2
  have hf : ContDiffOn ℝ ∞ f U := by
    apply contDiffOn_snd.sub
    exact (contDiff_snd.comp hγ).contDiffOn.comp
      (hi.comp contDiffOn_fst (fun x hx => hx.2)) (fun _ _ => mem_univ _)
  have hz : ∀ x ∈ Set.range γ ∩ U, f x = 0 := by
    rintro x ⟨⟨s, rfl⟩, hx⟩
    have hs : s ∈ e.source := by
      rw [← hpre]
      exact hx.1
    change (γ s).2 - (γ (e.symm (e s))).2 = 0
    rw [e.left_inv hs, sub_self]
  have hpU : γ t ∈ U := ⟨htV, htW⟩
  have hiAt : DifferentiableAt ℝ (fun y => (γ (e.symm y)).2) (X t) :=
    ((contDiff_snd.comp hγ).contDiffAt.comp (X t)
      ((hi.contDiffAt (hW.mem_nhds htW)))).differentiableAt (by simp)
  have hfst : HasFDerivAt (fun x : Base => x.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (γ t) :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun x : Base => x.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (γ t) :=
    hasFDerivAt_snd
  have hd := hsnd.sub (hiAt.hasFDerivAt.comp (γ t) hfst)
  change HasFDerivAt f _ (γ t) at hd
  refine ⟨U, hU, hpU, f, hf, hz, ?_⟩
  rw [hd.fderiv]
  simp

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
