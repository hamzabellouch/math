import OAI.GroupTheory.PolycyclicRecognition.Algebra.TranslationLocalHomeomorph
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting

namespace OAI

/-! # A covering from two-sided translation coordinates

A local group parameterization whose left and right translations are global
homeomorphisms is a covering map. No associativity on the parameter space is
needed for this step.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Topology

variable {V G : Type*} [TopologicalSpace V] [Zero V]
  [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
  (f : V → G) (R : V → V ≃ₜ V)
  (hR : ∀ a x, f (R a x) = f x * f a)
  (hzero : f 0 = 1) (hf : IsLocalHomeomorph f)
  (hRinv : Continuous (fun p : V × V => (R p.1).symm p.2))
  (hRcont : Continuous (fun p : V × V => R p.1 p.2))

omit [IsTopologicalGroup G] in
include hzero hf in
private theorem kernel_discrete : DiscreteTopology (f ⁻¹' {1}) := by
  have heq : f '' (f ⁻¹' {1}) = {1} := by
    ext g
    constructor
    · rintro ⟨v, hv, rfl⟩; exact hv
    · rintro rfl; exact ⟨0, hzero, hzero⟩
  have : DiscreteTopology (f '' (f ⁻¹' {1})) := by rw [heq]; infer_instance
  exact (hf.isLocalHomeomorphOn.mono (subset_univ _)).discreteTopology_of_image

omit [Zero V] [IsTopologicalGroup G] in
include hR in
private theorem right_inverse_fiber (e : OpenPartialHomeomorph G V)
    (he : ∀ g ∈ e.source, f (e g) = g) {x : V} (hx : f x ∈ e.source) :
    f ((R (e (f x))).symm x) = 1 := by
  have hh := hR (e (f x)) ((R (e (f x))).symm x)
  rw [(R (e (f x))).apply_symm_apply, he _ hx] at hh
  apply mul_right_cancel (b := f x)
  simpa using hh.symm

include hR hf hRinv hRcont in
private def translationFiberHomeomorph (e : OpenPartialHomeomorph G V)
    (he : ∀ g ∈ e.source, f (e g) = g) :
    (f ⁻¹' e.source) ≃ₜ e.source × (f ⁻¹' {1}) where
  toFun x := (⟨f x, x.2⟩,
    ⟨(R (e (f x))).symm x, right_inverse_fiber f R hR e he x.2⟩)
  invFun p := ⟨R (e p.1) p.2, by
    change f (R (e p.1) p.2) ∈ e.source
    rw [hR, show f p.2 = 1 from p.2.2, one_mul, he _ p.1.2]
    exact p.1.2⟩
  left_inv x := Subtype.ext ((R (e (f x))).apply_symm_apply x)
  right_inv p := by
    have hh : f (R (e p.1) p.2) = p.1 := by
      rw [hR, show f p.2 = 1 from p.2.2, one_mul, he _ p.1.2]
    apply Prod.ext
    · exact Subtype.ext hh
    · apply Subtype.ext
      change (R (e (f (R (e p.1) p.2)))).symm (R (e p.1) p.2) = p.2
      rw [hh, (R (e p.1)).symm_apply_apply]
  continuous_toFun := by
    have hf' : Continuous (fun x : f ⁻¹' e.source => f x) :=
      hf.continuous.comp continuous_subtype_val
    have he' : Continuous (fun x : f ⁻¹' e.source => e (f x)) :=
      e.continuousOn_toFun.comp_continuous hf' (fun x => x.2)
    exact (hf'.subtype_mk _).prodMk
      ((hRinv.comp (he'.prodMk continuous_subtype_val)).subtype_mk _)
  continuous_invFun := by
    have he' : Continuous (fun p : e.source × (f ⁻¹' {1}) => e p.1) :=
      (e.continuousOn_toFun.comp_continuous continuous_subtype_val (fun x => x.2)).comp
        continuous_fst
    exact (hRcont.comp (he'.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

omit [IsTopologicalGroup G] in
include hR hzero hf hRinv hRcont in
theorem evenlyCovered_one_of_translations : IsEvenlyCovered f 1 (f ⁻¹' {1}) := by
  let _ := kernel_discrete f hzero hf
  let e := hf.localInverseAt 0
  have hmem : (1 : G) ∈ e.source := hzero ▸ hf.apply_self_mem_localInverseAt_source (x := 0)
  have he : ∀ g ∈ e.source, f (e g) = g := fun _ hg =>
    hf.apply_localInverseAt_of_mem hg
  exact ⟨inferInstance, e.source, hmem, e.open_source,
    e.open_source.preimage hf.continuous,
    translationFiberHomeomorph f R hR hf hRinv hRcont e he, fun _ => rfl⟩

include hR hzero hf hRinv hRcont in
theorem covering_of_translations
    (L : V → V ≃ₜ V) (hL : ∀ a x, f (L a x) = f a * f x)
    (hsurj : Function.Surjective f) : IsCoveringMap f := by
  intro g
  obtain ⟨a, rfl⟩ := hsurj g
  have hh := (evenlyCovered_one_of_translations f R hR hzero hf hRinv hRcont).homeomorph_comp
    (Homeomorph.mulLeft (f a))
  have hh' := hh.comp_homeomorph (L a).symm
  have heq : (Homeomorph.mulLeft (f a) ∘ f) ∘ (L a).symm = f := by
    funext x
    exact (hL a ((L a).symm x)).symm.trans (congrArg f ((L a).apply_symm_apply x))
  rw [heq] at hh'
  have hh'' : IsEvenlyCovered f (f a) (f ⁻¹' {1}) := by simpa using hh'
  exact hh''.to_isEvenlyCovered_preimage

/-- A covering of a simply connected space from a connected space has a
continuous global inverse. -/
def homeomorphOfSimplyConnectedCovering [PreconnectedSpace V]
    [SimplyConnectedSpace G] [LocallyPathConnectedSpace G]
    (cov : IsCoveringMap f) : V ≃ₜ G := by
  let hlift := cov.existsUnique_continuousMap_lifts (ContinuousMap.id G) (f 0) 0 rfl
  let q := Classical.choose hlift
  have hq0 := (Classical.choose_spec hlift).1.1
  have hq := (Classical.choose_spec hlift).1.2
  have hleft : q ∘ f = id := by
    apply cov.eq_of_comp_eq (q.continuous.comp cov.continuous) continuous_id
      (a := 0) (ha := hq0)
    funext x
    exact congrFun hq (f x)
  exact
    { toFun := f
      invFun := q
      left_inv := fun x => congrFun hleft x
      right_inv := fun y => congrFun hq y
      continuous_toFun := cov.continuous
      continuous_invFun := q.continuous }

end PolycyclicRecognition

end

end OAI
