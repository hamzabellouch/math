import Mathlib
import OAI.Analysis.AffineBernstein.SmoothGraphChart

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

/- A one-to-one smooth local diffeomorphism on an open set gives a single
global smooth partial chart. -/
lemma exists_smooth_global_diffeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f : E → E} (hf : ContDiffOn ℝ ∞ f U) (him : MapsTo f U V)
    (hi : Set.InjOn f U) (hd : ∀ x ∈ U, Function.Bijective (fderiv ℝ f x)) :
    ∃ φ : OpenPartialHomeomorph E E, φ.source = U ∧ φ.target = f '' U ∧
      φ.target ⊆ V ∧ (φ : E → E) = f ∧ ContDiffOn ℝ ∞ φ φ.source ∧
      ContDiffOn ℝ ∞ φ.symm φ.target := by
  have hlocal (x : E) (hx : x ∈ U) :
      ∃ ψ : OpenPartialHomeomorph E E, x ∈ ψ.source ∧ ψ.source ⊆ U ∧
        ψ.target ⊆ V ∧ (ψ : E → E) = f ∧ ContDiffOn ℝ ∞ ψ ψ.source ∧
        ContDiffOn ℝ ∞ ψ.symm ψ.target := by
    let e := (LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap (hd x hx)).toContinuousLinearEquiv
    exact exists_smooth_local_diffeomorph hU hV hf hx (him hx) e rfl
  have ho : IsOpenMap (U.domRestrict f) := by
    intro W hW
    have hW' : IsOpen (Subtype.val '' W : Set E) := hU.isOpenMap_subtype_val _ hW
    apply isOpen_iff_mem_nhds.mpr
    rintro z ⟨x,hx,rfl⟩
    obtain ⟨ψ,hxψ,hs,ht,he,hψ,hψi⟩ := hlocal x x.property
    have hN : IsOpen (ψ '' ((Subtype.val '' W : Set E) ∩ ψ.source)) :=
      ψ.isOpen_image_of_subset_source (hW'.inter ψ.open_source) inter_subset_right
    have hxN : f x ∈ ψ '' ((Subtype.val '' W : Set E) ∩ ψ.source) :=
      ⟨x,⟨⟨x,hx,rfl⟩,hxψ⟩,by rw [he]⟩
    apply mem_of_superset (hN.mem_nhds hxN)
    rintro z ⟨y,⟨⟨x',hx',rfl⟩,hy⟩,rfl⟩
    exact ⟨x',hx',by rw [he]; rfl⟩
  let pe := hi.toPartialEquiv f U
  let φ := OpenPartialHomeomorph.ofContinuousOpenRestrict pe hf.continuousOn ho hU
  have hs : φ.source = U := rfl
  have ht : φ.target = f '' U := rfl
  have he : (φ : E → E) = f := rfl
  refine ⟨φ,hs,ht,?_,he,?_,?_⟩
  · rintro y ⟨x,hx,rfl⟩
    exact him hx
  · exact hf
  · intro y hy
    have hx : φ.symm y ∈ U := φ.map_target hy
    have hfa : ContDiffAt ℝ ∞ f (φ.symm y) := hf.contDiffAt (hU.mem_nhds hx)
    let e := (LinearEquiv.ofBijective (fderiv ℝ f (φ.symm y)).toLinearMap
      (hd _ hx)).toContinuousLinearEquiv
    apply (φ.contDiffAt_symm hy (f₀' := e) ?_ ?_).contDiffWithinAt
    · exact hfa.differentiableAt (by simp) |>.hasFDerivAt
    · exact hfa

/- A globally injective immersion into an actual graph admits a global
smooth graph chart on its entire open parameter domain. -/
theorem exists_smooth_global_graph_chart {n : ℕ} {U Ω : Set (Space n)}
    (hU : IsOpen U) (hΩ : IsOpen Ω) {X : Space n → Space n × ℝ}
    {u : Space n → ℝ} (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
    (him : ∀ y ∈ U, (X y).1 ∈ Ω ∧ (X y).2 = u (X y).1)
    (hi : Set.InjOn (fun x => (X x).1) U)
    (hd : ∀ x ∈ U, Function.Injective (fderiv ℝ X x)) :
    ∃ φ : OpenPartialHomeomorph (Space n) (Space n), φ.source = U ∧
      φ.target ⊆ Ω ∧ (∀ y ∈ U, X y = (φ y,u (φ y))) ∧
      ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target := by
  obtain ⟨φ,hs,ht,hΩφ,he,hφ,hψ⟩ := exists_smooth_global_diffeomorph hU hΩ hX.fst
    (fun x hx => (him x hx).1) hi
    (fun x hx => graph_projection_derivative_bijective hU hΩ hX hu him hx (hd x hx))
  refine ⟨φ,hs,hΩφ,?_,hφ,hψ⟩
  intro y hy
  rw [he]
  exact Prod.ext rfl (him y hy).2

end AffineBernstein
end

end OAI
