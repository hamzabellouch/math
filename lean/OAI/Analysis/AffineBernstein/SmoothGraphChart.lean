import Mathlib
import OAI.Analysis.AffineBernstein.Basic

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology

lemma exists_smooth_local_diffeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) {f : E → E}
    (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U) (hfx : f x ∈ V)
    (e : E ≃L[ℝ] E) (he : fderiv ℝ f x = e.toContinuousLinearMap) :
    ∃ φ : OpenPartialHomeomorph E E, x ∈ φ.source ∧ φ.source ⊆ U ∧
      φ.target ⊆ V ∧ (φ : E → E) = f ∧ ContDiffOn ℝ ∞ φ φ.source ∧
      ContDiffOn ℝ ∞ φ.symm φ.target := by
  have hfa := hf.contDiffAt (hU.mem_nhds hx)
  have hd : HasFDerivAt f e.toContinuousLinearMap x := by
    rw [← he]
    exact hfa.differentiableAt (by simp) |>.hasFDerivAt
  let φ₀ := hfa.toOpenPartialHomeomorph f hd (by simp)
  have hx₀ : x ∈ φ₀.source := hfa.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hn : ∀ᶠ y in nhds x, ∃ e' : E ≃L[ℝ] E, e'.toContinuousLinearMap = fderiv ℝ f y := by
    have hc : ContinuousAt (fderiv ℝ f) x := hfa.continuousAt_fderiv (by simp)
    exact hc.preimage_mem_nhds (by rw [he]; exact e.nhds)
  obtain ⟨N,hN,hNo,hxN⟩ := mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds hx) (inter_mem (hfa.continuousAt.preimage_mem_nhds (hV.mem_nhds hfx)) hn))
  let φ := φ₀.restrOpen N hNo
  have hφf : (φ : E → E) = f := rfl
  have hs : φ.source ⊆ U := fun y hy => (hN hy.2).1
  refine ⟨φ,⟨hx₀,hxN⟩,hs,?_,hφf,?_,?_⟩
  · intro y hy
    have hys := φ.map_target hy
    have hh := (hN hys.2).2.1
    change f (φ.symm y) ∈ V at hh
    simpa only [← hφf,φ.right_inv hy] using hh
  · simpa only [hφf] using hf.mono hs
  · intro y hy
    have hys := φ.map_target hy
    obtain ⟨e',he'⟩ := (hN hys.2).2.2
    have hg : ContDiffAt ℝ ∞ f (φ.symm y) := hf.contDiffAt (hU.mem_nhds (hs hys))
    apply (φ.contDiffAt_symm hy (f₀' := e') ?_ ?_).contDiffWithinAt
    · rw [hφf,he']
      exact hg.differentiableAt (by simp) |>.hasFDerivAt
    · simpa only [hφf] using hg

/- The graph projection of a smooth immersed parametrization of a graph
has nonsingular derivative. This is the differential input to the local
chart used in the support-coordinate stationarity calculation. -/
lemma graph_projection_derivative_bijective {n : ℕ} {U Ω : Set (Space n)}
    (hU : IsOpen U) (hΩ : IsOpen Ω) {X : Space n → Space n × ℝ}
    {u : Space n → ℝ} (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
    (him : ∀ y ∈ U, (X y).1 ∈ Ω ∧ (X y).2 = u (X y).1)
    {x : Space n} (hx : x ∈ U) (hi : Function.Injective (fderiv ℝ X x)) :
    Function.Bijective (fderiv ℝ (fun y => (X y).1) x) := by
  have hXa := hX.contDiffAt (hU.mem_nhds hx)
  have hd := hXa.differentiableAt (by simp)
  have he : X =ᶠ[nhds x] (fun y => ((X y).1,u (X y).1)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact Prod.ext rfl (him y hy).2
  have hu' := (hu.contDiffAt (hΩ.mem_nhds (him x hx).1)).differentiableAt (by simp)
  have heD := he.fderiv_eq (𝕜 := ℝ)
  have hg : fderiv ℝ X x =
      (fderiv ℝ (fun y => (X y).1) x).prod
        ((fderiv ℝ u (X x).1).comp (fderiv ℝ (fun y => (X y).1) x)) := by
    rw [heD]
    exact ((hd.fst.hasFDerivAt).prodMk (hu'.hasFDerivAt.comp x hd.fst.hasFDerivAt)).fderiv
  have hinj : Function.Injective (fderiv ℝ (fun y => (X y).1) x) := by
    intro v w hvw
    apply hi
    rw [hg]
    simp only [ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply,hvw]
  exact ⟨hinj,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩

theorem exists_smooth_graph_chart {n : ℕ} {U Ω : Set (Space n)}
    (hU : IsOpen U) (hΩ : IsOpen Ω) {X : Space n → Space n × ℝ}
    {u : Space n → ℝ} (hX : ContDiffOn ℝ ∞ X U) (hu : ContDiffOn ℝ ∞ u Ω)
    (him : ∀ y ∈ U, (X y).1 ∈ Ω ∧ (X y).2 = u (X y).1)
    {x : Space n} (hx : x ∈ U) (hi : Function.Injective (fderiv ℝ X x)) :
    ∃ φ : OpenPartialHomeomorph (Space n) (Space n), x ∈ φ.source ∧ φ.source ⊆ U ∧
      φ.target ⊆ Ω ∧ (∀ y ∈ φ.source, X y = (φ y,u (φ y))) ∧
      ContDiffOn ℝ ∞ φ φ.source ∧ ContDiffOn ℝ ∞ φ.symm φ.target := by
  have hb := graph_projection_derivative_bijective hU hΩ hX hu him hx hi
  let e := (LinearEquiv.ofBijective (fderiv ℝ (fun y => (X y).1) x).toLinearMap hb).toContinuousLinearEquiv
  obtain ⟨φ,hxφ,hs,ht,he,hφ,hψ⟩ := exists_smooth_local_diffeomorph hU hΩ hX.fst hx (him x hx).1 e rfl
  refine ⟨φ,hxφ,hs,ht,?_,hφ,hψ⟩
  intro y hy
  rw [he]
  exact Prod.ext rfl (him y (hs hy)).2

end AffineBernstein
end

end OAI
