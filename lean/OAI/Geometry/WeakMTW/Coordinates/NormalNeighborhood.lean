import Mathlib
import OAI.Geometry.WeakMTW.Analysis.SmoothFlow
import OAI.Geometry.WeakMTW.Coordinates.NormalCoordinates

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff

namespace NormalNeighborhood
noncomputable section
section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_smooth_local_diffeomorph {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S : Set E} (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S)
    {a : E} (ha : a ∈ S) {D : E ≃L[ℝ] F}
    (hd : HasFDerivAt f (D : E →L[ℝ] F) a) :
    ∃ e : OpenPartialHomeomorph E F,
      (e : E → F) = f ∧ a ∈ e.source ∧ e.source ⊆ S ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ z ∈ e.source, ∃ L : E ≃L[ℝ] F, fderiv ℝ f z = (L : E →L[ℝ] F) := by
  let P := ((hf a ha).contDiffAt (hS.mem_nhds ha)).toOpenPartialHomeomorph f hd (by simp)
  have hPa : a ∈ P.source :=
    ((hf a ha).contDiffAt (hS.mem_nhds ha)).mem_toOpenPartialHomeomorph_source hd (by simp)
  let W := S ∩ (fderiv ℝ f) ⁻¹' range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F)
  have hW : IsOpen W :=
    (hf.continuousOn_fderiv_of_isOpen hS (by simp)).isOpen_inter_preimage hS
      ContinuousLinearEquiv.isOpen
  have haW : a ∈ W := ⟨ha, ⟨D, hd.fderiv.symm⟩⟩
  let e := P.restrOpen W hW
  have hcoeff : (e : E → F) = f := rfl
  refine ⟨e, hcoeff, ⟨hPa, haW⟩, fun _ hz => hz.2.1, ?_, ?_⟩
  · intro y hy
    have hz := e.map_target hy
    obtain ⟨D', hD'⟩ := hz.2.2
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm hy (f₀' := D')
    · rw [hcoeff, hD']
      exact (((hf _ hz.2.1).contDiffAt (hS.mem_nhds hz.2.1)).differentiableAt (by simp)).hasFDerivAt
    · rw [hcoeff]
      exact (hf _ hz.2.1).contDiffAt (hS.mem_nhds hz.2.1)
  · intro z hz
    obtain ⟨L, hL⟩ := hz.2.2
    exact ⟨L, hL.symm⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem isOpen_initial_segment {U : Set (ℝ × E)} (hU : IsOpen U) (T : ℝ) :
    IsOpen {q : E | ∀ t ∈ Icc (0 : ℝ) T, (t, q) ∈ U} := by
  rw [isOpen_iff_mem_nhds]
  intro q hq
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro t ht
  exact (continuous_swap.continuousAt (x := (q, t))).preimage_mem_nhds
    (hU.mem_nhds (hq t ht))

end General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry

structure NormalFlow (G : E → MetricTensor E) (S : Set E) (x₀ : E) where
  time : ℝ
  time_pos : 0 < time
  domain : Set (ℝ × (E × E))
  domain_open : IsOpen domain
  flow : ℝ × (E × E) → E × E
  flow_smooth : ContDiffOn ℝ ∞ flow domain
  initial : ∀ q, (0, q) ∈ domain → flow (0, q) = q
  ode : ∀ q ∈ domain, (flow q).1 ∈ S ∧
    HasDerivAt (fun t => flow (t, q.2)) (geodesicSpray G (flow q)) q.1
  normal : OpenPartialHomeomorph (E × E) (E × E)
  normal_apply : ∀ q, normal q = (q.1, (flow (time, q)).1)
  center_mem : (x₀, 0) ∈ normal.source
  source_stays : ∀ q ∈ normal.source, ∀ t ∈ Icc (0 : ℝ) time, (t, q) ∈ domain
  inverse_smooth : ContDiffOn ℝ ∞ normal.symm normal.target
  normal_derivative_invertible : ∀ q ∈ normal.source,
    ∃ L : (E × E) ≃L[ℝ] (E × E), fderiv ℝ normal q = (L : (E × E) →L[ℝ] (E × E))

theorem exists_normalFlow {G : E → MetricTensor E} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {x₀ : E} (hx₀ : x₀ ∈ S) : Nonempty (NormalFlow G S x₀) := by
  obtain ⟨U, Φ, hU, h0, hΦ, hzero, hode'⟩ := SmoothFlow.exists_smooth_local_flow
    (hS.prod isOpen_univ) (contDiffOn_geodesicSpray hS hG hpos)
    (x₀ := (x₀, (0 : E))) ⟨hx₀, mem_univ _⟩
  have hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2)) (geodesicSpray G (Φ q)) q.1 :=
    fun q hq => ⟨(hode' q hq).1.1, (hode' q hq).2⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  let T : ℝ := r / 2
  have hT : 0 < T := half_pos hr
  have hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, (x₀, 0)) ∈ U := by
    intro t ht
    apply hball
    simp only [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq, sub_zero,
      abs_of_nonneg ht.1, max_eq_left ht.1]
    exact lt_of_le_of_lt ht.2 (half_lt_self hr)
  let A : Set (E × E) := {q | ∀ t ∈ Icc (0 : ℝ) T, (t, q) ∈ U}
  have hA : IsOpen A := isOpen_initial_segment hU T
  have ha : (x₀, 0) ∈ A := hseg
  let N : E × E → E × E := fun q => (q.1, (Φ (T, q)).1)
  have hN : ContDiffOn ℝ ∞ N A :=
    contDiffOn_fst.prodMk ((hΦ.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun q (hq : q ∈ A) => hq T ⟨hT.le, le_rfl⟩)).fst)
  have hDN := NormalCoordinates.hasFDerivAt_normalMap_zero hS hG hpos hU hΦ
    hzero hode hx₀ hT hseg
  obtain ⟨e, he, hem, hesub, hesmooth, heinv⟩ :=
    exists_smooth_local_diffeomorph hA hN ha hDN
  exact ⟨{
    time := T
    time_pos := hT
    domain := U
    domain_open := hU
    flow := Φ
    flow_smooth := hΦ
    initial := hzero
    ode := hode
    normal := e
    normal_apply := fun q => congrFun he q
    center_mem := hem
    source_stays := fun q hq => hesub hq
    inverse_smooth := hesmooth
    normal_derivative_invertible := fun q hq => by simpa only [he] using heinv q hq
  }⟩

end
end NormalNeighborhood
end

end WeakMTWGlobalSupport

end OAI
