import OAI.Analysis.CoulombTransport.LocalImplicit
import OAI.Analysis.CoulombTransport.StrictMinimum
import OAI.Analysis.CoulombTransport.HessianCoercivity

namespace OAI

universe uE

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Problem356.LocalGeometry

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A local exact supporting certificate, with the stationary branches retained
as analytic local diffeomorphisms and both domains shrunk to metric balls. -/
structure LocalSupportingCharts (F : E × (E × E) → ℝ)
    (G : E × (E × E) → E × E) (p : E) (s : E × E) where
  charts : LocalImplicit.AnalyticStationaryCharts G p s
  parameterRadius : ℝ
  parameterRadius_pos : 0 < parameterRadius
  source_ball : charts.central.source = Metric.ball p parameterRadius
  stateRadius : ℝ
  stateRadius_pos : 0 < stateRadius
  state_ball : charts.stateDomain = Metric.ball s stateRadius
  value : E → ℝ
  value_analytic : ContDiffOn ℝ ω value charts.central.source
  value_eq : ∀ y, value y = F (y, (charts.central y, charts.opposite y))
  value_base : value p = F (p, s)
  supporting : ∀ y ∈ charts.central.source, ∀ z ∈ charts.stateDomain,
    value y ≤ F (y, z)
  contact : ∀ y ∈ charts.central.source, ∀ z ∈ charts.stateDomain,
    F (y, z) = value y ↔ z = (charts.central y, charts.opposite y)

/-- Positive Hessian at the base point, together with separate local branch
invertibility, yields the full neighborhood-level supporting certificate. -/
theorem nonempty_localSupportingCharts [CompleteSpace E] [FiniteDimensional ℝ E]
    {F : E × (E × E) → ℝ} {G : E × (E × E) → E × E}
    {D : E → (E × E) → (E × E) →L[ℝ] ℝ}
    {H : E → (E × E) → (E × E) →L[ℝ] ((E × E) →L[ℝ] ℝ)}
    {p : E} {s : E × E}
    (C : LocalImplicit.AnalyticStationaryCharts G p s)
    (hF : ContDiffAt ℝ ω F (p, s))
    (hD : ∀ᶠ q in 𝓝 (p, s), HasFDerivAt (fun z => F (q.1, z)) (D q.1 q.2) q.2)
    (hH : ∀ᶠ q in 𝓝 (p, s), HasFDerivAt (D q.1) (H q.1 q.2) q.2)
    (hHcont : ContinuousAt (fun q : E × (E × E) => H q.1 q.2) (p, s))
    (hHpos : ∀ v : E × E, v ≠ 0 → 0 < H p s v v)
    (hcompatible : ∀ q : E × (E × E), G q = 0 → D q.1 q.2 = 0) :
    Nonempty (LocalSupportingCharts F G p s) := by
  let ψ : E → E × E := fun y => (C.central y, C.opposite y)
  have hψsmooth : ContDiffOn ℝ ω ψ C.central.source :=
    C.central_analytic.prodMk (C.source_eq ▸ C.opposite_analytic)
  have hψbase : ψ p = s := by simp [ψ, C.central_value, C.opposite_value]
  have hHnear := eventually_bilinear_pos (fun q : E × (E × E) => H q.1 q.2)
    (p, s) hHcont hHpos
  have hgood : ∀ᶠ q in 𝓝 (p, s), ContDiffAt ℝ ω F q ∧
      HasFDerivAt (fun z => F (q.1, z)) (D q.1 q.2) q.2 ∧
      HasFDerivAt (D q.1) (H q.1 q.2) q.2 ∧
      ∀ v : E × E, v ≠ 0 → 0 < H q.1 q.2 v v := by
    filter_upwards [hF.eventually (by simp), hD, hH, hHnear] with q h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hgood
  obtain ⟨r, hr, hrB⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hB (C.stateDomain_open.mem_nhds C.state_mem))
  have hψcont : ContinuousAt ψ p :=
    (hψsmooth.contDiffAt (C.central.open_source.mem_nhds C.point_mem)).continuousAt
  have hψball : ∀ᶠ y in 𝓝 p, ψ y ∈ Metric.ball s r := by
    apply hψcont.preimage_mem_nhds
    rw [hψbase]
    exact Metric.ball_mem_nhds s hr
  have hUgood : ∀ᶠ y in 𝓝 p,
      y ∈ C.central.source ∧ y ∈ A ∧ ψ y ∈ Metric.ball s r := by
    filter_upwards [C.central.open_source.mem_nhds C.point_mem, hA, hψball]
      with y h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨t, ht, htU⟩ := Metric.mem_nhds_iff.mp hUgood
  let U := Metric.ball p t
  have hUcentral : U ⊆ C.central.source := fun _ hy => (htU hy).1
  have hUopposite : U ⊆ C.opposite.source := C.source_eq ▸ hUcentral
  let X := C.central.restrOpen U Metric.isOpen_ball
  let Z := C.opposite.restrOpen U Metric.isOpen_ball
  have hXsource : X.source = U := inter_eq_right.mpr hUcentral
  have hZsource : Z.source = U := inter_eq_right.mpr hUopposite
  have hpair : (fun y => (X y, Z y)) = ψ := rfl
  have hproperties : ∀ y ∈ U, ∀ z ∈ Metric.ball s r,
      ContDiffAt ℝ ω F (y, z) ∧
      HasFDerivAt (fun z => F (y, z)) (D y z) z ∧
      HasFDerivAt (D y) (H y z) z ∧
      ∀ v : E × E, v ≠ 0 → 0 < H y z v v := by
    intro y hy z hz
    exact hAB ⟨(htU hy).2.1, (hrB hz).1⟩
  have hψU : ContDiffOn ℝ ω ψ U := hψsmooth.mono hUcentral
  have hψUmap : MapsTo ψ U (Metric.ball s r) := fun _ hy => (htU hy).2.2
  have hstatU : ∀ y ∈ U, D y (ψ y) = 0 := by
    intro y hy
    exact hcompatible (y, ψ y) (C.stationary y (hUcentral hy))
  have hcert := stationary_family_certificate_of_positive_hessian
    (fun q hq => (hproperties q.1 hq.1 q.2 hq.2).1.contDiffWithinAt)
    hψU hψUmap (convex_ball s r) Metric.isOpen_ball
    (fun y hy z hz => (hproperties y hy z hz).2.1)
    (fun y hy z hz => (hproperties y hy z hz).2.2.1)
    (fun y hy z hz => (hproperties y hy z hz).2.2.2) hstatU
  let C' : LocalImplicit.AnalyticStationaryCharts G p s := {
    central := X
    opposite := Z
    source_eq := hXsource.trans hZsource.symm
    point_mem := by rw [hXsource]; exact Metric.mem_ball_self ht
    central_value := C.central_value
    opposite_value := C.opposite_value
    stateDomain := Metric.ball s r
    stateDomain_open := Metric.isOpen_ball
    state_mem := Metric.mem_ball_self hr
    mapsTo_state := by rw [hpair, hXsource]; exact hψUmap
    stationary := fun y hy => C.stationary y hy.1
    unique_zero := fun y hy z hz => C.unique_zero y hy.1 z (hrB hz).2
    central_analytic := C.central_analytic.mono (fun _ hy => hy.1)
    central_inverse_analytic := C.central_inverse_analytic.mono (fun _ hy => hy.1)
    opposite_analytic := C.opposite_analytic.mono (fun _ hy => hy.1)
    opposite_inverse_analytic := C.opposite_inverse_analytic.mono (fun _ hy => hy.1) }
  refine ⟨{
    charts := C'
    parameterRadius := t
    parameterRadius_pos := ht
    source_ball := hXsource
    stateRadius := r
    stateRadius_pos := hr
    state_ball := rfl
    value := fun y => F (y, ψ y)
    value_analytic := ?_
    value_eq := fun _ => rfl
    value_base := by rw [hψbase]
    supporting := ?_
    contact := ?_ }⟩
  · change ContDiffOn ℝ ω (fun y => F (y, ψ y)) X.source
    rw [hXsource]
    exact hcert.1
  · intro y hy z hz
    exact (hcert.2 y (hXsource ▸ hy) z hz).1
  · intro y hy z hz
    exact (hcert.2 y (hXsource ▸ hy) z hz).2

/-- A local certificate survives arbitrary further neighborhood restrictions.
First shrink the state ball, and only then shrink the parameter ball so that
both branches still land in the new state ball. The functions and value are
unchanged, so previously established center values are preserved. -/
theorem LocalSupportingCharts.exists_shrink [CompleteSpace E]
    {F : E × (E × E) → ℝ} {G : E × (E × E) → E × E} {p : E} {s : E × E}
    (C : LocalSupportingCharts F G p s) (rp rs : ℝ) (hp : 0 < rp) (hs : 0 < rs) :
    ∃ D : LocalSupportingCharts F G p s,
      D.charts.central.source ⊆ C.charts.central.source ∩ Metric.ball p rp ∧
      D.charts.stateDomain ⊆ C.charts.stateDomain ∩ Metric.ball s rs ∧
      (D.charts.central : E → E) = C.charts.central ∧
      (D.charts.opposite : E → E) = C.charts.opposite ∧ D.value = C.value := by
  let r := min C.stateRadius rs
  have hr : 0 < r := lt_min C.stateRadius_pos hs
  have hball : Metric.ball s r ⊆ C.charts.stateDomain := by
    rw [C.state_ball]
    exact Metric.ball_subset_ball (min_le_left _ _)
  obtain ⟨d, hdstate, hdsource, hdX, hdZ⟩ := C.charts.exists_restrict_state
    (Metric.ball s r) Metric.isOpen_ball (Metric.mem_ball_self hr) hball
  have hU : d.central.source ∩ Metric.ball p rp ∈ 𝓝 p :=
    inter_mem (d.central.open_source.mem_nhds d.point_mem) (Metric.ball_mem_nhds p hp)
  obtain ⟨t, ht, e, hesource, heU, hestate, heX, heZ⟩ :=
    d.exists_restrict_ball (d.central.source ∩ Metric.ball p rp) hU
  have hsource : e.central.source ⊆ C.charts.central.source :=
    fun _ hy => hdsource (heU hy).1
  have hstate : e.stateDomain ⊆ C.charts.stateDomain := by
    rw [hestate, hdstate]
    exact hball
  have hsameX : (e.central : E → E) = C.charts.central := heX.trans hdX
  have hsameZ : (e.opposite : E → E) = C.charts.opposite := heZ.trans hdZ
  let D : LocalSupportingCharts F G p s := {
    charts := e
    parameterRadius := t
    parameterRadius_pos := ht
    source_ball := hesource
    stateRadius := r
    stateRadius_pos := hr
    state_ball := hestate.trans hdstate
    value := C.value
    value_analytic := C.value_analytic.mono hsource
    value_eq := by
      intro y
      rw [hsameX, hsameZ]
      exact C.value_eq y
    value_base := C.value_base
    supporting := fun y hy z hz => C.supporting y (hsource hy) z (hstate hz)
    contact := by
      intro y hy z hz
      rw [hsameX, hsameZ]
      exact C.contact y (hsource hy) z (hstate hz) }
  refine ⟨D, ?_, ?_, hsameX, hsameZ, rfl⟩
  · exact fun _ hy => ⟨hsource hy, (heU hy).2⟩
  · intro z hz
    refine ⟨hstate hz, ?_⟩
    change z ∈ e.stateDomain at hz
    rw [hestate, hdstate] at hz
    exact Metric.ball_subset_ball (min_le_right _ _) hz

end Problem356.LocalGeometry

end

end OAI
