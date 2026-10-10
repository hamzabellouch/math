import Mathlib

namespace OAI

universe uP uS

noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace Problem356.LocalImplicit

variable {P : Type uP} {S : Type uS}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

/-- Analytic implicit-function theorem, packaged on open product neighborhoods.
The equation is normalized to zero, as for a stationary-point equation. -/
theorem exists_analytic_implicit_branch
    (G : P × S → S) (p : P) (s : S)
    (hG : ContDiffAt ℝ ω G (p, s))
    (hzero : G (p, s) = 0)
    (hinv : (fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ P S).IsInvertible) :
    ∃ (ψ : P → S) (U : Set P) (V : Set S),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ s ∈ V ∧
      ContDiffOn ℝ ω ψ U ∧ MapsTo ψ U V ∧ ψ p = s ∧
      (∀ y ∈ U, G (y, ψ y) = 0) ∧
      (∀ y ∈ U, ∀ z ∈ V, G (y, z) = 0 ↔ ψ y = z) ∧
      HasStrictFDerivAt ψ
        (-(fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ P S).inverse ∘L
          (fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inl ℝ P S)) p := by
  let ψ : P → S := hG.implicitFunction (by simp) hinv
  have hψ : ContDiffAt ℝ ω ψ p := hG.contDiffAt_implicitFunction (by simp) hinv
  have hψp : ψ p = s := hG.implicitFunction_apply_self (by simp) hinv
  have heq : ∀ᶠ q in 𝓝 (p, s), G q = 0 ↔ ψ q.1 = q.2 := by
    simpa only [hzero] using hG.eventually_apply_eq_iff_implicitFunction (by simp) hinv
  obtain ⟨U₀, hU₀, V₀, hV₀, hprod⟩ := mem_nhds_prod_iff.mp heq
  obtain ⟨V, hVV₀, hVopen, hsV⟩ := mem_nhds_iff.mp hV₀
  have hmaps : ψ ⁻¹' V ∈ 𝓝 p := hψ.continuousAt.preimage_mem_nhds (by
    rw [hψp]
    exact hVopen.mem_nhds hsV)
  have hcont : ∀ᶠ y in 𝓝 p, ContDiffAt ℝ ω ψ y := hψ.eventually (by simp)
  have heqn : ∀ᶠ y in 𝓝 p, G (y, ψ y) = 0 := by
    simpa only [hzero] using hG.eventually_apply_implicitFunction (by simp) hinv
  obtain ⟨U, hUsub, hUopen, hpU⟩ :=
    mem_nhds_iff.mp (inter_mem hU₀ (inter_mem hmaps (hcont.and heqn)))
  refine ⟨ψ, U, V, hUopen, hpU, hVopen, hsV, ?_, ?_, hψp, ?_, ?_, ?_⟩
  · exact hUopen.contDiffOn_iff.mpr (fun _ hy => (hUsub hy).2.2.1)
  · exact fun y hy => (hUsub hy).2.1
  · exact fun y hy => (hUsub hy).2.2.2
  · intro y hy z hz
    exact hprod ⟨(hUsub hy).1, hVV₀ hz⟩
  · exact hG.hasStrictFDerivAt_implicitFunction (by simp) hinv

omit [CompleteSpace S] in
/-- A map analytic at one point with invertible derivative is analytic in both
 directions on a suitable open partial homeomorphism. -/
theorem exists_analytic_local_diffeomorph
    (f : P → S) (p : P)
    (hf : ContDiffAt ℝ ω f p)
    (hinv : (fderiv ℝ f p).IsInvertible) :
    ∃ e : OpenPartialHomeomorph P S,
      (e : P → S) = f ∧ p ∈ e.source ∧
      ContDiffOn ℝ ω e e.source ∧ ContDiffOn ℝ ω e.symm e.target := by
  obtain ⟨A, hA⟩ := hinv
  have hderiv : HasFDerivAt f (A : P →L[ℝ] S) p := by
    rw [hA]
    exact (hf.differentiableAt (by simp)).hasFDerivAt
  let e₀ := hf.toOpenPartialHomeomorph f hderiv (by simp)
  have he₀ : (e₀ : P → S) = f := rfl
  have hp₀ : p ∈ e₀.source := hf.mem_toOpenPartialHomeomorph_source hderiv (by simp)
  have hfp₀ : f p ∈ e₀.target := hf.image_mem_toOpenPartialHomeomorph_target hderiv (by simp)
  have hinverse : ContDiffAt ℝ ω e₀.symm (f p) := by
    have hleft : e₀.symm (f p) = p := e₀.left_inv hp₀
    apply e₀.contDiffAt_symm hfp₀
    · simpa only [hleft, he₀] using hderiv
    · simpa only [hleft, he₀] using hf
  obtain ⟨V, hVsub, hVopen, hfpV⟩ :=
    mem_nhds_iff.mp (hinverse.eventually (by simp))
  have hpre : f ⁻¹' V ∈ 𝓝 p := hf.continuousAt.preimage_mem_nhds (hVopen.mem_nhds hfpV)
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp
    (inter_mem (e₀.open_source.mem_nhds hp₀) (inter_mem (hf.eventually (by simp)) hpre))
  refine ⟨e₀.restrOpen U hUopen, rfl, ⟨hp₀, hpU⟩, ?_, ?_⟩
  · apply (e₀.restrOpen U hUopen).open_source.contDiffOn_iff.mpr
    intro x hx
    exact (hUsub hx.2).2.1
  · apply (e₀.restrOpen U hUopen).open_target.contDiffOn_iff.mpr
    intro y hy
    have hx := (e₀.restrOpen U hUopen).map_target hy
    have hxy := (e₀.restrOpen U hUopen).right_inv hy
    apply hVsub
    have hmem := (hUsub hx.2).2.2
    change f ((e₀.restrOpen U hUopen).symm y) ∈ V at hmem
    change f ((e₀.restrOpen U hUopen).symm y) = y at hxy
    exact hxy ▸ hmem

omit [CompleteSpace S] in
/-- The two projections of a local branch can be made analytic diffeomorphisms
on one common source neighborhood, contained in any prescribed neighborhood. -/
theorem exists_two_analytic_local_charts
    (ψ : P → S × S) (p : P) (U : Set P) (hU : U ∈ 𝓝 p)
    (hψ : ContDiffAt ℝ ω ψ p)
    (hinv₁ : (fderiv ℝ (fun y => (ψ y).1) p).IsInvertible)
    (hinv₂ : (fderiv ℝ (fun y => (ψ y).2) p).IsInvertible) :
    ∃ e₁ e₂ : OpenPartialHomeomorph P S,
      (e₁ : P → S) = (fun y => (ψ y).1) ∧
      (e₂ : P → S) = (fun y => (ψ y).2) ∧
      p ∈ e₁.source ∧ e₁.source = e₂.source ∧ e₁.source ⊆ U ∧
      ContDiffOn ℝ ω e₁ e₁.source ∧ ContDiffOn ℝ ω e₁.symm e₁.target ∧
      ContDiffOn ℝ ω e₂ e₂.source ∧ ContDiffOn ℝ ω e₂.symm e₂.target := by
  obtain ⟨e₁, he₁, hp₁, hc₁, hi₁⟩ :=
    exists_analytic_local_diffeomorph (fun y => (ψ y).1) p hψ.fst hinv₁
  obtain ⟨e₂, he₂, hp₂, hc₂, hi₂⟩ :=
    exists_analytic_local_diffeomorph (fun y => (ψ y).2) p hψ.snd hinv₂
  obtain ⟨O, hOU, hOopen, hpO⟩ := mem_nhds_iff.mp hU
  let W := e₁.source ∩ (e₂.source ∩ O)
  have hWopen : IsOpen W := e₁.open_source.inter (e₂.open_source.inter hOopen)
  have hW₁ : W ⊆ e₁.source := fun _ h => h.1
  have hW₂ : W ⊆ e₂.source := fun _ h => h.2.1
  have hs₁ : (e₁.restrOpen W hWopen).source = W := inter_eq_right.mpr hW₁
  have hs₂ : (e₂.restrOpen W hWopen).source = W := inter_eq_right.mpr hW₂
  refine ⟨e₁.restrOpen W hWopen, e₂.restrOpen W hWopen, he₁, he₂, ?_,
    hs₁.trans hs₂.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs₁]
    exact ⟨hp₁, hp₂, hpO⟩
  · rw [hs₁]
    exact fun _ h => hOU h.2.2
  · exact hc₁.mono (fun _ h => h.1)
  · exact hi₁.mono (fun _ h => h.1)
  · exact hc₂.mono (fun _ h => h.1)
  · exact hi₂.mono (fun _ h => h.1)

/-- The derivative supplied by the implicit-function theorem, with parameter first. -/
def implicitDerivative (G : P × (S × S) → S × S) (p : P) (s : S × S) :
    P →L[ℝ] S × S :=
  -(fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ P (S × S)).inverse ∘L
    (fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inl ℝ P (S × S))

/-- Two separately invertible coordinates of one local stationary branch. -/
structure AnalyticStationaryCharts (G : P × (S × S) → S × S) (p : P) (s : S × S) where
  central : OpenPartialHomeomorph P S
  opposite : OpenPartialHomeomorph P S
  source_eq : central.source = opposite.source
  point_mem : p ∈ central.source
  central_value : central p = s.1
  opposite_value : opposite p = s.2
  stateDomain : Set (S × S)
  stateDomain_open : IsOpen stateDomain
  state_mem : s ∈ stateDomain
  mapsTo_state : MapsTo (fun y => (central y, opposite y)) central.source stateDomain
  stationary : ∀ y ∈ central.source, G (y, (central y, opposite y)) = 0
  unique_zero : ∀ y ∈ central.source, ∀ z ∈ stateDomain,
    G (y, z) = 0 ↔ (central y, opposite y) = z
  central_analytic : ContDiffOn ℝ ω central central.source
  central_inverse_analytic : ContDiffOn ℝ ω central.symm central.target
  opposite_analytic : ContDiffOn ℝ ω opposite opposite.source
  opposite_inverse_analytic : ContDiffOn ℝ ω opposite.symm opposite.target

/-- Local stationarity plus the three invertibility checks produces two genuine
analytic charts on a common open source. -/
theorem nonempty_analyticStationaryCharts
    (G : P × (S × S) → S × S) (p : P) (s : S × S)
    (hG : ContDiffAt ℝ ω G (p, s)) (hzero : G (p, s) = 0)
    (hinv : (fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ P (S × S)).IsInvertible)
    (hcentral : (ContinuousLinearMap.fst ℝ S S ∘L implicitDerivative G p s).IsInvertible)
    (hopposite : (ContinuousLinearMap.snd ℝ S S ∘L implicitDerivative G p s).IsInvertible) :
    Nonempty (AnalyticStationaryCharts G p s) := by
  obtain ⟨ψ, U, V, hUopen, hpU, hVopen, hsV, hψU, hψV, hψp, heqn, huniq, hd⟩ :=
    exists_analytic_implicit_branch G p s hG hzero hinv
  have hψ : ContDiffAt ℝ ω ψ p := hUopen.contDiffOn_iff.mp hψU hpU
  have hd₁ : HasFDerivAt (fun y => (ψ y).1)
      (ContinuousLinearMap.fst ℝ S S ∘L implicitDerivative G p s) p :=
    hd.hasFDerivAt.fst
  have hd₂ : HasFDerivAt (fun y => (ψ y).2)
      (ContinuousLinearMap.snd ℝ S S ∘L implicitDerivative G p s) p :=
    hd.hasFDerivAt.snd
  obtain ⟨e₁, e₂, he₁, he₂, hp, hsource, hsub, hc₁, hi₁, hc₂, hi₂⟩ :=
    exists_two_analytic_local_charts ψ p U (hUopen.mem_nhds hpU) hψ
      (by rw [hd₁.fderiv]; exact hcentral) (by rw [hd₂.fderiv]; exact hopposite)
  refine ⟨{
    central := e₁
    opposite := e₂
    source_eq := hsource
    point_mem := hp
    central_value := ?_
    opposite_value := ?_
    stateDomain := V
    stateDomain_open := hVopen
    state_mem := hsV
    mapsTo_state := ?_
    stationary := ?_
    unique_zero := ?_
    central_analytic := hc₁
    central_inverse_analytic := hi₁
    opposite_analytic := hc₂
    opposite_inverse_analytic := hi₂ }⟩
  · simp only [he₁, hψp]
  · simp only [he₂, hψp]
  · intro y hy
    simpa only [he₁, he₂, Prod.eta] using hψV (hsub hy)
  · intro y hy
    simpa only [he₁, he₂, Prod.eta] using heqn y (hsub hy)
  · intro y hy z hz
    simpa only [he₁, he₂, Prod.eta] using huniq y (hsub hy) z hz

namespace AnalyticStationaryCharts

variable {G : P × (S × S) → S × S} {p : P} {s : S × S}

omit [CompleteSpace P] [CompleteSpace S]

/-- Restrict both parameter charts to the same additional open neighborhood. -/
def restrictSource (c : AnalyticStationaryCharts G p s)
    (U : Set P) (hU : IsOpen U) (hp : p ∈ U) : AnalyticStationaryCharts G p s where
  central := c.central.restrOpen U hU
  opposite := c.opposite.restrOpen U hU
  source_eq := by
    change c.central.source ∩ U = c.opposite.source ∩ U
    rw [c.source_eq]
  point_mem := ⟨c.point_mem, hp⟩
  central_value := c.central_value
  opposite_value := c.opposite_value
  stateDomain := c.stateDomain
  stateDomain_open := c.stateDomain_open
  state_mem := c.state_mem
  mapsTo_state := fun _ hy => c.mapsTo_state hy.1
  stationary := fun y hy => c.stationary y hy.1
  unique_zero := fun y hy z hz => c.unique_zero y hy.1 z hz
  central_analytic := c.central_analytic.mono (fun _ h => h.1)
  central_inverse_analytic := c.central_inverse_analytic.mono (fun _ h => h.1)
  opposite_analytic := c.opposite_analytic.mono (fun _ h => h.1)
  opposite_inverse_analytic := c.opposite_inverse_analytic.mono (fun _ h => h.1)

@[simp] theorem restrictSource_central_coe
    (c : AnalyticStationaryCharts G p s) (U : Set P) (hU : IsOpen U) (hp : p ∈ U) :
    ((c.restrictSource U hU hp).central : P → S) = c.central := rfl

@[simp] theorem restrictSource_opposite_coe
    (c : AnalyticStationaryCharts G p s) (U : Set P) (hU : IsOpen U) (hp : p ∈ U) :
    ((c.restrictSource U hU hp).opposite : P → S) = c.opposite := rfl

@[simp] theorem restrictSource_source
    (c : AnalyticStationaryCharts G p s) (U : Set P) (hU : IsOpen U) (hp : p ∈ U) :
    (c.restrictSource U hU hp).central.source = c.central.source ∩ U := rfl

/-- Any smaller open state neighborhood can be used after shrinking the common
parameter domain. All chart functions and all uniqueness conclusions are preserved. -/
theorem exists_restrict_state
    (c : AnalyticStationaryCharts G p s) (W : Set (S × S))
    (hW : IsOpen W) (hsW : s ∈ W) (hWV : W ⊆ c.stateDomain) :
    ∃ d : AnalyticStationaryCharts G p s,
      d.stateDomain = W ∧ d.central.source ⊆ c.central.source ∧
      (d.central : P → S) = c.central ∧ (d.opposite : P → S) = c.opposite := by
  have hp₂ : p ∈ c.opposite.source := c.source_eq ▸ c.point_mem
  have hc₁ : ContinuousAt c.central p :=
    c.central.continuousOn.continuousAt (c.central.open_source.mem_nhds c.point_mem)
  have hc₂ : ContinuousAt c.opposite p :=
    c.opposite.continuousOn.continuousAt (c.opposite.open_source.mem_nhds hp₂)
  have hval : (c.central p, c.opposite p) = s :=
    Prod.ext c.central_value c.opposite_value
  have hpre : (fun y => (c.central y, c.opposite y)) ⁻¹' W ∈ 𝓝 p :=
    (hc₁.prodMk hc₂).preimage_mem_nhds (by rw [hval]; exact hW.mem_nhds hsW)
  obtain ⟨U, hUsub, hUopen, hpU⟩ := mem_nhds_iff.mp hpre
  let c₀ := c.restrictSource U hUopen hpU
  let d : AnalyticStationaryCharts G p s := {
    c₀ with
      stateDomain := W
      stateDomain_open := hW
      state_mem := hsW
      mapsTo_state := fun _ hy => hUsub hy.2
      unique_zero := fun y hy z hz => c.unique_zero y hy.1 z (hWV hz) }
  exact ⟨d, rfl, (fun _ hy => hy.1), rfl, rfl⟩

/-- The common source can be chosen to be a genuine positive-radius ball,
inside any prescribed parameter neighborhood, without changing either chart function. -/
theorem exists_restrict_ball
    (c : AnalyticStationaryCharts G p s) (U : Set P) (hU : U ∈ 𝓝 p) :
    ∃ r : ℝ, 0 < r ∧ ∃ d : AnalyticStationaryCharts G p s,
      d.central.source = Metric.ball p r ∧ d.central.source ⊆ U ∧
      d.stateDomain = c.stateDomain ∧
      (d.central : P → S) = c.central ∧ (d.opposite : P → S) = c.opposite := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (c.central.open_source.mem_nhds c.point_mem) hU)
  let d := c.restrictSource (Metric.ball p r) Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hsource : d.central.source = Metric.ball p r :=
    inter_eq_right.mpr (fun _ hx => (hball hx).1)
  refine ⟨r, hr, d, hsource, ?_, rfl, rfl, rfl⟩
  rw [hsource]
  exact fun _ hx => (hball hx).2

end AnalyticStationaryCharts

end Problem356.LocalImplicit

end

end OAI
