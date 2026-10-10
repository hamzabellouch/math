import OAI.Probability.GammaPassage.GoodSiteProbability
import OAI.Probability.GammaPassage.GoodSitePaths

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Quantitative rare-fast bound in terms of an integer ceiling. -/
theorem gamma_rareFast_eventually (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (hA : 0 < A) (hR : 0 ≤ R) (hε : 0 < ε)
    (plus : Bool) (p0 : ℝ) (hp0 : 0 < p0) (hp1 : p0 ≤ 1) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ᶠ s : ℝ in atTop, ∀ n : ℤ,
      (⌈D0*s⌉ : ℝ)+s ≤ n →
      P.real {ω | (fun e => τ e ω) ∈
        rareFastEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm h hshape hrate) b plus) A R ε s n 0} < p0 := by
  let _ := h.probability
  let k : ℕ := ⌈4*(A+3)+8⌉₊+1
  obtain ⟨ζ,hζ,hpaths⟩ := high_density_oriented_paths_uniform k
  have htM := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1-p0)
    (by linarith : 1-p0 < 1)
  obtain ⟨M,hpow,hM⟩ := ((htM.eventually (gt_mem_nhds (by linarith : 0 < ζ/2))).and
    (eventually_ge_atTop (1 : ℕ))).exists
  have hM0 : 0 < M := by omega
  obtain ⟨D0,hD0,hbad⟩ := gamma_goodSiteEvent_failure h hshape hrate b A R ε hb plus M hM0 hR hε
  refine ⟨D0,hD0,?_⟩
  filter_upwards [hbad (ζ/2) (by linarith),eventually_ge_atTop (1 : ℝ)] with s hbs hs
  intro n hn
  have hd0 : (0 : ℝ) ≤ (⌈D0*s⌉ : ℤ) := by
    have := Int.le_ceil (D0*s)
    nlinarith
  have hd : 0 ≤ (⌈D0*s⌉ : ℤ) := by exact_mod_cast hd0
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  by_contra hlow
  have hl : p0 ≤ P.real {ω | (fun e => τ e ω) ∈
      rareFastEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm h hshape hrate) b plus) A R ε s n 0} := le_of_not_gt hlow
  have hg (v : Vertex) : P.real {ω | (fun e => τ e ω) ∉
      goodSiteEvent (gammaMeanNorm h hshape hrate) b A R ε s plus n ⌈D0*s⌉ M v} ≤ ζ := by
    have := hbs n v p0 hl
    linarith
  have hi := goodSiteEvent_independent h (gammaMeanNorm h hshape hrate) b A R ε s plus n ⌈D0*s⌉ M hM0 hA hd hR hs hn
  have hp := hpaths Ω P
    (fun v => {ω | (fun e => τ e ω) ∈ goodSiteEvent (gammaMeanNorm h hshape hrate) b A R ε s plus n ⌈D0*s⌉ M v})
    (fun v => (measurableSet_goodSiteEvent ..).preimage (Measurable.of_eval h.measurable)) hi hg
  have hz := gamma_goodSite_path_probability_zero h hshape hrate b A R ε s plus n ⌈D0*s⌉ M
    hb hR hε hs hn0 hd hM0
  unfold Measure.real at hp
  simp only [mem_ofPred_eq] at hp
  rw [hz] at hp
  simp at hp

/-- Exact two-parameter epsilon formulation: once s and n/s are large,
the probability of the manuscript's strict localized event is small. -/
theorem gamma_rareFast_bound (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (hA : 0 < A) (hR : 0 ≤ R) (hε : 0 < ε)
    (plus : Bool) (κ : ℝ) (hκ : 0 < κ) :
    ∃ S K : ℝ, 1 ≤ S ∧ 0 < K ∧ ∀ s : ℝ, S ≤ s → ∀ n : ℤ,
      K*s ≤ n → P.real {ω | (fun e => τ e ω) ∈
        rareFastEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm h hshape hrate) b plus) A R ε s n 0} < κ := by
  let p0 := min κ 1
  have hp0 : 0 < p0 := lt_min hκ (by norm_num)
  obtain ⟨D0,hD0,hh⟩ := gamma_rareFast_eventually h hshape hrate b A R ε hb hA hR hε plus p0 hp0
    (min_le_right _ _)
  obtain ⟨S,hS⟩ := eventually_atTop.mp hh
  refine ⟨max S 1,D0+2,le_max_right _ _,by linarith,?_⟩
  intro s hs n hn
  have hs1 : 1 ≤ s := (le_max_right _ _).trans hs
  have hc : (⌈D0*s⌉ : ℝ) < D0*s+1 := Int.ceil_lt_add_one _
  exact (hS s ((le_max_left _ _).trans hs) n (by nlinarith)).trans_le (min_le_left _ _)

/-- Rare-fast joint limit along arbitrary filters with `s → ∞` and
`n/s → ∞`, where `n` is integer-valued and eventually positive. -/
theorem gamma_rareFast_tendsto {ι : Type*} {l : Filter ι}
    (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (hA : 0 < A) (hR : 0 ≤ R) (hε : 0 < ε)
    (plus : Bool) (s : ι → ℝ) (n : ι → ℤ)
    (hs : Tendsto s l atTop) (hn : Tendsto (fun i => (n i : ℝ)/s i) l atTop) :
    Tendsto (fun i => P.real {ω | (fun e => τ e ω) ∈
      rareFastEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm h hshape hrate) b plus) A R ε (s i) (n i) 0}) l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun _ => ha.trans_le measureReal_nonneg)
  · intro κ hκ
    obtain ⟨S,K,hS,_,hh⟩ := gamma_rareFast_bound h hshape hrate b A R ε hb hA hR hε plus κ hκ
    filter_upwards [hs.eventually (eventually_ge_atTop S),hn.eventually (eventually_ge_atTop K)] with i hsi hni
    apply hh (s i) hsi (n i)
    exact (le_div_iff₀ (by linarith : 0 < s i)).mp hni

/-- Exact translations, even chosen differently at each scale, have the same
probability and therefore the same rare-fast limit. -/
theorem gamma_rareFast_translate_tendsto {ι : Type*} {l : Filter ι}
    (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (hA : 0 < A) (hR : 0 ≤ R) (hε : 0 < ε)
    (plus : Bool) (s : ι → ℝ) (n : ι → ℤ) (t : ι → Vertex)
    (hs : Tendsto s l atTop) (hn : Tendsto (fun i => (n i : ℝ)/s i) l atTop) :
    Tendsto (fun i => P.real {ω | (fun e => τ e ω) ∈
      rareFastEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm h hshape hrate) b plus) A R ε (s i) (n i) (t i)}) l (𝓝 0) := by
  have he (i : ι) := congrArg ENNReal.toReal (rareFastEvent_probability_translate h b ((gammaMeanNorm h hshape hrate) (direction b))
    (extremeSlope (gammaMeanNorm h hshape hrate) b plus) A R ε (s i) (n i) (t i))
  exact (gamma_rareFast_tendsto h hshape hrate b A R ε hb hA hR hε plus s n hs hn).congr
    (fun i => (he i).symm)

end GammaFPP.CrossingBridge

end OAI
