import OAI.Probability.SLE.Gauge.PassageSuccess
import Mathlib.Topology.TietzeExtension

namespace OAI

/-! Measurable actual front passages. Local ribbon coordinates are extended
from their closed patch only to construct an adapted stopping time; on every
successful passage this stopping time is exactly the original first front. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.FrontSuccessMeasurability
open FirstFrontPassage PassageSuccess

local instance frontSuccessPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance frontSuccessPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

/-- Freeze a continuous path outside a finite time interval. -/
def clampedPath (f : C(ℝ≥0, ℂ)) (s t : ℝ≥0) : C(ℝ≥0, ℂ) :=
  f.comp ⟨fun u => max s (min u t), continuous_const.max (continuous_id.min continuous_const)⟩

theorem measurable_clampedPath
    {Ω : Type*} [MeasurableSpace Ω] (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f)
    (s t : Ω → ℝ≥0) (hs : Measurable s) (ht : Measurable t) :
    Measurable (fun ω => clampedPath (f ω) (s ω) (t ω)) := by
  apply source_path_measurable
  intro u
  exact continuous_eval.measurable.comp
    (hf.prodMk (hs.max (measurable_const.min ht)))

theorem sourceSausageSet_eq_clamped
    (f : C(ℝ≥0, ℂ)) (s t : ℝ≥0) (hst : s ≤ t) (v : ℝ) :
    sourceSausageSet f s t v = wholeSausageSet (clampedPath f s t) v := by
  ext z
  constructor
  · rintro ⟨u, hu, hv⟩
    refine ⟨u, ?_⟩
    simpa only [clampedPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      min_eq_left hu.2, max_eq_right hu.1, dist_comm] using hv
  · rintro ⟨u, hv⟩
    exact ⟨max s (min u t), ⟨le_max_left _ _, max_le hst (min_le_right _ _)⟩,
      by simpa only [clampedPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk, dist_comm] using hv⟩

/-- Variable finite endpoints cause no measurability loss in the physical
sausage charge. No stopping-time assumption on these endpoints is needed. -/
theorem segmentSausageCharge_measurable
    {Ω : Type*} [MeasurableSpace Ω] (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f)
    (s t : Ω → ℝ≥0) (hs : Measurable s) (ht : Measurable t)
    (κ v : ℝ) (R : Set ℂ) :
    Measurable (fun ω => segmentSausageCharge κ (f ω) (s ω) (t ω) v R) := by
  have hm := (wholeSausageCharge_measurable κ v R).comp (measurable_clampedPath f hf s t hs ht)
  have he (ω : Ω) : segmentSausageCharge κ (f ω) (s ω) (t ω) v R =
      if s ω ≤ t ω then wholeSausageCharge κ (clampedPath (f ω) (s ω) (t ω)) v R else 0 := by
    split_ifs with hst
    · simp only [segmentSausageCharge, wholeSausageCharge, sourceSausageSet_eq_clamped _ _ _ hst]
    · have hempty : sourceSausageSet (f ω) (s ω) (t ω) v = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro z ⟨u, hu, _⟩
        exact hst (hu.1.trans hu.2)
      simp only [segmentSausageCharge, hempty, inter_empty, measure_empty, mul_zero]
  simp_rw [he]
  exact Measurable.ite (measurableSet_le hs ht) hm measurable_const

/-- An open target and a measurable finite endpoint give a measurable
whole-prefix containment event. -/
theorem measurableSet_prefix_mapsTo
    {Ω : Type*} [MeasurableSpace Ω] (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f)
    (t : Ω → ℝ≥0) (ht : Measurable t) (V : Set ℂ) (hV : IsOpen V) :
    MeasurableSet {ω | MapsTo (f ω) (Icc 0 (t ω)) V} := by
  let g := fun ω => clampedPath (f ω) 0 (t ω)
  have hgm : Measurable g := measurable_clampedPath f hf (fun _ => 0) t measurable_const ht
  have he : {ω | MapsTo (f ω) (Icc 0 (t ω)) V} =
      ⋂ n : ℕ, {ω | MapsTo (g ω) (Icc 0 (n : ℝ≥0)) V} := by
    ext ω
    constructor
    · intro h
      apply mem_iInter.mpr
      intro n u hu
      exact h ⟨bot_le, by simp only [ContinuousMap.coe_mk, zero_le, max_eq_right, min_le_right]⟩
    · intro h u hu
      obtain ⟨n, hn⟩ := exists_nat_ge (u : ℝ)
      have hnn : u ≤ (n : ℝ≥0) := by exact_mod_cast hn
      have hh := (mem_iInter.mp h n) ⟨bot_le, hnn⟩
      simpa only [g, clampedPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        min_eq_left hu.2, max_eq_right (show (0 : ℝ≥0) ≤ u from bot_le)] using hh
  rw [he]
  exact MeasurableSet.iInter fun n =>
    (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc hV).measurableSet.preimage hgm

/-- Agreement through an attained first hit identifies the first hitting
time, regardless of how the two coordinates are defined later. -/
theorem firstFrontTime_eq_of_prefix
    (x y : ℝ≥0 → ℝ) (q : ℝ) (τ : ℝ≥0)
    (hx : firstFrontTime x q = (τ : WithTop ℝ≥0)) (hattain : x τ = q)
    (hxy : EqOn x y (Icc 0 τ)) :
    firstFrontTime y q = (τ : WithTop ℝ≥0) := by
  have hleast : IsLeast {t : ℝ≥0 | 0 ≤ t ∧ y t - q ∈ ({0} : Set ℝ)} τ := by
    refine ⟨⟨bot_le, ?_⟩, ?_⟩
    · rw [← hxy ⟨bot_le, le_rfl⟩, hattain, sub_self]
      exact mem_singleton 0
    · intro t ht
      by_contra hbad
      have hlt : t < τ := lt_of_not_ge hbad
      have hy : y t = q := sub_eq_zero.mp ht.2
      have hxhit : x t - q ∈ ({0} : Set ℝ) := by
        rw [hxy ⟨bot_le, hlt.le⟩, hy, sub_self]
        exact mem_singleton 0
      have hh := hittingAfter_le_of_mem (u := fun t (_ : Unit) => x t - q)
        (ω := ()) (show (0 : ℝ≥0) ≤ t from bot_le) hxhit
      change firstFrontTime x q ≤ (t : WithTop ℝ≥0) at hh
      rw [hx, WithTop.coe_le_coe] at hh
      exact (not_le_of_gt hlt) hh
  unfold firstFrontTime hittingAfter
  rw [ite_eq_left ⟨τ, hleast.1⟩, hleast.csInf_eq]

/-- The concrete success event depends only on the coordinate inside its
allowed region; the attained front equation makes this exact. -/
theorem frontSuccess_eq_of_eqOn
    {Ω : Type*} (η : ℕ → Ω → ℝ≥0 → ℂ) (p p' : ℕ → ℂ → ℝ)
    (σ : Ω → ℝ≥0) (V : ℕ → Set ℂ) (a : ℕ → ℂ) (ε : ℝ) (n : ℕ)
    (hpeq : EqOn (p n) (p' n) (V n)) :
    FrontSuccess η p σ V a ε n = FrontSuccess η p' σ V a ε n := by
  suffices hsub : ∀ (q q' : ℕ → ℂ → ℝ), EqOn (q n) (q' n) (V n) →
      FrontSuccess η q σ V a ε n ⊆ FrontSuccess η q' σ V a ε n from
    Subset.antisymm (hsub p p' hpeq) (hsub p' p hpeq.symm)
  intro q q' hqq ω hω
  let τ := frontTime (fun t => q n (η n ω t)) 1
  obtain ⟨hfirst, hhit, hσ, hpath, hoffset⟩ := hω
  have heq : EqOn (fun t => q n (η n ω t)) (fun t => q' n (η n ω t)) (Icc 0 τ) :=
    fun t ht => hqq (hpath ht)
  have hfirst' := firstFrontTime_eq_of_prefix _ _ 1 τ hfirst hhit heq
  have ht : frontTime (fun t => q' n (η n ω t)) 1 = τ := by
    simp only [frontTime, hfirst', WithTop.untopD_coe]
  change firstFrontTime (fun t => q' n (η n ω t)) 1 = _ ∧ _
  rw [ht]
  exact ⟨hfirst', (heq ⟨bot_le, le_rfl⟩).symm.trans hhit, hσ, hpath, hoffset⟩

/-- A globally continuous progress coordinate gives the actual adapted
front stopping time, including the possibility of no hit. -/
theorem firstFrontTime_stopping
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (η : Ω → ℝ≥0 → ℂ) (ha : Adapted ℱ (fun t ω => η ω t))
    (hc : ∀ ω, Continuous (η ω)) (p : ℂ → ℝ) (hp : Continuous p) :
    IsStoppingTime ℱ (fun ω => firstFrontTime (fun t => p (η ω t)) 1) :=
  firstFrontTime_isStoppingTime ℱ (fun t ω => p (η ω t))
    (fun t => hp.measurable.comp (ha t)) (fun ω => hp.comp (hc ω)) 1

/-- Success is measurable when the progress coordinate is globally
continuous; the next theorem removes this unnecessary global requirement. -/
theorem measurableSet_frontSuccess_of_continuous
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (η : ℕ → Ω → ℝ≥0 → ℂ) (p : ℕ → ℂ → ℝ) (σ : Ω → ℝ≥0)
    (V : ℕ → Set ℂ) (a : ℕ → ℂ) (ε : ℝ) (n : ℕ)
    (ha : Adapted ℱ (fun t ω => η n ω t)) (hc : ∀ ω, Continuous (η n ω))
    (hp : Continuous (p n)) (hσ : Measurable σ) (hV : IsOpen (V n)) :
    MeasurableSet (FrontSuccess η p σ V a ε n) := by
  let f := sourceTracePath (η n) hc
  have hfm : Measurable f := source_path_measurable f
    (fun t => (ha t).mono (ℱ.le t) le_rfl)
  let τ := fun ω => frontTime (fun t => p n (η n ω t)) 1
  have hfirst := firstFrontTime_stopping ℱ (η n) ha hc (p n) hp
  have hτ : Measurable τ := hfirst.measurable'.untopD 0
  have heval : Measurable (fun ω => η n ω (τ ω)) :=
    continuous_eval.measurable.comp (hfm.prodMk hτ)
  have hprefix := measurableSet_prefix_mapsTo f hfm τ hτ (V n) hV
  have hset : MeasurableSet {ω |
      firstFrontTime (fun t => p n (η n ω t)) 1 = (τ ω : WithTop ℝ≥0) ∧
      p n (η n ω (τ ω)) = 1 ∧ σ ω < τ ω ∧
      MapsTo (η n ω) (Icc 0 (τ ω)) (V n) ∧ ‖η n ω (τ ω) - a n‖ < ε / 4} :=
    (measurableSet_eq_fun hfirst.measurable'
      (WithTop.continuous_coe.measurable.comp hτ)).inter
      ((measurableSet_eq_fun (hp.measurable.comp heval) measurable_const).inter
        ((measurableSet_lt hσ hτ).inter
          (hprefix.inter (measurableSet_lt (heval.sub_const _).norm measurable_const))))
  exact hset

/-- A closed physical ribbon patch supplies a continuous progress extension
by the proved Tietze theorem. -/
theorem exists_continuous_progress_extension
    (p : ℂ → ℝ) (K : Set ℂ) (hK : IsClosed K) (hp : ContinuousOn p K) :
    ∃ g : C(ℂ, ℝ), EqOn p g K := by
  let f : C(K, ℝ) := ⟨fun z => p z, hp.domRestrict⟩
  obtain ⟨g, hg⟩ := f.exists_restrict_eq hK
  refine ⟨g, ?_⟩
  intro z hz
  have hh := congrArg (fun F : C(K, ℝ) => F ⟨z, hz⟩) hg
  exact hh.symm

/-- The original local front event is measurable, and agrees there with an
adapted front stopping time obtained by extending the ribbon coordinate. -/
theorem measurableSet_frontSuccess_of_continuousOn
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (η : ℕ → Ω → ℝ≥0 → ℂ) (p : ℕ → ℂ → ℝ) (σ : Ω → ℝ≥0)
    (V : ℕ → Set ℂ) (a : ℕ → ℂ) (ε : ℝ) (n : ℕ)
    (ha : Adapted ℱ (fun t ω => η n ω t)) (hc : ∀ ω, Continuous (η n ω))
    (K : Set ℂ) (hK : IsClosed K) (hp : ContinuousOn (p n) K)
    (hσ : Measurable σ) (hV : IsOpen (V n)) (hVK : V n ⊆ K) :
    MeasurableSet (FrontSuccess η p σ V a ε n) ∧
      ∃ ρ : Ω → WithTop ℝ≥0, IsStoppingTime ℱ ρ ∧
        ∀ ω ∈ FrontSuccess η p σ V a ε n,
          ρ ω = firstFrontTime (fun t => p n (η n ω t)) 1 := by
  obtain ⟨g, hg⟩ := exists_continuous_progress_extension (p n) K hK hp
  let p' : ℕ → ℂ → ℝ := fun _ => g
  have heq := frontSuccess_eq_of_eqOn η p p' σ V a ε n (hg.mono hVK)
  have hmeas := measurableSet_frontSuccess_of_continuous ℱ η p' σ V a ε n
    ha hc g.continuous hσ hV
  refine ⟨heq.symm ▸ hmeas, (fun ω => firstFrontTime (fun t => g (η n ω t)) 1),
    firstFrontTime_stopping ℱ (η n) ha hc g g.continuous, ?_⟩
  intro ω hω
  obtain ⟨hfirst, hhit, _, hpath, _⟩ := hω
  exact (firstFrontTime_eq_of_prefix _ _ 1 _ hfirst hhit
    (fun t ht => hg (hVK (hpath ht)))).trans hfirst.symm

/-- The full local-coordinate success-and-mass event is measurable. This is
the concrete event used by the repeated ribbon passage argument. -/
theorem measurableSet_frontSuccess_mass
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (η : ℕ → Ω → ℝ≥0 → ℂ) (p : ℕ → ℂ → ℝ) (σ : Ω → ℝ≥0)
    (V : ℕ → Set ℂ) (a : ℕ → ℂ) (ε : ℝ) (n : ℕ)
    (ha : Adapted ℱ (fun t ω => η n ω t)) (hc : ∀ ω, Continuous (η n ω))
    (K : Set ℂ) (hK : IsClosed K) (hp : ContinuousOn (p n) K)
    (hσ : Measurable σ) (hV : IsOpen (V n)) (hVK : V n ⊆ K)
    (κ v c : ℝ) (R : Set ℂ) :
    MeasurableSet {ω | ω ∈ FrontSuccess η p σ V a ε n ∧ ENNReal.ofReal c ≤
      segmentSausageCharge κ (η n ω) (σ ω)
        (frontTime (fun t => p n (η n ω t)) 1) v R} := by
  obtain ⟨g, hg⟩ := exists_continuous_progress_extension (p n) K hK hp
  let p' : ℕ → ℂ → ℝ := fun _ => g
  have heq := frontSuccess_eq_of_eqOn η p p' σ V a ε n (hg.mono hVK)
  let τ := fun ω => frontTime (fun t => g (η n ω t)) 1
  have hτ : Measurable τ := (firstFrontTime_stopping ℱ (η n) ha hc g g.continuous).measurable'.untopD 0
  let f := sourceTracePath (η n) hc
  have hfm : Measurable f := source_path_measurable f
    (fun t => (ha t).mono (ℱ.le t) le_rfl)
  have hmass := segmentSausageCharge_measurable f hfm σ τ hσ hτ κ v R
  have hm := (measurableSet_frontSuccess_of_continuous ℱ η p' σ V a ε n
    ha hc g.continuous hσ hV).inter (measurableSet_le (measurable_const : Measurable (fun _ : Ω => ENNReal.ofReal c)) hmass)
  convert hm using 1
  ext ω
  by_cases hω : ω ∈ FrontSuccess η p σ V a ε n
  · have hω' : ω ∈ FrontSuccess η p' σ V a ε n := heq ▸ hω
    have hωsave := hω
    obtain ⟨hfirst, hhit, _, hpath, _⟩ := hω
    have hfirst' := firstFrontTime_eq_of_prefix _ _ 1 _ hfirst hhit
      (fun t ht => hg (hVK (hpath ht)))
    have ht : τ ω = frontTime (fun t => p n (η n ω t)) 1 := by
      simp only [τ, frontTime, hfirst', WithTop.untopD_coe]
    simp only [mem_ofPred_eq, mem_inter_iff, hωsave, hω', true_and, ht]
    rfl
  · have hω' : ω ∉ FrontSuccess η p' σ V a ε n := by simpa only [← heq] using hω
    simp only [mem_ofPred_eq, mem_inter_iff, hω, hω', false_and]

end SLEExactGauge.FrontSuccessMeasurability

end

end OAI
