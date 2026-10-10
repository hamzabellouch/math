import OAI.Probability.SLE.Geometry.FrontSuccessMeasurability

namespace OAI

/-! The front success-and-mass event is measurable in the actual extended
front past, not merely in the full path sigma algebra. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.FrontSuccessMeasurability
open FirstFrontPassage PassageSuccess

local instance stoppedFrontPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance stoppedFrontPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

/-- Stop at a possibly infinite time, leaving the path running if no front
is ever reached. -/
def stoppedAtPath (f : C(ℝ≥0, ℂ)) (ρ : WithTop ℝ≥0) : C(ℝ≥0, ℂ) :=
  if ρ = ⊤ then f else clampedPath f 0 (ρ.untopD 0)

theorem stoppedAtPath_apply (f : C(ℝ≥0, ℂ)) (ρ : WithTop ℝ≥0) (t : ℝ≥0) :
    stoppedAtPath f ρ t = f (min ρ (t : WithTop ℝ≥0)).untopA := by
  cases ρ with
  | top => simp only [stoppedAtPath, ite_true, min_top_left, WithTop.untopA, WithTop.untopD_coe]
  | coe ρ => simp only [stoppedAtPath, WithTop.coe_ne_top, ite_false, WithTop.untopD_coe,
      clampedPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk, zero_le, max_eq_right,
      ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe, min_comm]

/-- The whole stopped path is measurable in its stopping-time past even
when that stopping time can be infinite. -/
theorem stoppedAtPath_measurable
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (η : Ω → ℝ≥0 → ℂ) (ha : Adapted ℱ (fun t ω => η ω t))
    (hc : ∀ ω, Continuous (η ω)) (ρ : Ω → WithTop ℝ≥0) (hρ : IsStoppingTime ℱ ρ) :
    Measurable[hρ.measurableSpace]
      (fun ω => stoppedAtPath (sourceTracePath η hc ω) (ρ ω)) := by
  have hp := ha.stronglyAdapted.isStronglyProgressive_of_continuous hc
  let : MeasurableSpace Ω := hρ.measurableSpace
  apply source_path_measurable
  intro t
  have hm := measurable_stoppedValue hp (hρ.min_const t)
  have hm' := hm.mono (IsStoppingTime.measurableSpace_mono (hρ.min_const t) hρ
    (fun _ => min_le_left _ _)) le_rfl
  change Measurable (fun ω => η ω (min (ρ ω) (t : WithTop ℝ≥0)).untopA) at hm'
  simpa only [stoppedAtPath_apply, sourceTracePath, ContinuousMap.coe_mk] using hm'

/-- A finite original stopping time truncated at the front is measurable
in the front past. -/
theorem truncated_start_measurable
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (σ : Ω → ℝ≥0) (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0)))
    (ρ : Ω → WithTop ℝ≥0) (hρ : IsStoppingTime ℱ ρ) :
    Measurable[hρ.measurableSpace]
      (fun ω => (min (σ ω : WithTop ℝ≥0) (ρ ω)).untopD 0) := by
  exact ((hσ.min hρ).measurable.mono
    (IsStoppingTime.measurableSpace_mono (hσ.min hρ) hρ (fun _ => min_le_right _ _)) le_rfl).untopD 0

/-- A finite first front for a continuous coordinate is attained. -/
theorem firstFrontTime_attained
    (x : ℝ≥0 → ℝ) (hx : Continuous x) (q : ℝ) (τ : ℝ≥0)
    (hτ : firstFrontTime x q = (τ : WithTop ℝ≥0)) : x τ = q := by
  have hh : hittingAfter (fun t (_ : Unit) => x t - q) {0} 0 () ≤ (τ : WithTop ℝ≥0) := hτ.le
  obtain ⟨u, hu, hxu⟩ := (hittingAfter_zero_le_iff (fun t (_ : Unit) => x t - q)
    (fun _ => hx.sub continuous_const) 0 τ ()).mp hh
  have hlu := hittingAfter_le_of_mem (u := fun t (_ : Unit) => x t - q)
    (ω := ()) hu.1 (show x u - q ∈ ({0} : Set ℝ) from hxu)
  change firstFrontTime x q ≤ (u : WithTop ℝ≥0) at hlu
  rw [hτ, WithTop.coe_le_coe] at hlu
  have he : u = τ := le_antisymm hu.2 hlu
  exact he ▸ sub_eq_zero.mp hxu

/-- Stopping the path and truncating the earlier time at the front does not
change the concrete success event. -/
theorem frontSuccess_stopped_eq
    {Ω : Type*} (η : ℕ → Ω → ℝ≥0 → ℂ) (p : ℕ → ℂ → ℝ)
    (σ : Ω → ℝ≥0) (V : ℕ → Set ℂ) (a : ℕ → ℂ) (ε : ℝ) (n : ℕ)
    (hc : ∀ ω, Continuous (η n ω)) (hp : Continuous (p n)) :
    let ρ := fun ω => firstFrontTime (fun t => p n (η n ω t)) 1
    let η' := fun (_ : ℕ) ω => (stoppedAtPath (sourceTracePath (η n) hc ω) (ρ ω) : ℝ≥0 → ℂ)
    let σ' := fun ω => (min (σ ω : WithTop ℝ≥0) (ρ ω)).untopD 0
    FrontSuccess η p σ V a ε n = FrontSuccess η' p σ' V a ε n := by
  dsimp only
  ext ω
  let ρ := firstFrontTime (fun t => p n (η n ω t)) 1
  cases hρ : ρ with
  | top =>
    have hfirst : firstFrontTime (fun t => p n (η n ω t)) 1 = ⊤ := hρ
    simp only [FrontSuccess, hfirst, WithTop.top_ne_coe, false_and, mem_ofPred_eq,
      stoppedAtPath, ite_true, min_top_right, WithTop.untopD_coe,
      sourceTracePath, ContinuousMap.coe_mk]
  | coe τ =>
    have hfirst : firstFrontTime (fun t => p n (η n ω t)) 1 = (τ : WithTop ℝ≥0) := hρ
    have hhit := firstFrontTime_attained _ (hp.comp (hc ω)) 1 τ hfirst
    have hpath : EqOn
        (fun t => stoppedAtPath (sourceTracePath (η n) hc ω) (ρ) t) (η n ω) (Icc 0 τ) := by
      intro t ht
      simp only [hρ, stoppedAtPath, WithTop.coe_ne_top, ite_false, WithTop.untopD_coe,
        clampedPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        min_eq_left ht.2, max_eq_right ht.1]
      rfl
    have hfirst' := firstFrontTime_eq_of_prefix
      (fun t => p n (η n ω t)) (fun t => p n (stoppedAtPath (sourceTracePath (η n) hc ω) ρ t))
      1 τ hfirst hhit (fun t ht => congrArg (p n) (hpath ht).symm)
    have ht : frontTime (fun t => p n (η n ω t)) 1 = τ := by
      simp only [frontTime, hfirst, WithTop.untopD_coe]
    have ht' : frontTime
        (fun t => p n (stoppedAtPath (sourceTracePath (η n) hc ω) ρ t)) 1 = τ := by
      simp only [frontTime, hfirst', WithTop.untopD_coe]
    have hmaps : MapsTo (fun t => stoppedAtPath (sourceTracePath (η n) hc ω) ρ t)
        (Icc 0 τ) (V n) ↔ MapsTo (η n ω) (Icc 0 τ) (V n) := by
      constructor <;> intro h t ht
      · simpa only [hpath ht] using h ht
      · simpa only [hpath ht] using h ht
    have hsig : (min (σ ω : WithTop ℝ≥0) ρ).untopD 0 = min (σ ω) τ := by
      simp only [hρ, ← WithTop.coe_min, WithTop.untopD_coe]
    have hendpoint := hpath ⟨bot_le, le_rfl⟩
    rw [hρ] at hfirst' ht' hmaps hsig hendpoint
    change (_ : Prop) ↔ (_ : Prop)
    simp only [FrontSuccess, mem_ofPred_eq, ht, ht', hfirst, hfirst', hsig,
      hendpoint, hmaps, min_lt_iff, lt_self_iff_false, or_false, true_and]

/-- The mass on a successful passage is also unchanged by stopping at the
front, including the earlier endpoint. -/
theorem frontSuccess_mass_stopped_eq
    {Ω : Type*} (η : ℕ → Ω → ℝ≥0 → ℂ) (p : ℕ → ℂ → ℝ)
    (σ : Ω → ℝ≥0) (V : ℕ → Set ℂ) (a : ℕ → ℂ) (ε : ℝ) (n : ℕ)
    (hc : ∀ ω, Continuous (η n ω)) (hp : Continuous (p n)) (κ v c : ℝ) (R : Set ℂ) :
    let ρ := fun ω => firstFrontTime (fun t => p n (η n ω t)) 1
    let η' := fun (_ : ℕ) ω => (stoppedAtPath (sourceTracePath (η n) hc ω) (ρ ω) : ℝ≥0 → ℂ)
    let σ' := fun ω => (min (σ ω : WithTop ℝ≥0) (ρ ω)).untopD 0
    {ω | ω ∈ FrontSuccess η p σ V a ε n ∧ ENNReal.ofReal c ≤
      segmentSausageCharge κ (η n ω) (σ ω) (frontTime (fun t => p n (η n ω t)) 1) v R} =
    {ω | ω ∈ FrontSuccess η' p σ' V a ε n ∧ ENNReal.ofReal c ≤
      segmentSausageCharge κ (η' n ω) (σ' ω) (frontTime (fun t => p n (η' n ω t)) 1) v R} := by
  dsimp only
  have hsuccess := frontSuccess_stopped_eq η p σ V a ε n hc hp
  ext ω
  by_cases hω : ω ∈ FrontSuccess η p σ V a ε n
  · have hω' := hsuccess ▸ hω
    have hωsave := hω
    obtain ⟨hfirst, _, hστ, _, _⟩ := hω
    let τ := frontTime (fun t => p n (η n ω t)) 1
    have heval (t : ℝ≥0) (ht : t ≤ τ) :
        stoppedAtPath (sourceTracePath (η n) hc ω)
          (firstFrontTime (fun t => p n (η n ω t)) 1) t = η n ω t := by
      change t ≤ frontTime (fun t => p n (η n ω t)) 1 at ht
      simp only [hfirst, stoppedAtPath, WithTop.coe_ne_top, ite_false, WithTop.untopD_coe,
        clampedPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        min_eq_left ht, max_eq_right (show (0 : ℝ≥0) ≤ t from bot_le)]
      rfl
    have hfirst' := firstFrontTime_eq_of_prefix
      (fun t => p n (η n ω t))
      (fun t => p n (stoppedAtPath (sourceTracePath (η n) hc ω)
        (firstFrontTime (fun u => p n (η n ω u)) 1) t))
      1 τ hfirst (by exact hωsave.2.1)
      (fun t ht => congrArg (p n) (heval t ht.2).symm)
    have ht' : frontTime (fun t => p n (stoppedAtPath (sourceTracePath (η n) hc ω)
        (firstFrontTime (fun u => p n (η n ω u)) 1) t)) 1 = τ := by
      simp only [frontTime, hfirst', WithTop.untopD_coe]
    have hσ' : (min (σ ω : WithTop ℝ≥0)
        (firstFrontTime (fun t => p n (η n ω t)) 1)).untopD 0 = σ ω := by
      rw [hfirst, ← WithTop.coe_min, WithTop.untopD_coe, min_eq_left hστ.le]
    have hsausage := sourceSausageSet_congr_interval
      (s := σ ω) (t := τ) (fun t ht => heval t ht.2) v
    simp only [mem_ofPred_eq, hωsave, hω', true_and, hσ', ht', segmentSausageCharge, hsausage]
    rfl
  · have hω' : ω ∉ FrontSuccess
        (fun (_ : ℕ) ω => (stoppedAtPath (sourceTracePath (η n) hc ω)
          (firstFrontTime (fun t => p n (η n ω t)) 1) : ℝ≥0 → ℂ)) p
        (fun ω => (min (σ ω : WithTop ℝ≥0)
          (firstFrontTime (fun t => p n (η n ω t)) 1)).untopD 0) V a ε n := by
      simpa only [← hsuccess] using hω
    simp only [mem_ofPred_eq, hω, hω', false_and]

/-- The full success-and-mass event belongs to the front past. -/
theorem frontSuccess_mass_measurable_at_front
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (η : ℕ → Ω → ℝ≥0 → ℂ) (p : ℕ → ℂ → ℝ) (σ : Ω → ℝ≥0)
    (V : ℕ → Set ℂ) (a : ℕ → ℂ) (ε : ℝ) (n : ℕ)
    (ha : Adapted ℱ (fun t ω => η n ω t)) (hc : ∀ ω, Continuous (η n ω))
    (hp : Continuous (p n)) (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0)))
    (hV : IsOpen (V n)) (κ v c : ℝ) (R : Set ℂ) :
    let hρ := firstFrontTime_stopping ℱ (η n) ha hc (p n) hp
    MeasurableSet[hρ.measurableSpace] {ω | ω ∈ FrontSuccess η p σ V a ε n ∧ ENNReal.ofReal c ≤
      segmentSausageCharge κ (η n ω) (σ ω) (frontTime (fun t => p n (η n ω t)) 1) v R} := by
  dsimp only
  let ρ := fun ω => firstFrontTime (fun t => p n (η n ω t)) 1
  have hρ := firstFrontTime_stopping ℱ (η n) ha hc (p n) hp
  let f := fun ω => stoppedAtPath (sourceTracePath (η n) hc ω) (ρ ω)
  have hfm : Measurable[hρ.measurableSpace] f := stoppedAtPath_measurable ℱ (η n) ha hc ρ hρ
  let η' : ℕ → Ω → ℝ≥0 → ℂ := fun _ ω => f ω
  let σ' := fun ω => (min (σ ω : WithTop ℝ≥0) (ρ ω)).untopD 0
  have hσ' : Measurable[hρ.measurableSpace] σ' := truncated_start_measurable ℱ σ hσ ρ hρ
  rw [frontSuccess_mass_stopped_eq η p σ V a ε n hc hp κ v c R]
  let : MeasurableSpace Ω := hρ.measurableSpace
  let ℱ' : Filtration ℝ≥0 hρ.measurableSpace := Filtration.const ℝ≥0 hρ.measurableSpace le_rfl
  apply measurableSet_frontSuccess_mass ℱ' η' p σ' V a ε n
    (fun t => (continuous_eval_const t).measurable.comp hfm) (fun ω => (f ω).continuous)
    univ isClosed_univ hp.continuousOn hσ' hV (subset_univ _) κ v c R

/-- Local physical ribbon coordinates suffice for an actual stopping time
whose past contains the full success-and-mass event. -/
theorem local_frontSuccess_mass_measurable_at_front
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (η : ℕ → Ω → ℝ≥0 → ℂ) (p : ℕ → ℂ → ℝ) (σ : Ω → ℝ≥0)
    (V : ℕ → Set ℂ) (a : ℕ → ℂ) (ε : ℝ) (n : ℕ)
    (ha : Adapted ℱ (fun t ω => η n ω t)) (hc : ∀ ω, Continuous (η n ω))
    (K : Set ℂ) (hK : IsClosed K) (hp : ContinuousOn (p n) K)
    (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0)))
    (hV : IsOpen (V n)) (hVK : V n ⊆ K) (κ v c : ℝ) (R : Set ℂ) :
    ∃ ρ : Ω → WithTop ℝ≥0, ∃ hρ : IsStoppingTime ℱ ρ,
      MeasurableSet[hρ.measurableSpace] (FrontSuccess η p σ V a ε n) ∧
      MeasurableSet[hρ.measurableSpace] {ω | ω ∈ FrontSuccess η p σ V a ε n ∧ ENNReal.ofReal c ≤
        segmentSausageCharge κ (η n ω) (σ ω)
          (frontTime (fun t => p n (η n ω t)) 1) v R} ∧
      ∀ ω ∈ FrontSuccess η p σ V a ε n,
        ρ ω = firstFrontTime (fun t => p n (η n ω t)) 1 := by
  obtain ⟨g, hg⟩ := exists_continuous_progress_extension (p n) K hK hp
  let p' : ℕ → ℂ → ℝ := fun _ => g
  let ρ := fun ω => firstFrontTime (fun t => g (η n ω t)) 1
  have hρ := firstFrontTime_stopping ℱ (η n) ha hc g g.continuous
  have heq := frontSuccess_eq_of_eqOn η p p' σ V a ε n (hg.mono hVK)
  have htime (ω : Ω) (hω : ω ∈ FrontSuccess η p σ V a ε n) :
      ρ ω = firstFrontTime (fun t => p n (η n ω t)) 1 := by
    obtain ⟨hfirst, hhit, _, hpath, _⟩ := hω
    exact (firstFrontTime_eq_of_prefix _ _ 1 _ hfirst hhit
      (fun t ht => hg (hVK (hpath ht)))).trans hfirst.symm
  have hmassEq (b : ℝ) :
      {ω | ω ∈ FrontSuccess η p σ V a ε n ∧ ENNReal.ofReal b ≤
        segmentSausageCharge κ (η n ω) (σ ω)
          (frontTime (fun t => p n (η n ω t)) 1) v R} =
      {ω | ω ∈ FrontSuccess η p' σ V a ε n ∧ ENNReal.ofReal b ≤
        segmentSausageCharge κ (η n ω) (σ ω)
          (frontTime (fun t => p' n (η n ω t)) 1) v R} := by
    ext ω
    by_cases hω : ω ∈ FrontSuccess η p σ V a ε n
    · have hω' := heq ▸ hω
      have ht : frontTime (fun t => p' n (η n ω t)) 1 =
          frontTime (fun t => p n (η n ω t)) 1 :=
        congrArg (fun z : WithTop ℝ≥0 => z.untopD 0) (htime ω hω)
      simp only [mem_ofPred_eq, hω, hω', true_and, ht]
    · have hω' : ω ∉ FrontSuccess η p' σ V a ε n := by simpa only [← heq] using hω
      simp only [mem_ofPred_eq, hω, hω', false_and]
  have hmass (b : ℝ) := frontSuccess_mass_measurable_at_front ℱ η p' σ V a ε n
    ha hc g.continuous hσ hV κ v b R
  refine ⟨ρ, hρ, ?_, ?_, htime⟩
  · have hz := hmass 0
    rw [← hmassEq 0] at hz
    simpa only [ENNReal.ofReal_zero, zero_le, and_true, ofPred_mem_eq] using hz
  · rw [hmassEq c]
    exact hmass c

end SLEExactGauge.FrontSuccessMeasurability

end

end OAI
