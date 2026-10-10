import OAI.Probability.SLE.Mass.LevelApproximationSupport
import OAI.Probability.SLE.Mass.LevelRadonExtraction
import OAI.Probability.SLE.Mass.RadonTestLimitProperties

namespace OAI

/-! Actual past support of every convex-tail Radon limit.  Compact tests
separated from the past trace vanish at all sufficiently high levels. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma level_density_eventually_zero_on_compact
    {Ω : Type*} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ} (ω : Ω)
    (hBc : Continuous (fun s => B s ω))
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane)
    (hdis : Disjoint K (γ ω '' Icc 0 t))
    (u : ℕ → ℝ) (hu : Tendsto u atTop atTop) :
    ∀ᶠ n in atTop, ∀ z ∈ K,
      levelApproximationDensity κ B γ G (u n) t ω z = 0 := by
  let S := γ ω '' Icc 0 t
  have hS : IsClosed S := (isCompact_Icc.image hw.1).isClosed
  have hSne : S.Nonempty := ⟨γ ω 0,0,⟨le_rfl,bot_le⟩,rfl⟩
  obtain ⟨r,hr,hrK⟩ := hK.exists_forall_le'
    (Complex.continuous_im.min (Metric.continuous_infDist_pt (s := S))).continuousOn
    (fun z hz => lt_min (hKH hz)
      ((hS.notMem_iff_infDist_pos hSne).mp (fun hs => Set.disjoint_left.mp hdis hz hs)))
  obtain ⟨M,hM⟩ := hK.bddAbove_image Complex.continuous_im.continuousOn
  have hlim : Tendsto (fun n => (2*M)*Real.exp (-u n)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hu)).const_mul (2*M)
  filter_upwards [hlim.eventually (eventually_lt_nhds hr)] with n hn z hz
  apply levelApproximationDensity_eq_zero_of_avoidance ω (hBc.const_mul _) hw z r hr
    ((hrK z hz).trans (min_le_left _ _)) (u n)
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM ⟨z,hz,rfl⟩)
      (by norm_num : (0:ℝ) ≤ 2)) (Real.exp_pos _).le).trans_lt hn) t
  intro s hs
  exact ((hrK z hz).trans (min_le_right _ _)).trans
    ((Metric.infDist_le_dist_of_mem (show γ ω s ∈ S from ⟨s,hs,rfl⟩)).trans_eq (dist_comm _ _))

lemma halfPlane_level_test_eventually_zero_off_past
    {Ω : Type*} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ} (ω : Ω)
    (hBc : Continuous (fun s => B s ω))
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) (f : C_c(upperHalfPlane,ℝ))
    (hf : ∀ z ∈ tsupport f, (z : ℂ) ∉ γ ω '' Icc 0 t)
    (u : ℕ → ℝ) (hu : Tendsto u atTop atTop) :
    ∀ᶠ n in atTop, ∫ z, f z ∂halfPlaneLevelMeasure κ B γ G (u n) t ω = 0 := by
  let K := (Subtype.val : upperHalfPlane → ℂ) '' tsupport f
  have hK : IsCompact K := f.hasCompactSupport.image continuous_subtype_val
  have hKH : K ⊆ upperHalfPlane := by rintro _ ⟨z,_,rfl⟩; exact z.property
  have hdis : Disjoint K (γ ω '' Icc 0 t) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨z,hz,rfl⟩ hs
    exact hf z hz hs
  filter_upwards [level_density_eventually_zero_on_compact ω hBc hw t K hK hKH hdis u hu]
    with n hn
  have hzero : halfPlaneLevelMeasure κ B γ G (u n) t ω (tsupport f) = 0 := by
    rw [halfPlaneLevelMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
      levelApproximation,withDensity_apply _ hK.measurableSet]
    apply le_antisymm ?_ bot_le
    apply (setLIntegral_mono' hK.measurableSet (fun z hz => le_of_eq (hn z hz))).trans_eq
    simp
  apply integral_eq_zero_of_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with z hz
  exact image_eq_zero_of_notMem_tsupport hz

/-- Every compact test away from the actual past vanishes on every late
convex tail.  The coefficients may be arbitrary: no normalization is used. -/
lemma convex_level_test_eventually_zero_off_past
    {Ω : Type*} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ} (ω : Ω)
    (hBc : Continuous (fun s => B s ω))
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) (f : C_c(upperHalfPlane,ℝ))
    (hf : ∀ z ∈ tsupport f, (z : ℂ) ∉ γ ω '' Icc 0 t)
    (u : ℕ → ℝ) (hu : Tendsto u atTop atTop)
    (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) :
    ∀ᶠ n in atTop, ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n t ω = 0 := by
  let K := (Subtype.val : upperHalfPlane → ℂ) '' tsupport f
  have hK : IsCompact K := f.hasCompactSupport.image continuous_subtype_val
  have hKH : K ⊆ upperHalfPlane := by rintro _ ⟨z,_,rfl⟩; exact z.property
  have hdis : Disjoint K (γ ω '' Icc 0 t) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨z,hz,rfl⟩ hs
    exact hf z hz hs
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (level_density_eventually_zero_on_compact ω hBc hw t K hK hKH hdis u hu)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hzero : convexLevelMeasure κ B γ G u s w n t ω (tsupport f) = 0 := by
    rw [convexLevelMeasure,Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [Measure.smul_apply]
    suffices he : halfPlaneLevelMeasure κ B γ G (u (n+i)) t ω (tsupport f) = 0 by
      simp only [he,smul_zero]
    rw [halfPlaneLevelMeasure,comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
      levelApproximation,withDensity_apply _ hK.measurableSet]
    apply le_antisymm ?_ bot_le
    apply (setLIntegral_mono' hK.measurableSet
      (fun z hz => le_of_eq (hN (n+i) (hn.trans (Nat.le_add_right n i)) z hz))).trans_eq
    simp
  apply integral_eq_zero_of_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with z hz
  exact image_eq_zero_of_notMem_tsupport hz

/-- Any vague limit of the actual convex level measures at a finite time
is carried by the actual trace up to that time. -/
theorem convex_level_radon_limit_carried_by_past
    {Ω : Type*} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ} (ω : Ω)
    (hBc : Continuous (fun s => B s ω))
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) (u : ℕ → ℝ) (hu : Tendsto u atTop atTop)
    (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (ν : Measure upperHalfPlane) [ν.Regular]
    (hlim : ∀ f : C_c(upperHalfPlane,ℝ),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n t ω)
        atTop (𝓝 (∫ z, f z ∂ν))) :
    ν {z : upperHalfPlane | (z : ℂ) ∉ γ ω '' Icc 0 t} = 0 := by
  let S : Set upperHalfPlane := {z | (z : ℂ) ∈ γ ω '' Icc 0 t}
  apply radon_limit_carried_by_closed _ ν hlim S
    (((isCompact_Icc.image hw.1).isClosed).preimage continuous_subtype_val)
  intro f hf
  exact convex_level_test_eventually_zero_off_past ω hBc hw t f hf u hu s w

theorem convex_level_radon_limit_zero_at_zero
    {Ω : Type*} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ} (ω : Ω)
    (hBc : Continuous (fun s => B s ω))
    (hw : IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : Tendsto u atTop atTop)
    (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (ν : Measure upperHalfPlane) [ν.Regular]
    (hlim : ∀ f : C_c(upperHalfPlane,ℝ),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n 0 ω)
        atTop (𝓝 (∫ z, f z ∂ν))) : ν = 0 := by
  have h := convex_level_radon_limit_carried_by_past ω hBc hw 0 u hu s w ν hlim
  have he : {z : upperHalfPlane | (z : ℂ) ∉ γ ω '' Icc 0 0} = univ := by
    apply Set.eq_univ_of_forall
    intro z hz
    obtain ⟨a,ha,haz⟩ := hz
    have ha0 : a = 0 := le_antisymm ha.2 ha.1
    subst a
    have hz0 : (z : ℂ) = 0 := haz.symm.trans hw.2.1
    have hpos := z.property
    change 0 < (z : ℂ).im at hpos
    simp only [hz0,Complex.zero_im,lt_self_iff_false] at hpos
  rw [he] at h
  exact Measure.measure_univ_eq_zero.mp h

/-- The support conclusion holds simultaneously for the prescribed
countable list of finite times on the same vague-convergence event. -/
theorem ae_common_level_radon_limits_carried_by_past
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
    {γ : Ω → ℝ≥0 → ℂ} {G F : Ω → ℝ≥0 → ℂ → ℂ}
    (hBc : ∀ ω, Continuous (fun s => B s ω))
    (hw : ∀ ω, IsCapacityTwoWitness
      (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (t : ℕ → ℝ≥0) (u : ℕ → ℝ) (hu : Tendsto u atTop atTop)
    (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) (ν : ℕ → Ω → Measure upperHalfPlane)
    (hν : ∀ j ω, (ν j ω).Regular)
    (hlim : ∀ᵐ ω ∂P, ∀ j (f : C_c(upperHalfPlane,ℝ)),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n (t j) ω)
        atTop (𝓝 (∫ z, f z ∂ν j ω))) :
    ∀ᵐ ω ∂P, ∀ j, ν j ω {z : upperHalfPlane | (z : ℂ) ∉ γ ω '' Icc 0 (t j)} = 0 := by
  filter_upwards [hlim] with ω hω
  intro j
  let := hν j ω
  exact convex_level_radon_limit_carried_by_past ω (hBc ω) (hw ω) (t j) u hu
    s w (ν j ω) (hω j)

lemma past_inter_surviving_subset_segment (γ : ℝ≥0 → ℂ) (s t : ℝ≥0) :
    (γ '' Icc 0 t) ∩ survivingDomain γ s ⊆ γ '' Icc s t := by
  rintro z ⟨⟨a,ha,rfl⟩,hlive⟩
  have hsa : s ≤ a := by
    by_contra h
    exact hlive.1.2 ⟨a,⟨ha.1,(lt_of_not_ge h).le⟩,rfl⟩
  exact ⟨a,⟨hsa,ha.2⟩,rfl⟩

/-- A positive increment dominated by the past mass and by the remaining
mass is carried by the new segment. This is the deterministic consequence
of past support and the conditional-kernel future support. -/
theorem increment_le_restrict_trace_segment
    (γ : ℝ≥0 → ℂ) (s t : ℝ≥0) (η μpast μfuture ν : Measure upperHalfPlane)
    (hηpast : η ≤ μpast) (hηfuture : η ≤ μfuture) (hην : η ≤ ν)
    (hpast : μpast {z : upperHalfPlane | (z : ℂ) ∉ γ '' Icc 0 t} = 0)
    (hfuture : μfuture {z : upperHalfPlane | (z : ℂ) ∉ survivingDomain γ s} = 0) :
    η ≤ ν.restrict {z : upperHalfPlane | (z : ℂ) ∈ γ '' Icc s t} := by
  have hp : ∀ᵐ z : upperHalfPlane ∂η, (z : ℂ) ∈ γ '' Icc 0 t := by
    have hz : η {z : upperHalfPlane | (z : ℂ) ∉ γ '' Icc 0 t} = 0 :=
      le_zero_iff.mp ((hηpast {z : upperHalfPlane | (z : ℂ) ∉ γ '' Icc 0 t}).trans_eq hpast)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with z hz
    exact not_not.mp hz
  have hf : ∀ᵐ z : upperHalfPlane ∂η, (z : ℂ) ∈ survivingDomain γ s := by
    have hz : η {z : upperHalfPlane | (z : ℂ) ∉ survivingDomain γ s} = 0 :=
      le_zero_iff.mp ((hηfuture {z : upperHalfPlane | (z : ℂ) ∉ survivingDomain γ s}).trans_eq hfuture)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with z hz
    exact not_not.mp hz
  have hm : ∀ᵐ z ∂η, z ∈ {z : upperHalfPlane | (z : ℂ) ∈ γ '' Icc s t} := by
    filter_upwards [hp,hf] with z hzp hzf
    exact past_inter_surviving_subset_segment γ s t ⟨hzp,hzf⟩
  calc
    η = η.restrict {z : upperHalfPlane | (z : ℂ) ∈ γ '' Icc s t} :=
      (Measure.restrict_eq_self_of_ae_mem hm).symm
    _ ≤ ν.restrict {z : upperHalfPlane | (z : ℂ) ∈ γ '' Icc s t} :=
      Measure.restrict_mono le_rfl hην

end SLEExactGauge.Multipoint

end

end OAI
