import OAI.Probability.SLE.Geometry.SpatialPastKernels
import OAI.Probability.SLE.Mass.LevelRandomRadon
import OAI.Probability.SLE.Mass.SubSigmaRadonLimit

namespace OAI

/-! The finite-level mass accumulated by a deterministic time is measurable
in the natural driver filtration. All spatial variables are retained in the
past-measurable kernel before integration. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Classical
open scoped Topology NNReal ENNReal CompactlySupported

namespace SLEExactGauge

lemma radiusLevelTime_le_iff_prefix
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (u : ℝ) (hu : 0 ≤ u) (T : ℝ≥0) :
    radiusLevelTime γ G z u ≤ (T : ℝ≥0∞) ↔
      (z ∈ survivingDomain γ T ∧ fullRadius G T z ≤ (2*z.im)*Real.exp (-u)) ∨
      radiusLevelTime γ G z u < (T : ℝ≥0∞) := by
  constructor
  · intro h
    rcases h.eq_or_lt with he | ht
    · left
      obtain ⟨s,hs,hR⟩ := exists_live_level_of_radiusLevelTime_lt_top γ G z u
        (h.trans_lt (by simp))
      have hτ := radiusLevelTime_eq_of_live_level hU hw z u s hs hR
      have hsT : s = T := by exact_mod_cast hτ.symm.trans he
      subst s
      exact ⟨hs,hR.le⟩
    · exact Or.inr ht
  · rintro (⟨hT,hR⟩ | ht)
    · rcases hR.eq_or_lt with he | ht
      · rw [radiusLevelTime_eq_of_live_level hU hw z u T hT he]
      · exact (radiusLevelTime_lt_of_live_radius_lt hU hw z u hu T hT ht).le
    · exact ht.le

lemma capped_radiusLevelTime_dense
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (u : ℝ) (hu : 0 ≤ u) (T : ℝ≥0) :
    min (radiusLevelTime γ G z u) (T : ℝ≥0∞) =
      ⨅ n : ℕ, if denseSeq ℝ≥0 n < T ∧
        z ∈ survivingDomain γ (denseSeq ℝ≥0 n) ∧
        fullRadius G (denseSeq ℝ≥0 n) z < (2*z.im)*Real.exp (-u)
        then (denseSeq ℝ≥0 n : ℝ≥0∞) else T := by
  apply eq_of_forall_gt_iff
  intro x
  by_cases hTx : (T : ℝ≥0∞) < x
  · have hl : min (radiusLevelTime γ G z u) (T : ℝ≥0∞) < x :=
      (min_le_right _ _).trans_lt hTx
    have hr : (⨅ n : ℕ, if denseSeq ℝ≥0 n < T ∧
        z ∈ survivingDomain γ (denseSeq ℝ≥0 n) ∧
        fullRadius G (denseSeq ℝ≥0 n) z < (2*z.im)*Real.exp (-u)
        then (denseSeq ℝ≥0 n : ℝ≥0∞) else T) < x := by
      apply (iInf_le_of_le 0 ?_).trans_lt hTx
      split_ifs with h
      · exact_mod_cast h.1.le
      · exact le_rfl
    exact iff_of_true hl hr
  · rw [min_lt_iff, or_iff_left hTx, iInf_lt_iff,
      radiusLevelTime_lt_iff_dense hU hw z u hu x]
    constructor
    · rintro ⟨n,hnx,hn,hR⟩
      have hnT : denseSeq ℝ≥0 n < T := by
        exact_mod_cast hnx.trans_le (le_of_not_gt hTx)
      refine ⟨n,?_⟩
      have hh : denseSeq ℝ≥0 n < T ∧ z ∈ survivingDomain γ (denseSeq ℝ≥0 n) ∧
          fullRadius G (denseSeq ℝ≥0 n) z < (2*z.im)*Real.exp (-u) := ⟨hnT,hn,hR⟩
      rwa [ite_eq_left hh]
    · rintro ⟨n,hn⟩
      split_ifs at hn with h
      · exact ⟨n,hn,h.2.1,h.2.2⟩
      · exact False.elim (hTx hn)

private lemma prefix_time_measurable
    {Y : Type*} [MeasurableSpace Y] (τ : Y → ℝ≥0∞) (T : ℝ≥0)
    (D : ℕ → Y → Prop) (hD : ∀ n, MeasurableSet {p | D n p})
    (E : Y → Prop) (hE : MeasurableSet {p | E p})
    (hcap : ∀ p, min (τ p) (T : ℝ≥0∞) =
      ⨅ n : ℕ, if D n p then (denseSeq ℝ≥0 n : ℝ≥0∞) else T)
    (hlt : ∀ p, τ p < (T : ℝ≥0∞) ↔ ∃ n, D n p)
    (hle : ∀ p, τ p ≤ (T : ℝ≥0∞) ↔ E p ∨ τ p < (T : ℝ≥0∞)) :
    Measurable (fun p => min (τ p) (T : ℝ≥0∞)) ∧
      MeasurableSet {p | τ p ≤ (T : ℝ≥0∞)} := by
  classical
  have hmLess : MeasurableSet {p | τ p < (T : ℝ≥0∞)} := by
    have he : {p | τ p < (T : ℝ≥0∞)} = ⋃ n, {p | D n p} := by
      ext p
      simpa only [mem_iUnion,mem_ofPred_eq] using hlt p
    rw [he]
    exact MeasurableSet.iUnion hD
  constructor
  · have hh : Measurable (fun p => ⨅ n : ℕ,
        if D n p then (denseSeq ℝ≥0 n : ℝ≥0∞) else T) :=
      Measurable.iInf fun n => Measurable.ite (hD n) measurable_const measurable_const
    convert hh using 1
    exact funext hcap
  · convert hE.union hmLess using 1
    ext p
    exact hle p

private lemma prefix_level_time_measurable
    {Y : Type*} [MeasurableSpace Y] (τ : Y → ℝ≥0∞) (T : ℝ≥0)
    (R : ℝ≥0 → Y → ℝ) (L : ℝ≥0 → Y → Prop) (a : Y → ℝ)
    (hR : Measurable (fun p : Iic T × Y => if L p.1 p.2 then R p.1 p.2 else 0))
    (hL : MeasurableSet {p : Iic T × Y | L p.1 p.2}) (ha : Measurable a)
    (hcap : ∀ p, min (τ p) (T : ℝ≥0∞) =
      ⨅ n : ℕ, if denseSeq ℝ≥0 n < T ∧ L (denseSeq ℝ≥0 n) p ∧
        R (denseSeq ℝ≥0 n) p < a p then (denseSeq ℝ≥0 n : ℝ≥0∞) else T)
    (hlt : ∀ p, τ p < (T : ℝ≥0∞) ↔ ∃ n, denseSeq ℝ≥0 n < T ∧
      L (denseSeq ℝ≥0 n) p ∧ R (denseSeq ℝ≥0 n) p < a p)
    (hle : ∀ p, τ p ≤ (T : ℝ≥0∞) ↔
      (L T p ∧ R T p ≤ a p) ∨ τ p < (T : ℝ≥0∞)) :
    Measurable (fun p => min (τ p) (T : ℝ≥0∞)) ∧
      MeasurableSet {p | τ p ≤ (T : ℝ≥0∞)} := by
  classical
  have hmR (s : Iic T) : Measurable (fun p => if L s p then R s p else 0) :=
    hR.comp (measurable_const.prodMk measurable_id)
  have hmL (s : Iic T) : MeasurableSet {p | L s p} :=
    hL.preimage (measurable_const.prodMk measurable_id)
  have hmD (n : ℕ) : MeasurableSet {p : Y |
      denseSeq ℝ≥0 n < T ∧ L (denseSeq ℝ≥0 n) p ∧ R (denseSeq ℝ≥0 n) p < a p} := by
    by_cases hn : denseSeq ℝ≥0 n < T
    · let s : Iic T := ⟨denseSeq ℝ≥0 n,hn.le⟩
      convert (hmL s).inter (measurableSet_lt (hmR s) ha) using 1
      ext p
      simp only [mem_ofPred_eq,mem_inter_iff,s]
      by_cases hl : L (denseSeq ℝ≥0 n) p <;> simp [hl,hn]
    · simp only [hn,false_and,ofPred_false,MeasurableSet.empty]
  have hEnd : MeasurableSet {p : Y | L T p ∧ R T p ≤ a p} := by
    let s : Iic T := ⟨T,by simp⟩
    convert (hmL s).inter (measurableSet_le (hmR s) ha) using 1
    ext p
    simp only [mem_inter_iff,mem_ofPred_eq,s]
    by_cases hl : L T p <;> simp [hl]
  apply prefix_time_measurable τ T _ hmD _ hEnd ?_ hlt hle
  intro p
  rw [hcap p]
  apply iInf_congr
  intro n
  split_ifs <;> rfl

theorem actual_radius_prefix_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (T : ℝ≥0) :
    let mT := (borel ℂ).prod (Filtration.natural B (fun t => (hm t).stronglyMeasurable) T)
    @Measurable (ℂ × Ω) ℝ≥0∞ mT (borel ℝ≥0∞)
      (fun p => min (radiusLevelTime (γ p.2) (G p.2) p.1 u) (T : ℝ≥0∞)) ∧
    @MeasurableSet (ℂ × Ω) mT
      {p | radiusLevelTime (γ p.2) (G p.2) p.1 u ≤ (T : ℝ≥0∞)} := by
  classical
  obtain ⟨_,hR,hL⟩ := actual_spatial_past_kernels hm hc κ γ G F hw T
  let : MeasurableSpace Ω := Filtration.natural B (fun t => (hm t).stronglyMeasurable) T
  have htarget : Measurable (fun p : ℂ × Ω => (2*p.1.im)*Real.exp (-u)) :=
    (Complex.measurable_im.comp measurable_fst).const_mul 2 |>.mul_const _
  apply prefix_level_time_measurable
    (fun p : ℂ × Ω => radiusLevelTime (γ p.2) (G p.2) p.1 u) T
    (fun t p => fullRadius (G p.2) t p.1)
    (fun t p => p.1 ∈ survivingDomain (γ p.2) t)
    (fun p => (2*p.1.im)*Real.exp (-u)) hR hL htarget
  · intro p
    exact capped_radiusLevelTime_dense ((hc p.2).const_mul _) (hw p.2) p.1 u hu T
  · intro p
    simpa only [ENNReal.coe_lt_coe] using
      radiusLevelTime_lt_iff_dense ((hc p.2).const_mul _) (hw p.2) p.1 u hu (T : ℝ≥0∞)
  · intro p
    exact radiusLevelTime_le_iff_prefix ((hc p.2).const_mul _) (hw p.2) p.1 u hu T

namespace Multipoint

private lemma measurable_capped_green
    {Y : Type*} [MeasurableSpace Y] (τ : Y → ℝ≥0∞) (T : ℝ≥0)
    (g : Iic T × Y → ℝ)
    (hτ : Measurable (fun p => min (τ p) (T : ℝ≥0∞)))
    (hA : MeasurableSet {p | τ p ≤ (T : ℝ≥0∞)}) (hg : Measurable g) :
    Measurable (fun p => if τ p ≤ (T : ℝ≥0∞) then ENNReal.ofReal
      (g (⟨(min (τ p) (T : ℝ≥0∞)).toNNReal, by
        exact_mod_cast ENNReal.toNNReal_mono
          (by simp : (T : ℝ≥0∞) ≠ ∞) (min_le_right (τ p) (T : ℝ≥0∞))⟩,p)) else 0) := by
  classical
  have hb (p : Y) : (min (τ p) (T : ℝ≥0∞)).toNNReal ∈ Iic T := by
    exact_mod_cast ENNReal.toNNReal_mono
      (by simp : (T : ℝ≥0∞) ≠ ∞) (min_le_right (τ p) (T : ℝ≥0∞))
  have hm := (ENNReal.measurable_toNNReal.comp hτ).subtype_mk (h := hb)
  exact Measurable.ite hA (hg.comp (hm.prodMk measurable_id)).ennreal_ofReal measurable_const

lemma levelApproximationDensity_eq_cappedGreen
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (T : ℝ≥0) (ω : Ω) (z : ℂ) :
    levelApproximationDensity κ B γ G u T ω z =
      if radiusLevelTime (γ ω) (G ω) z u ≤ (T : ℝ≥0∞) then
        ENNReal.ofReal (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω)
          (min (radiusLevelTime (γ ω) (G ω) z u) (T : ℝ≥0∞)).toNNReal z) else 0 := by
  unfold levelApproximationDensity
  by_cases h : radiusLevelTime (γ ω) (G ω) z u ≤ (T : ℝ≥0∞)
  · have hf : radiusLevelTime (γ ω) (G ω) z u < ∞ := h.trans_lt (by simp)
    simp only [ite_eq_left h,min_eq_left h,stoppedGreen,ite_eq_left hf]
  · simp only [ite_eq_right h]

theorem levelApproximationDensity_past_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (T : ℝ≥0) :
    @Measurable (Ω × ℂ) ℝ≥0∞
      ((Filtration.natural B (fun t => (hm t).stronglyMeasurable) T).prod (borel ℂ))
      (borel ℝ≥0∞) (fun p => levelApproximationDensity κ B γ G u T p.1 p.2) := by
  classical
  obtain ⟨hρ,hA⟩ := actual_radius_prefix_measurable hm hc κ u hu γ G F hw T
  obtain ⟨hG,_,_⟩ := actual_spatial_past_kernels hm hc κ γ G F hw T
  let : MeasurableSpace Ω := Filtration.natural B (fun t => (hm t).stronglyMeasurable) T
  have hd := measurable_capped_green
    (fun p : ℂ × Ω => radiusLevelTime (γ p.2) (G p.2) p.1 u) T
    (fun p : Iic T × (ℂ × Ω) => greenDensity κ
      (fun s => Real.sqrt κ * B s p.2.2) (γ p.2.2) (G p.2.2) p.1 p.2.1) hρ hA hG
  simpa only [levelApproximationDensity_eq_cappedGreen,Function.comp_def,
    Prod.fst_swap,Prod.snd_swap] using
    hd.comp measurable_swap

lemma levelApproximationRealTest_past_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (T : ℝ≥0) (f : ℂ → ℝ) (hf : Measurable f) :
    Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) T]
      (levelApproximationRealTest κ B γ G u T f) := by
  have hd := levelApproximationDensity_past_measurable hm hc κ u hu γ G F hw T
  let : MeasurableSpace Ω := Filtration.natural B (fun t => (hm t).stronglyMeasurable) T
  have he (ω : Ω) : levelApproximationRealTest κ B γ G u T f ω =
      ∫ z, (levelApproximationDensity κ B γ G u T ω z).toReal * f z := by
    apply integral_withDensity_eq_integral_toReal_smul hd.of_uncurry_left
    filter_upwards [] with z
    unfold levelApproximationDensity
    split_ifs <;> simp
  simp_rw [show levelApproximationRealTest κ B γ G u T f =
    (fun ω => ∫ z, (levelApproximationDensity κ B γ G u T ω z).toReal * f z)
    from funext he]
  exact (hd.ennreal_toReal.mul (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

lemma convexLevelMeasure_test_past_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (n : ℕ) (T : ℝ≥0)
    (f : C_c(upperHalfPlane,ℝ)) :
    Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) T]
      (fun ω => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n T ω) := by
  have he (ω : Ω) := integral_convexLevelMeasure hκ hκ8 γ G F ω (hc ω) (hw ω)
    u s w n T (hw₀ n) f
  simp_rw [he]
  apply Finset.measurable_sum
  intro i hi
  exact measurable_const.mul (levelApproximationRealTest_past_measurable hm hc κ
    (u (n+i)) (hu (n+i)) γ G F hw T (extendHalfPlaneTest f)
    (extendHalfPlaneTest_measurable f f.continuous.measurable))

/-- Every actual vague limit at a fixed time has a version measurable in
that time's uncompleted natural filtration. The convex sequence is unchanged. -/
theorem level_radon_limit_has_past_measurable_version
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (T : ℝ≥0)
    (ν : Ω → Measure upperHalfPlane)
    (hν : ∀ᵐ ω ∂P, (ν ω).Regular)
    (hlim : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n T ω)
        atTop (𝓝 (∫ z, f z ∂ν ω))) :
    ∃ η : Ω → Measure upperHalfPlane,
      Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) T] η ∧
      (∀ ω, (η ω).Regular ∧ IsFiniteMeasureOnCompacts (η ω)) ∧ η =ᵐ[P] ν := by
  let : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace
  exact exists_subsigma_radon_version
    (Filtration.natural B (fun t => (hm t).stronglyMeasurable) T) P _ ν
    (fun n ω => convexLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hc ω) (hw ω)
      u s w n T)
    (fun n f => convexLevelMeasure_test_past_measurable hm hc hκ hκ8 γ G F hw
      u hu s w hw₀ n T f) hν hlim

end Multipoint
end SLEExactGauge

end

end OAI
