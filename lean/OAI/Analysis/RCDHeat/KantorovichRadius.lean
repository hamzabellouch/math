import Mathlib
import OAI.Analysis.RCDHeat.EntropyWassersteinGeodesic
import OAI.Analysis.RCDHeat.CompactKantorovich

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: KantorovichRadius, KantorovichLeftLimit, KantorovichRelaxed, KantorovichGradient, KantorovichIdentity. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [ProperSpace X]

 

omit [ProperSpace X] in
 theorem hopf_minimizer_distance_mono {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) {x y z : X}
    (hy : y ∈ hopfMinimizers f s x) (hz : z ∈ hopfMinimizers f t x) :
    dist x y ≤ dist x z := by
  have ht : 0 < t := hs.trans hst
  have ha := hopfLax_le_cost hf hs x z
  have hb := hopfLax_le_cost hf ht x y
  change hopfLax f s x = f y+dist x y^2/(2*s) at hy
  change hopfLax f t x = f z+dist x z^2/(2*t) at hz
  rw [hy] at ha
  rw [hz] at hb
  have hdenS : 0 < 2*s := by positivity
  have hdenT : 0 < 2*t := by positivity
  have has : (dist x y^2-dist x z^2)/(2*s) ≤ f z-f y := by
    rw [sub_div]
    linarith
  have hbt : (dist x z^2-dist x y^2)/(2*t) ≤ f y-f z := by
    rw [sub_div]
    linarith
  have ha' := (div_le_iff₀ hdenS).mp has
  have hb' := (div_le_iff₀ hdenT).mp hbt
  have hmul : (t-s)*(dist x y^2-dist x z^2) ≤ 0 := by
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hb'),mul_nonneg ht.le (sub_nonneg.mpr ha')]
  have hsquare : dist x y^2 ≤ dist x z^2 := by nlinarith [sub_pos.mpr hst]
  nlinarith [dist_nonneg (x := x) (y := y),dist_nonneg (x := x) (y := z)]

 theorem hopfRadius_le_later_minimizer {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) {x z : X}
    (hz : z ∈ hopfMinimizers f t x) : hopfRadius f s x ≤ dist x z := by
  obtain ⟨y,hy,he⟩ := hopfRadius_attained hf hs x
  rw [he]
  exact hopf_minimizer_distance_mono hf hs hst hy hz

 theorem hopfRadius_monotone_time {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : X) :
    MonotoneOn (fun t => hopfRadius f t x) (Ioi (0:ℝ)) := by
  intro s hs t ht hst
  rcases eq_or_lt_of_le hst with rfl | hst
  · rfl
  obtain ⟨z,hz,he⟩ := hopfRadius_attained hf ht x
  change hopfRadius f s x ≤ hopfRadius f t x
  rw [he]
  exact hopfRadius_le_later_minimizer hf hs hst hz

variable [MeasurableSpace X] [BorelSpace X]
 theorem hopfRadius_measurable {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {t : ℝ} (ht : 0 < t) : Measurable (hopfRadius f t) := by
  apply UpperSemicontinuous.measurable
  rw [upperSemicontinuous_iff]
  intro x
  rw [upperSemicontinuousAt_iff]
  intro a ha
  obtain ⟨δ,hδ,hh⟩ := hopfRadius_upperSemicontinuous hf ht x (a-hopfRadius f t x) (sub_pos.mpr ha)
  filter_upwards [ball_mem_nhds x hδ] with z hz
  simpa only [add_sub_cancel] using hh z hz
end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable def hopfLeftTime (n : ℕ) : ℝ := 1-1/(n+2:ℝ)
 theorem hopfLeftTime_bounds (n : ℕ) : 1/2 ≤ hopfLeftTime n ∧ hopfLeftTime n < 1 := by
  have hn : (2:ℝ) ≤ n+2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hi : 1/(n+2:ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hn
  have hp : 0 < 1/(n+2:ℝ) := by positivity
  dsimp [hopfLeftTime]
  constructor <;> linarith
 theorem hopfLeftTime_pos (n : ℕ) : 0 < hopfLeftTime n := lt_of_lt_of_le (by norm_num) (hopfLeftTime_bounds n).1
 theorem hopfLeftTime_mono : Monotone hopfLeftTime := by
  intro n m hnm
  have hn : 0 < (n:ℝ)+2 := by positivity
  have hh : (n:ℝ)+2 ≤ m+2 := by exact_mod_cast Nat.add_le_add_right hnm 2
  exact sub_le_sub_left (one_div_le_one_div_of_le hn hh) _
 theorem hopfLeftTime_tendsto : Tendsto hopfLeftTime atTop (𝓝 (1:ℝ)) := by
  have hh : Tendsto (fun n : ℕ => 1/((n+1:ℕ)+1:ℝ)) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  have he : (fun n : ℕ => 1/((n+1:ℕ)+1:ℝ)) = (fun n : ℕ => 1/(n+2:ℝ)) := by
    funext n
    simp only [Nat.cast_add,Nat.cast_one]
    congr 1
    ring
  rw [he] at hh
  change Tendsto (fun n : ℕ => 1-1/(n+2:ℝ)) atTop (𝓝 (1:ℝ))
  simpa only [sub_zero] using tendsto_const_nhds.sub hh

variable {X : Type*} [MetricSpace X] [ProperSpace X]
noncomputable def hopfLeftRadius (f : X → ℝ) (x : X) : ℝ :=
  ⨆ n : ℕ, hopfRadius f (hopfLeftTime n) x

 theorem hopfLeftRadius_bdd {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hgeo : IsGeodesicSpace X) (x : X) :
    BddAbove (range (fun n => hopfRadius f (hopfLeftTime n) x)) := by
  refine ⟨(L:ℝ),?_⟩
  rintro _ ⟨n,rfl⟩
  exact (hopfRadius_le_sharp hf hgeo (hopfLeftTime_pos n) x).trans
    (mul_le_of_le_one_left L.coe_nonneg (hopfLeftTime_bounds n).2.le)

 theorem hopfLeftRadius_bounds {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hgeo : IsGeodesicSpace X) (x : X) : 0 ≤ hopfLeftRadius f x ∧ hopfLeftRadius f x ≤ L := by
  constructor
  · exact (hopfRadius_bounds hf (hopfLeftTime_pos 0) x).1.trans
      (le_ciSup (hopfLeftRadius_bdd hf hgeo x) 0)
  · apply ciSup_le
    intro n
    exact (hopfRadius_le_sharp hf hgeo (hopfLeftTime_pos n) x).trans
      (mul_le_of_le_one_left L.coe_nonneg (hopfLeftTime_bounds n).2.le)

 theorem hopfLeftRadius_tendsto {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hgeo : IsGeodesicSpace X) (x : X) :
    Tendsto (fun n => hopfRadius f (hopfLeftTime n) x) atTop (𝓝 (hopfLeftRadius f x)) := by
  apply tendsto_atTop_ciSup _ (hopfLeftRadius_bdd hf hgeo x)
  intro n m hnm
  exact hopfRadius_monotone_time hf x (hopfLeftTime_pos n) (hopfLeftTime_pos m) (hopfLeftTime_mono hnm)

 theorem hopfLeftRadius_le_minimizer {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    {x y : X} (hy : y ∈ hopfMinimizers f 1 x) : hopfLeftRadius f x ≤ dist x y := by
  apply ciSup_le
  intro n
  exact hopfRadius_le_later_minimizer hf (hopfLeftTime_pos n) (hopfLeftTime_bounds n).2 hy

variable [MeasurableSpace X] [BorelSpace X]
 theorem hopfLeftRadius_measurable {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Measurable (hopfLeftRadius f) := by
  exact Measurable.iSup (fun n => hopfRadius_measurable hf (hopfLeftTime_pos n))
end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hgeo : IsGeodesicSpace X)
include hf hgeo

 theorem hopfLeftRadius_memLp : MemLp (hopfLeftRadius f) 2 μ :=
  memLp_of_bounded (Eventually.of_forall (hopfLeftRadius_bounds hf hgeo))
    (hopfLeftRadius_measurable hf).aestronglyMeasurable 2

omit [MeasurableSpace X] [BorelSpace X] in
 theorem hopfScaledRadius_bounds (n : ℕ) (x : X) :
    0 ≤ hopfRadius f (hopfLeftTime n) x/hopfLeftTime n ∧
    hopfRadius f (hopfLeftTime n) x/hopfLeftTime n ≤ L := by
  constructor
  · exact div_nonneg (hopfRadius_bounds hf (hopfLeftTime_pos n) x).1 (hopfLeftTime_pos n).le
  · exact (div_le_iff₀ (hopfLeftTime_pos n)).mpr (by
      simpa only [mul_comm] using hopfRadius_le_sharp hf hgeo (hopfLeftTime_pos n) x)

 theorem hopfScaledRadius_memLp (n : ℕ) :
    MemLp (fun x => hopfRadius f (hopfLeftTime n) x/hopfLeftTime n) 2 μ :=
  memLp_of_bounded (Eventually.of_forall (hopfScaledRadius_bounds hf hgeo n))
    ((hopfRadius_measurable hf (hopfLeftTime_pos n)).div_const _).aestronglyMeasurable 2

 theorem hopfScaledRadius_toLp_tendsto :
    Tendsto (fun n => (hopfScaledRadius_memLp μ hf hgeo n).toLp
      (fun x => hopfRadius f (hopfLeftTime n) x/hopfLeftTime n)) atTop
      (𝓝 ((hopfLeftRadius_memLp μ hf hgeo).toLp (hopfLeftRadius f))) := by
  apply L2Differentiation.toLp_tendsto_of_dominated μ _ _ (fun _ => (L:ℝ)^2) (integrable_const _)
  · exact Eventually.of_forall (fun n => Eventually.of_forall fun x => by
      have ha := hopfScaledRadius_bounds hf hgeo n x
      have hb := hopfLeftRadius_bounds hf hgeo x
      nlinarith [sq_nonneg ((hopfRadius f (hopfLeftTime n) x/hopfLeftTime n)-hopfLeftRadius f x)])
  · exact Eventually.of_forall (fun x => by
      have hh := (hopfLeftRadius_tendsto hf hgeo x).div hopfLeftTime_tendsto
        (show (1:ℝ) ≠ 0 by norm_num)
      change Tendsto (fun n => hopfRadius f (hopfLeftTime n) x/hopfLeftTime n) atTop
        (𝓝 (hopfLeftRadius f x/1)) at hh
      simpa only [div_one] using hh)

 theorem hopfLeft_toLp_tendsto :
    Tendsto (fun n => ((hopfLax_continuous hf (hopfLeftTime_pos n)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (p := 2) (μ := μ)).toLp (hopfLax f (hopfLeftTime n))) atTop
      (𝓝 (((hopfLax_continuous hf (show (0:ℝ) < 1 by norm_num)).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _) (p := 2) (μ := μ)).toLp (hopfLax f 1))) := by
  have hb (n : ℕ) (x : X) : |hopfLax f (hopfLeftTime n) x-hopfLax f 1 x| ≤ (L:ℝ)^2 := by
    have hh := hopfLax_time_difference_sharp hf hgeo (show (0:ℝ) < 1 by norm_num) (hopfLeftTime_pos n) x
    have ht := hopfLeftTime_bounds n
    rw [abs_of_nonpos (by linarith : hopfLeftTime n-1 ≤ 0)] at hh
    have hmul := mul_le_mul_of_nonneg_left (show -(hopfLeftTime n-1) ≤ 1 by linarith) (sq_nonneg (L:ℝ))
    nlinarith
  apply L2Differentiation.toLp_tendsto_of_dominated μ _ _ (fun _ => ((L:ℝ)^2)^2) (integrable_const _)
  · exact Eventually.of_forall (fun n => Eventually.of_forall fun x => by
      have hh := hb n x
      have hs := (sq_le_sq₀ (abs_nonneg _) (sq_nonneg _)).mpr hh
      simpa only [sq_abs] using hs)
  · refine Eventually.of_forall fun x => ?_
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hzero : Tendsto (fun n => (L:ℝ)^2/2*|hopfLeftTime n-1|) atTop (𝓝 (0:ℝ)) := by
      simpa only [Pi.mul_apply,Pi.sub_apply,sub_self,abs_zero,mul_zero] using
        ((tendsto_const_nhds (x := (L:ℝ)^2/2)).mul
          ((hopfLeftTime_tendsto.sub (tendsto_const_nhds (x := (1:ℝ)))).abs))
    apply squeeze_zero (fun _ => dist_nonneg) _ hzero
    intro n
    simpa only [Real.dist_eq] using
      hopfLax_time_difference_sharp hf hgeo (show (0:ℝ) < 1 by norm_num) (hopfLeftTime_pos n) x

 

 theorem hopfLeftRadius_isRelaxed :
    IsRelaxedSlope μ
      (((hopfLax_continuous hf (show (0:ℝ) < 1 by norm_num)).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _) (p := 2) (μ := μ)).toLp (hopfLax f 1))
      ((hopfLeftRadius_memLp μ hf hgeo).toLp (hopfLeftRadius f)) := by
  refine ⟨fun n => ((hopfLax_continuous hf (hopfLeftTime_pos n)).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (p := 2) (μ := μ)).toLp (hopfLax f (hopfLeftTime n)),
    fun n => hopfLax f (hopfLeftTime n),
    fun n => (hopfScaledRadius_memLp μ hf hgeo n).toLp
      (fun x => hopfRadius f (hopfLeftTime n) x/hopfLeftTime n),
    fun n => ⟨L,hopfLax_lipschitz hf hgeo (hopfLeftTime_pos n)⟩,?_,?_,
    hopfLeft_toLp_tendsto μ hf hgeo,hopfScaledRadius_toLp_tendsto μ hf hgeo⟩
  · intro n
    exact MemLp.coeFn_toLp _
  · intro n
    filter_upwards [(hopfScaledRadius_memLp μ hf hgeo n).coeFn_toLp] with x hx
    rw [hx]
    exact ⟨(hopfScaledRadius_bounds hf hgeo n x).1,hopfLax_slope_le hf (hopfLeftTime_pos n) x⟩
end

 
section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
  (hQ : QuadraticCheegerEnergy μ)

 theorem hopfLeftRadius_minimalSlope_bound {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hgeo : IsGeodesicSpace X) :
    ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ
      (SobolevSpace.ofLipschitzCompact μ hQ
        (hopfLax_lipschitz hf hgeo (show (0:ℝ) < 1 by norm_num))
        (HasCompactSupport.of_compactSpace _)) x ≤ hopfLeftRadius f x := by
  let u := SobolevSpace.ofLipschitzCompact μ hQ
    (hopfLax_lipschitz hf hgeo (show (0:ℝ) < 1 by norm_num))
    (HasCompactSupport.of_compactSpace _)
  have he : SobolevSpace.toLp μ hQ u =
      ((hopfLax_continuous hf (show (0:ℝ) < 1 by norm_num)).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _) (p := 2) (μ := μ)).toLp (hopfLax f 1) := by
    apply Lp.ext
    exact (SobolevSpace.ofLipschitzCompact_coe μ hQ _ _).trans (MemLp.coeFn_toLp _).symm
  have hr := hopfLeftRadius_isRelaxed μ hf hgeo
  rw [←he] at hr
  have hle := (Lp.coeFn_le _ _).mpr (SobolevSpace.minimalSlope_le μ hQ u hr)
  filter_upwards [hle,(hopfLeftRadius_memLp μ hf hgeo).coeFn_toLp] with x hx heq
  exact hx.trans_eq heq

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
 theorem hopfLax_of_contact {φ ψ : X → ℝ} {L : ℝ≥0} (hψ : LipschitzWith L ψ)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2) {x y : X}
    (hc : φ x+ψ y = dist x y^2/2) :
    hopfLax (-ψ) 1 x = φ x ∧ y ∈ hopfMinimizers (-ψ) 1 x := by
  have hupper := hopfLax_le_cost hψ.neg (show (0:ℝ) < 1 by norm_num) x y
  simp only [Pi.neg_apply,mul_one] at hupper
  have hlower : φ x ≤ hopfLax (-ψ) 1 x := by
    apply le_csInf ⟨_,mem_range_self x⟩
    rintro _ ⟨z,rfl⟩
    have hh := had x z
    simp only [Pi.neg_apply,mul_one]
    linarith
  have he : hopfLax (-ψ) 1 x = φ x := by linarith
  refine ⟨he,?_⟩
  change hopfLax (-ψ) 1 x = -ψ y+dist x y^2/(2*1)
  rw [he]
  linarith

 

 theorem IsOptimalCoupling.compact_sobolev_potential
    (hgeo : IsGeodesicSpace X) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁] (hac : ν₀ ≪ μ)
    {π : Measure (X×X)} (hp : IsOptimalCoupling ν₀ ν₁ π) :
    ∃ (u : SobolevSpace μ hQ) (φ ψ : X → ℝ) (L : ℝ≥0),
      LipschitzWith L φ ∧ LipschitzWith L ψ ∧
      (φ =ᵐ[μ] SobolevSpace.toLp μ hQ u) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ xy ∂π, φ xy.1+ψ xy.2 = dist xy.1 xy.2^2/2) ∧
      (∀ᵐ xy ∂π, SobolevSpace.minimalSlope μ hQ u xy.1 ≤ dist xy.1 xy.2) := by
  obtain ⟨φ,ψ,⟨L,hφ,hψ⟩,had,hc⟩ := hp.compact_potentials ν₀ ν₁
  let f : X → ℝ := -ψ
  have hf : LipschitzWith L f := hψ.neg
  have hLip := hopfLax_lipschitz hf hgeo (show (0:ℝ) < 1 by norm_num)
  let u := SobolevSpace.ofLipschitzCompact μ hQ hLip (HasCompactSupport.of_compactSpace _)
  refine ⟨u,hopfLax f 1,ψ,L,hLip,hψ,
    (SobolevSpace.ofLipschitzCompact_coe μ hQ hLip (HasCompactSupport.of_compactSpace _)).symm,
    ?_,?_,?_⟩
  · intro x y
    have hh := hopfLax_le_cost hf (show (0:ℝ) < 1 by norm_num) x y
    change hopfLax f 1 x ≤ -ψ y+dist x y^2/(2*1) at hh
    linarith
  · filter_upwards [hc] with xy hxy
    have he := (hopfLax_of_contact hψ had hxy).1
    change hopfLax (-⇑ψ) 1 xy.1+ψ xy.2 = _
    rw [he]
    exact hxy
  · have hbound := (hopfLeftRadius_minimalSlope_bound μ hQ hf hgeo).filter_mono hac.ae_le
    rw [←hp.1] at hbound
    have hb := ae_of_ae_map measurable_fst.aemeasurable hbound
    filter_upwards [hb,hc] with xy hh hxy
    exact hh.trans (hopfLeftRadius_le_minimizer hf (hopfLax_of_contact hψ had hxy).2)
end

 
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

 theorem IsRelaxedSlope.kantorovich_gradient_eq_displacement (μ : Measure X)
    [ProperSpace X] [μ.Regular] (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G)
    {φ ψ : X → ℝ} (hu : φ =ᵐ[μ] u)
    (had : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2)
    (hb : ∀ᵐ γ ∂π, G (γ 0) ≤ dist (γ 0) (γ 1)) :
    ∀ᵐ γ ∂π, G (γ 0) = dist (γ 0) (γ 1) := by
  have hnn : ∀ᵐ γ ∂π, 0 ≤ G (γ 0) :=
    ae_of_ae_map (measurable_path_eval 0).aemeasurable
      (((Lp.coeFn_nonneg G).mpr (hG.nonneg μ)).filter_mono
        (Measure.absolutelyContinuous_of_le_smul (hcomp 0)).ae_le)
  have hiG : MemLp (fun γ : C(Time,X) => G (γ 0)) 2 π :=
    compressionPullback_memLp μ π _ (measurable_path_eval 0) hC (hcomp 0) G
  have hiD2 := (memLp_two_iff_integrable_sq hD.aestronglyMeasurable).mp hD
  have hiG2 := (memLp_two_iff_integrable_sq hiG.aestronglyMeasurable).mp hiG
  have hle := hG.kantorovich_action_le_gradient_square μ π hgeo hC hcomp hD hu had hcontact
  have hs : ∀ᵐ γ ∂π, 0 ≤ dist (γ 0) (γ 1)^2-G (γ 0)^2 := by
    filter_upwards [hb,hnn] with γ hb hn
    exact sub_nonneg.mpr (sq_le_sq₀ hn dist_nonneg |>.mpr hb)
  have hz : (∫γ : C(Time,X),dist (γ 0) (γ 1)^2-G (γ 0)^2 ∂π) = 0 := by
    apply le_antisymm _ (integral_nonneg_of_ae hs)
    rw [integral_sub hiD2 hiG2]
    linarith
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hs (hiD2.sub hiG2)).mp hz,hnn]
    with γ hγ hn
  change dist (γ 0) (γ 1)^2-G (γ 0)^2 = 0 at hγ
  exact (sq_eq_sq₀ hn dist_nonneg).mp (by linarith)

 

 theorem compact_optimal_plan_gradient_identity [CompactSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (hspace : IsGeodesicSpace X) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ) :
    ∃ (u : SobolevSpace μ hQ) (φ ψ : X → ℝ) (L : ℝ≥0),
      LipschitzWith L φ ∧ LipschitzWith L ψ ∧
      (φ =ᵐ[μ] SobolevSpace.toLp μ hQ u) ∧
      (∀ x y, φ x+ψ y ≤ dist x y^2/2) ∧
      (∀ᵐ γ ∂π, φ (γ 0)+ψ (γ 1) = dist (γ 0) (γ 1)^2/2) ∧
      (∀ᵐ γ ∂π, SobolevSpace.minimalSlope μ hQ u (γ 0) = dist (γ 0) (γ 1)) := by
  have hac : ν₀ ≪ μ := by
    rw [←(optimalPlan_endpoints ν₀ ν₁ π hp).1]
    exact Measure.absolutelyContinuous_of_le_smul (hcomp 0)
  obtain ⟨u,φ,ψ,L,hφ,hψ,hu,had,hc,hb⟩ := hp.compact_sobolev_potential μ hQ hspace ν₀ ν₁ hac
  have hm := (measurable_path_eval (X := X) 0).prodMk (measurable_path_eval 1)
  have hc' := ae_of_ae_map hm.aemeasurable hc
  have hb' := ae_of_ae_map hm.aemeasurable hb
  have hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π := by
    have hd := ((continuous_fst.dist continuous_snd : Continuous (fun xy : X×X => dist xy.1 xy.2)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (p := 2) (μ := π.map (fun γ => (γ 0,γ 1))))
    exact hd.comp_of_map hm.aemeasurable
  exact ⟨u,φ,ψ,L,hφ,hψ,hu,had,hc',
    (SobolevSpace.minimalSlope_isRelaxed μ hQ u).kantorovich_gradient_eq_displacement
      μ π hgeo hC hcomp hD hu had hc' hb'⟩

end RegularPointCoordinates

end OAI
