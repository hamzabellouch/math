import Mathlib
import OAI.Probability.SLE.FiniteMass
import OAI.Probability.SLE.WindowPropagation

namespace OAI

/-! Retained Seed Moments for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
lemma source_unit_ball_height {z₀ z : ℂ} (hz₀ : 2 < z₀.im) (hz : z ∈ closedBall z₀ 1) :
    1 < z.im := by
  have hdist : abs (z.im-z₀.im) ≤ dist z z₀ := by
    simpa only [dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (z-z₀)
  have hh : dist z z₀ ≤ 1 := hz
  have ha := neg_abs_le (z.im-z₀.im)
  linarith

lemma source_open_closed_ball_ae (z₀ : ℂ) :
    closedBall z₀ 1 =ᵐ[volume] ball z₀ 1 := by
  have he : ∀ᵐ z : ℂ ∂volume, z ∉ sphere z₀ 1 := by
    rw [ae_iff]
    simpa [Metric.sphere, dist_eq_norm] using Measure.addHaar_sphere volume z₀ (1:ℝ)
  filter_upwards [he] with z hz
  apply propext
  change dist z z₀ ≤ 1 ↔ dist z z₀ < 1
  change dist z z₀ ≠ 1 at hz
  exact le_iff_lt_or_eq.trans (or_iff_left hz)

lemma source_finite_mass_le_unit_mass {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z₀ : ℂ) (hz : 2 < z₀.im) (rf : ℝ) (hf : 0 < rf) (hf1 : rf ≤ 1)
    (T : ℝ≥0) (ω : a.samples) :
    finiteSpatialGreenMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf T (closedBall z₀ 1) ≤
      ENNReal.ofReal (spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1)) := by
  have hi := a.spatialGreenWeight_spatial_integrable hκ hκ8 rf hf
    (ball z₀ 1) measurableSet_ball (measure_ball_lt_top (μ := volume) (x := z₀) (r := 1)).ne
    (fun z hz' => hf1.trans (source_unit_ball_height hz (ball_subset_closedBall hz')).le) ω
  rw [spatialRealMass,ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun z => by
    dsimp [spatialGreenWeight]; split_ifs
    · exact le_rfl
    · exact greenDensity_nonneg (a.witness ω) κ _ z))]
  rw [finiteSpatialGreenMass,Measure.restrict_congr_set (source_open_closed_ball_ae z₀)]
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  split_ifs
  · exact le_rfl
  · dsimp [spatialGreenWeight]; split_ifs
    · exact le_rfl
    · exact greenDensity_nonneg (a.witness ω) κ _ z

lemma source_unit_mesh_second_moment (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8) :
    ∃ d : ℝ, 0 < d ∧ d < 1 ∧
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ), 2 < z₀.im →
    ∃ m₂ : ℝ, 0 < m₂ ∧ ∀ rf : ℝ, 0 < rf → rf ≤ d →
      (∫⁻ ω : a.samples, ENNReal.ofReal (spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
        (γ ω) (a.G ω) rf (ball z₀ 1))^2 ∂(P.comap Subtype.val)) ≤ ENNReal.ofReal m₂ := by
  obtain ⟨C,c,d,hC,hc,hd,hd1,ht⟩ := source_initial_unit_mesh_tail κ hκ hκ8
  refine ⟨d,hd,hd1,?_⟩
  intro Ω m P hP γ a z₀ hz
  let : IsProbabilityMeasure P := hP
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let v := (volume (ball z₀ 1)).toReal
  let M := max C v*d^(-codimension κ)
  let b := c*d^(-2:ℝ)
  let A := max 1 C*Real.exp b
  let α := b/M
  have hk : 0 < κ := by linarith
  have hp : 0 < codimension κ := codimension_pos κ hκ8
  have hp1 : codimension κ < 1 := by dsimp [codimension, dimension]; linarith
  have hM : 0 < M := mul_pos (hC.trans_le (le_max_left _ _)) (Real.rpow_pos_of_pos hd _)
  have hb : 0 < b := mul_pos hc (Real.rpow_pos_of_pos hd _)
  have hA : 0 < A := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (Real.exp_pos _)
  have hα : 0 < α := div_pos hb hM
  refine ⟨8*A/α^2,by positivity,?_⟩
  intro rf hf hfd
  let X := fun ω : a.samples => spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) rf (ball z₀ 1)
  have hx (ω : a.samples) : 0 ≤ X ω ∧ X ω ≤ v*rf^(-codimension κ) :=
    a.spatialRealMass_bound hk hκ8 rf hf (ball z₀ 1) measurableSet_ball
      (measure_ball_lt_top (μ := volume) (x := z₀) (r := 1)).ne
      (fun z hz' => (hfd.trans hd1.le).trans (source_unit_ball_height hz (ball_subset_closedBall hz')).le) ω
  have hlinear : ∀ t : ℝ, 1 ≤ t → μ {ω | M*t < X ω} ≤ ENNReal.ofReal (C*Real.exp (-b*t)) :=
    source_mesh_tail_to_linear μ X (codimension κ) C c d v rf hp hp1.le hC hc hd
      ENNReal.toReal_nonneg hf (fun ω => (hx ω).2)
      (fun δ hfd hd' => ht Ω m P hP γ a z₀ hz rf δ hf hfd hd')
  exact source_exponential_second_moment μ X (a.spatialRealMass_measurable _ _) (fun ω => (hx ω).1)
    A α hA.le hα (source_linear_tail_all X M C b hM hC hb hlinear)
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

def SourceRetainedSeedTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
    (z₀ : ℂ), 2 < z₀.im →
  ∃ (T : ℝ≥0) (e₀ m₀ m₂ : ℝ),
    0 < T ∧ 0 < e₀ ∧ 0 < m₀ ∧ 0 < m₂ ∧
    ∀ r : ℝ, 0 < r → r ≤ e₀ →
      let X := fun ω : a.samples => finiteSpatialGreenMass κ
        (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r T (closedBall z₀ 1)
      ENNReal.ofReal m₀ ≤ ∫⁻ ω, X ω ∂(P.comap Subtype.val) ∧
      (∫⁻ ω, (X ω)^2 ∂(P.comap Subtype.val)) ≤ ENNReal.ofReal m₂
theorem sourceRetainedSeed_proved : SourceRetainedSeedTarget := by
  intro κ hκ hκ8 Ω m P hP γ a z₀ hz
  let : IsProbabilityMeasure P := hP
  have hk : 0 < κ := by linarith
  have hK : closedBall z₀ 1 ⊆ upperHalfPlane :=
    fun z hz' => zero_lt_one.trans (source_unit_ball_height hz hz')
  obtain ⟨T,e₀,m₀,hT,he,hm,hfirst⟩ := a.source_finite_time_first_moment hk hκ8 z₀ 1 (by norm_num) hK
  obtain ⟨d,hd,hd1,hsecond⟩ := source_unit_mesh_second_moment κ hκ hκ8
  obtain ⟨m₂,hm₂,hsecond⟩ := hsecond Ω m P hP γ a z₀ hz
  refine ⟨T,min e₀ d,m₀,m₂,hT,lt_min he hd,hm,hm₂,?_⟩
  intro r hr hre
  refine ⟨hfirst r hr (hre.trans (min_le_left _ _)),?_⟩
  have hrd : r ≤ d := hre.trans (min_le_right _ _)
  apply le_trans (lintegral_mono (fun ω => pow_le_pow_left' (source_finite_mass_le_unit_mass
    a hk hκ8 z₀ hz r hr (hrd.trans hd1.le) T ω) 2))
  exact hsecond r hr hrd
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
lemma source_first_sphere_free {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hy : r ≤ z.im) (hs : r ≤ dist (γ 0) z)
    (s : ℝ≥0) (hfirst : spatialHitTime γ z r = s) :
    ball z r ⊆ upperHalfPlane \ (γ '' Icc 0 s) := by
  intro w hw
  refine ⟨ball_subset_upperHalfPlane hy hw,?_⟩
  rintro ⟨u,hu,rfl⟩
  have hh := spatialHitTime_lt_of_dist_lt hc z r hs u hw
  rw [hfirst] at hh
  exact (not_lt_of_ge hu.2) (WithTop.coe_lt_coe.mp hh)

lemma source_live_hit_spatial_eq {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hs : r ≤ dist (γ 0) z)
    (s : ℝ≥0) (hh : liveSpatialHitTime γ z r = s) :
    spatialHitTime γ z r = s := by
  rw [liveSpatialHitTime_eq hc z r hs] at hh
  split_ifs at hh with ht hl
  · exact (WithTop.coe_ne_top hh.symm).elim
  · exact hh
  · exact (WithTop.coe_ne_top hh.symm).elim

lemma source_live_collar_free {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (hy : 4 ≤ z.im) (hs : 3 ≤ dist (γ 0) z)
    (s : ℝ≥0) (hh : liveSpatialHitTime γ z 3 = s) :
    closedBall z 2 ⊆ survivingDomain γ s := by
  have hm := source_liveHit_mem hc z 3 hs s hh
  have hball := ball_subset_survivingDomain (by norm_num : (0:ℝ)<3) hm.1
    (source_first_sphere_free hc z 3 (by linarith) hs s
      (source_live_hit_spatial_eq hc z 3 hs s hh))
  exact fun w hw => hball (by change dist w z < 3; have : dist w z ≤ 2 := hw; linarith)

lemma source_enter_implies_live_contact {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    {G F : ℝ≥0 → ℂ → ℂ} (h : IsCapacityTwoWitness U γ G F)
    (z : ℂ) (hy : 4 ≤ z.im) (t : ℝ≥0) (ht : dist (γ t) z < 3) :
    liveSpatialHitTime γ z 3 ≠ ⊤ := by
  have hs : 3 ≤ dist (γ 0) z := by
    rw [h.2.1,dist_zero_left]
    have := (le_abs_self z.im).trans (Complex.abs_im_le_norm z)
    linarith
  have hh := spatialHitTime_lt_of_dist_lt h.1 z 3 hs t ht
  have hn : spatialHitTime γ z 3 ≠ ⊤ := ne_of_lt (hh.trans_le le_top)
  obtain ⟨s,he⟩ := WithTop.ne_top_iff_exists.mp hn
  have hst : s ≤ t := (WithTop.coe_lt_coe.mp (he ▸ hh)).le
  have hfree := source_first_sphere_free h.1 z 3 (by linarith) hs s he.symm
  have hl := h.surviving_of_free_ball_future_tip s t hst z 3 (by norm_num) hfree ht
  have hm := spatialHitTime_mem h.1 z 3 s he.symm
  exact ne_of_lt ((source_liveHit_le γ z 3 s hl hm.le).trans_lt (WithTop.coe_lt_top s))

lemma source_weight_zero_no_unit_entrance {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    {G F : ℝ≥0 → ℂ → ℂ} (h : IsCapacityTwoWitness U γ G F)
    (κ : ℝ) (z₀ : ℂ) (hy : 4 ≤ z₀.im) (rf : ℝ) (hf1 : rf ≤ 1)
    (hn : liveSpatialHitTime γ z₀ 3 = ⊤) (z : ℂ) (hz : z ∈ ball z₀ 1) :
    spatialGreenWeight κ U γ G z rf = 0 := by
  unfold spatialGreenWeight
  split_ifs with hb
  · rfl
  · have hn' : spatialHitTime γ z rf ≠ ⊤ := fun hh => hb hh
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn'
    have hm := spatialHitTime_mem h.1 z rf t ht.symm
    have hd : dist (γ t) z₀ < 3 := by
      have hz' : dist z z₀ < 1 := hz
      have hh := dist_triangle (γ t) z z₀
      linarith
    exact (source_enter_implies_live_contact h z₀ hy t hd hn).elim
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
lemma source_event_bound_from_past {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ) (A E : Set Ω)
    (hA : MeasurableSet[m] A) (hE : MeasurableSet E) (hEA : E ⊆ A)
    (K : ℝ) (hK : 0 ≤ K)
    (ht : ∀ᵐ ω ∂μ, ω ∈ A → μ[(fun ω => if ω ∈ E then (1:ℝ) else 0) | m] ω ≤ K) :
    μ E ≤ ENNReal.ofReal (μ.real A*K) := by
  have hi : Integrable (fun ω => if ω ∈ E then (1:ℝ) else 0) μ :=
    (integrable_const (1:ℝ)).indicator hE
  have hb := setIntegral_mono_ae_restrict (s := A) integrable_condExp.integrableOn
    (integrable_const K).integrableOn ((ae_restrict_iff' (hm _ hA)).mpr ht)
  rw [setIntegral_condExp hm hi hA] at hb
  change (∫ ω in A, E.indicator (fun _ => (1:ℝ)) ω ∂μ) ≤ _ at hb
  rw [setIntegral_indicator hE,inter_eq_right.mpr hEA,setIntegral_const,setIntegral_const] at hb
  simp only [smul_eq_mul,mul_one] at hb
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (mul_nonneg ENNReal.toReal_nonneg hK)).mpr hb

lemma source_live_unit_mesh_tail (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8) :
    ∃ C c δ₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ₀ ∧ δ₀ < 1 ∧
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ), 4 ≤ z₀.im →
    ∀ (rf δ : ℝ), 0 < rf → rf ≤ δ → δ ≤ δ₀ →
      (P.comap Subtype.val) {ω : a.samples | C*δ^(-codimension κ) <
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1)} ≤
      ENNReal.ofReal ((P.comap Subtype.val).real {ω : a.samples | liveSpatialHitTime (γ ω) z₀ 3 ≠ ⊤} *
        (C*Real.exp (-c*δ^(-2:ℝ)))) := by
  obtain ⟨C,c,δ₀,hC,hc,hδ,hδ1,ht⟩ := sourcePhysicalMeshTail_proved κ hκ hκ8 1 (by norm_num)
  refine ⟨C,c,δ₀,hC,hc,hδ,hδ1,?_⟩
  intro Ω m P hP γ a z₀ hz rf δ hf hfd hd
  let : IsProbabilityMeasure P := hP
  let ρ := fun ω : a.samples => liveSpatialHitTime (γ ω) z₀ 3
  have hρ : IsStoppingTime a.filtration ρ := source_liveHit_stopping a z₀ 3 (by linarith)
  let A := {ω : a.samples | ρ ω ≠ ⊤}
  have hA : MeasurableSet[hρ.measurableSpace] A := (measurableSet_eq_fun hρ.measurable measurable_const).compl
  apply source_event_bound_from_past hρ.measurableSpace_le A _ hA
    (measurableSet_lt measurable_const (a.spatialRealMass_measurable _ _))
  · intro ω hω
    by_contra hn
    have htop : liveSpatialHitTime (γ ω) z₀ 3 = ⊤ := by simpa only [A,ρ,mem_ofPred_eq,not_not] using hn
    have hzX : spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro z hz'
      exact source_weight_zero_no_unit_entrance (a.witness ω) κ z₀ hz rf (hfd.trans (hd.trans hδ1.le)) htop z hz'
    change C*δ^(-codimension κ) < _ at hω
    rw [hzX] at hω
    exact (not_lt_of_ge (mul_nonneg hC.le (Real.rpow_nonneg (hf.trans_le hfd).le _))) hω
  · positivity
  · have hh := ht Ω m P hP γ a ρ hρ z₀ rf δ hf hfd hd
    filter_upwards [hh] with ω hω
    intro hωA
    apply hω hωA
    have hs : 3 ≤ dist (γ ω 0) z₀ := by
      rw [(a.witness ω).2.1,dist_zero_left]
      have := (le_abs_self z₀.im).trans (Complex.abs_im_le_norm z₀)
      linarith
    have he : liveSpatialHitTime (γ ω) z₀ 3 = ((ρ ω).untopD 0 : ℝ≥0) := by
      change ρ ω = _
      obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hωA
      rw [← ht]
      rfl
    change closedBall z₀ (1+1) ⊆ _
    convert source_live_collar_free (a.trace_continuous ω) z₀ hz hs ((ρ ω).untopD 0) he using 1
    norm_num

lemma source_live_entrance_bound {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z₀ : ℂ) (hz : 4 ≤ z₀.im) (hsmall : 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*4))) :
    (P.comap Subtype.val).real {ω : a.samples | liveSpatialHitTime (γ ω) z₀ 3 ≠ ⊤} ≤
      (uniformInverseAngleConstant κ 1*(128*Real.pi)^codimension κ*4^codimension κ)*initialGreen κ z₀ := by
  apply le_trans (measureReal_mono (show {ω : a.samples | liveSpatialHitTime (γ ω) z₀ 3 ≠ ⊤} ⊆
      {ω | ∃ t : ℝ≥0, dist (γ ω t) z₀ < 4} from ?_))
  · have hh := euclidean_approach a.brownian κ hκ hκ8 (fun ω : a.samples => γ ω) a.G a.F
      (Eventually.of_forall a.witness) z₀ (by change 0 < z₀.im; linarith) 4 (by norm_num) hz hsmall
    change ((P.comap Subtype.val) {ω : a.samples | ∃ t : ℝ≥0, dist (γ ω t) z₀ < 4}).toReal ≤ _
    calc
      _ ≤ _ := hh
      _ = _ := by ring
  · intro ω hω
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hω
    have hs : 3 ≤ dist (γ ω 0) z₀ := by
      rw [(a.witness ω).2.1,dist_zero_left]
      have := (le_abs_self z₀.im).trans (Complex.abs_im_le_norm z₀)
      linarith
    exact ⟨t,by rw [(source_liveHit_mem (a.trace_continuous ω) z₀ 3 hs t ht.symm).2]; norm_num⟩
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_mesh_tail_to_stretched {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (p C c δ₀ v rf a : ℝ) (hp : 0 < p)
    (_hC : 0 < C) (_hc : 0 < c) (hδ : 0 < δ₀) (hv : 0 ≤ v) (_hf : 0 < rf) (_ha : 0 ≤ a)
    (hbound : ∀ ω, X ω ≤ v*rf^(-p))
    (ht : ∀ δ : ℝ, rf ≤ δ → δ ≤ δ₀ → μ {ω | C*δ^(-p) < X ω} ≤
      ENNReal.ofReal (a*(C*Real.exp (-c*δ^(-2:ℝ))))) :
    ∀ u : ℝ, 1 ≤ u →
      μ {ω | max C v*δ₀^(-p)*u < X ω} ≤
        ENNReal.ofReal (a*C*Real.exp (-(c*δ₀^(-2:ℝ))*u^(2/p))) := by
  intro u hu1
  have hu : 0 < u := zero_lt_one.trans_le hu1
  let δ := δ₀*u^(-1/p)
  have he0 : -1/p ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hp.le
  have hδp : 0 < δ := mul_pos hδ (Real.rpow_pos_of_pos hu _)
  have hδd : δ ≤ δ₀ := by
    dsimp [δ]
    exact mul_le_of_le_one_right hδ.le (Real.rpow_le_one_of_one_le_of_nonpos hu1 he0)
  have he : δ^(-p) = δ₀^(-p)*u := by
    dsimp [δ]
    rw [Real.mul_rpow hδ.le (Real.rpow_nonneg hu.le _),← Real.rpow_mul hu.le]
    have he : (-1/p)*(-p) = 1 := by field_simp
    rw [he,Real.rpow_one]
  have hex : δ^(-2:ℝ) = δ₀^(-2:ℝ)*u^(2/p) := by
    dsimp [δ]
    rw [Real.mul_rpow hδ.le (Real.rpow_nonneg hu.le _),← Real.rpow_mul hu.le]
    congr 2
    ring
  have hn (b : ℝ) (hb : b ≤ max C v) : b*δ^(-p) ≤ max C v*δ₀^(-p)*u := by
    rw [he,←mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hδ.le _)) hu.le
  by_cases hfd : rf ≤ δ
  · apply (measure_mono (show {ω | max C v*δ₀^(-p)*u < X ω} ⊆
        {ω | C*δ^(-p) < X ω} from fun ω hω => (hn C (le_max_left _ _)).trans_lt hω)).trans
    calc
      _ ≤ _ := ht δ hfd hδd
      _ = _ := by
        rw [hex]
        have he : -c*(δ₀^(-2:ℝ)*u^(2/p)) = -(c*δ₀^(-2:ℝ))*u^(2/p) := by ring
        rw [he,mul_assoc]
  · have hx (ω : Ω) : X ω ≤ max C v*δ₀^(-p)*u := by
      calc
        X ω ≤ v*rf^(-p) := hbound ω
        _ ≤ v*δ^(-p) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hδp (le_of_not_ge hfd) (by linarith)) hv
        _ ≤ _ := hn v (le_max_right _ _)
    have he : {ω | max C v*δ₀^(-p)*u < X ω} = ∅ := by
      ext ω; simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false]; exact not_lt_of_ge (hx ω)
    rw [he,measure_empty]
    exact bot_le
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

def SourceLiveEntranceTailTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∃ M C c : ℝ, 0 < M ∧ 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ),
    4 ≤ z₀.im → 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*4)) →
  ∀ (rf u : ℝ), 0 < rf → rf ≤ 1 → 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | M*u < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (Metric.ball z₀ 1)} ≤
      ENNReal.ofReal (C*initialGreen κ z₀*Real.exp (-c*u^(2/codimension κ)))
theorem sourceLiveEntranceTail_proved : SourceLiveEntranceTailTarget := by
  intro κ hκ hκ8
  obtain ⟨C,c,δ₀,hC,hc,hδ,hδ1,ht⟩ := source_live_unit_mesh_tail κ hκ hκ8
  let v := (volume (ball (0:ℂ) 1)).toReal
  let M := max C v*δ₀^(-codimension κ)
  let b := c*δ₀^(-2:ℝ)
  let A := uniformInverseAngleConstant κ 1*(128*Real.pi)^codimension κ*4^codimension κ
  have hk : 0 < κ := by linarith
  have hp : 0 < codimension κ := codimension_pos κ hκ8
  have hM : 0 < M := mul_pos (hC.trans_le (le_max_left _ _)) (Real.rpow_pos_of_pos hδ _)
  have hb : 0 < b := mul_pos hc (Real.rpow_pos_of_pos hδ _)
  have hA : 0 < A := mul_pos (mul_pos (uniformInverseAngleConstant_pos κ 1 hk hκ8 zero_lt_one)
    (Real.rpow_pos_of_pos (by positivity) _)) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨M,A*C,b,hM,mul_pos hA hC,hb,?_⟩
  intro Ω m P hP γ a z₀ hz hsmall rf u hf hf1 hu
  let : IsProbabilityMeasure P := hP
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let X := fun ω : a.samples => spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) rf (ball z₀ 1)
  have hx (ω : a.samples) : X ω ≤ v*rf^(-codimension κ) := by
    have hh := (a.spatialRealMass_bound hk hκ8 rf hf (ball z₀ 1) measurableSet_ball
      (measure_ball_lt_top (μ := volume) (x := z₀) (r := 1)).ne (fun z hz' => ?_) ω).2
    · simpa only [v,Complex.volume_ball] using hh
    · have hd : abs (z.im-z₀.im) ≤ dist z z₀ := by
        simpa only [dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (z-z₀)
      have hh : dist z z₀ < 1 := hz'
      have ha := neg_abs_le (z.im-z₀.im)
      linarith
  have ht' := source_mesh_tail_to_stretched μ X (codimension κ) C c δ₀ v rf
    (μ.real {ω : a.samples | liveSpatialHitTime (γ ω) z₀ 3 ≠ ⊤}) hp hC hc hδ
    ENNReal.toReal_nonneg hf ENNReal.toReal_nonneg hx
    (fun δ hfd hd => ht Ω m P hP γ a z₀ hz rf δ hf hfd hd) u hu
  apply ht'.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (A*initialGreen κ z₀)*C*Real.exp (-b*u^(2/codimension κ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (source_live_entrance_bound a hk hκ8 z₀ hz hsmall) hC.le) (Real.exp_pos _).le
    _ = _ := by ring
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_scaled_radius_hit_iff (c : ℝ≥0) (hc : 0 < c)
    (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) (t : ℝ≥0) :
    dist (sourceScaleTrace c γ t) ((c : ℂ) * z) - (c : ℝ) * r = 0 ↔
      dist (γ (sourceScaleTime c t)) z - r = 0 := by
  have hcR : 0 < (c : ℝ) := hc
  rw [sourceScaleTrace, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hcR, ← dist_eq_norm, ← mul_sub]
  exact mul_eq_zero.trans (or_iff_right hcR.ne')

lemma source_scale_spatial_hit (c : ℝ≥0) (hc : 0 < c)
    (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) :
    spatialHitTime (sourceScaleTrace c γ) ((c : ℂ) * z) ((c : ℝ) * r) =
      WithTop.map (fun t : ℝ≥0 => c ^ 2 * t) (spatialHitTime γ z r) := by
  classical
  let S : Set ℝ≥0 := {t | dist (γ t) z - r = 0}
  let Sc : Set ℝ≥0 := {t | dist (sourceScaleTrace c γ t) ((c : ℂ) * z) - (c : ℝ) * r = 0}
  let e : ℝ≥0 ≃o ℝ≥0 := OrderIso.mulLeft₀ (c ^ 2) (pow_pos hc 2)
  have he (x : ℝ≥0) : e x = c ^ 2 * x := rfl
  have htime (x : ℝ≥0) : sourceScaleTime c (c ^ 2 * x) = x := by
    simp [sourceScaleTime, hc.ne']
  have hset : e '' S = Sc := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (source_scaled_radius_hit_iff c hc γ z r _).2 (by simpa only [he, htime] using (show dist (γ u) z - r = 0 from hu))
    · intro ht
      refine ⟨sourceScaleTime c t, (source_scaled_radius_hit_iff c hc γ z r t).1 ht, ?_⟩
      simp [he, sourceScaleTime, mul_div_cancel₀ _ (pow_ne_zero 2 hc.ne')]
  unfold spatialHitTime hittingAfter
  simp only [zero_le, true_and, Set.mem_singleton_iff]
  change (if Sc.Nonempty then ((sInf Sc : ℝ≥0) : WithTop ℝ≥0) else ⊤) =
    WithTop.map (fun t : ℝ≥0 => c^2*t) (if S.Nonempty then ((sInf S : ℝ≥0) : WithTop ℝ≥0) else ⊤)
  have hh : Sc.Nonempty ↔ S.Nonempty := by rw [← hset]; exact Set.image_nonempty
  by_cases hS : S.Nonempty
  · rw [ite_eq_left hS, ite_eq_left (hh.mpr hS), WithTop.map_coe]
    congr 1
    rw [← he, e.map_csInf' hS (OrderBot.bddBelow S), hset]
  · rw [ite_eq_right hS, ite_eq_right (mt hh.mp hS), WithTop.map_top]

lemma source_scale_spatial_hit_top (c : ℝ≥0) (hc : 0 < c)
    (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) :
    spatialHitTime (sourceScaleTrace c γ) ((c : ℂ) * z) ((c : ℝ) * r) = ⊤ ↔
      spatialHitTime γ z r = ⊤ := by
  rw [source_scale_spatial_hit c hc]
  simp

lemma source_scale_spatial_hit_value (c : ℝ≥0) (hc : 0 < c)
    (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) :
    (spatialHitTime (sourceScaleTrace c γ) ((c : ℂ) * z) ((c : ℝ) * r)).untopD 0 =
      c ^ 2 * (spatialHitTime γ z r).untopD 0 := by
  rw [source_scale_spatial_hit c hc]
  cases hh : spatialHitTime γ z r
  · simp
  · rfl

lemma source_scale_spatial_hit_le (c : ℝ≥0) (hc : 0 < c)
    (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) (T : ℝ≥0) :
    spatialHitTime (sourceScaleTrace c γ) ((c : ℂ) * z) ((c : ℝ) * r) ≤ (c ^ 2 * T : ℝ≥0) ↔
      spatialHitTime γ z r ≤ T := by
  rw [source_scale_spatial_hit c hc]
  cases hh : spatialHitTime γ z r
  · exact iff_of_false (WithTop.not_top_le_coe _) (WithTop.not_top_le_coe _)
  · simp only [WithTop.map_coe, WithTop.coe_le_coe]
    exact mul_le_mul_iff_right₀ (pow_pos hc 2)

lemma source_scale_chart_deriv (c : ℝ≥0) (hc : 0 < c)
    (G : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) :
    deriv (sourceScaleChart c G t) ((c : ℂ) * z) = deriv (G (sourceScaleTime c t)) z := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  change deriv (fun w : ℂ => (c : ℂ) * G (sourceScaleTime c t) (w / (c : ℂ))) _ = _
  rw [deriv_const_mul_field]
  simp_rw [div_eq_mul_inv, mul_comm _ ((c : ℂ)⁻¹)]
  rw [deriv_comp_mul_left]
  simp only [smul_eq_mul]
  simp [hcC]

lemma source_scale_fullRadius (c : ℝ≥0) (hc : 0 < c)
    (G : ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) (z : ℂ) :
    fullRadius (sourceScaleChart c G) t ((c : ℂ) * z) =
      (c : ℝ) * fullRadius G (sourceScaleTime c t) z := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  unfold fullRadius
  rw [source_scale_chart_deriv c hc]
  simp only [sourceScaleChart, mul_div_cancel_left₀ _ hcC, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  ring

lemma source_scale_greenDensity (κ : ℝ) (c : ℝ≥0) (hc : 0 < c)
    (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (z : ℂ) :
    greenDensity κ (fun u => (c : ℝ) * U (sourceScaleTime c u))
      (sourceScaleTrace c γ) (sourceScaleChart c G) t ((c : ℂ) * z) =
    ((c : ℝ) ^ (-codimension κ)) * greenDensity κ U γ G (sourceScaleTime c t) z := by
  have hcR : 0 < (c : ℝ) := hc
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hlive : (c : ℂ) * z ∈ survivingDomain (sourceScaleTrace c γ) t ↔
      z ∈ survivingDomain γ (sourceScaleTime c t) := by
    simpa [hcC] using source_scale_domain_iff c t hc γ ((c : ℂ) * z)
  by_cases hz : z ∈ survivingDomain γ (sourceScaleTime c t)
  · simp only [greenDensity,ite_eq_left hz,ite_eq_left (hlive.mpr hz)]
    rw [source_scale_fullRadius c hc]
    have hR : 0 ≤ fullRadius G (sourceScaleTime c t) z := by
      exact div_nonneg (mul_nonneg (by norm_num) (hw.2.2.2.2.2.1 _ hz).le) (norm_nonneg _)
    rw [Real.mul_rpow hcR.le hR]
    simp only [sourceScaleChart, mul_div_cancel_left₀ _ hcC, Complex.ofReal_mul, ← mul_sub]
    rw [Complex.arg_real_mul _ hcR]
    ring
  · simp only [greenDensity,ite_eq_right hz,ite_eq_right (mt hlive.mp hz),mul_zero]
lemma source_scale_spatial_greenWeight (κ : ℝ) (c : ℝ≥0) (hc : 0 < c)
    (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F) (z : ℂ) (r : ℝ) :
    spatialGreenWeight κ (fun u => (c : ℝ) * U (sourceScaleTime c u))
      (sourceScaleTrace c γ) (sourceScaleChart c G) ((c : ℂ) * z) ((c : ℝ) * r) =
    ((c : ℝ) ^ (-codimension κ)) * spatialGreenWeight κ U γ G z r := by
  unfold spatialGreenWeight
  simp only [source_scale_spatial_hit_top c hc]
  split_ifs with ht
  · simp
  · rw [source_scale_greenDensity κ c hc U γ G F hw, source_scale_spatial_hit_value c hc]
    simp [sourceScaleTime, hc.ne']

end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
def sourceScaled (a : RegularSLEPresentation P κ γ) (c : ℝ≥0) (hc : 0 < c) :
    RegularSLEPresentation P κ (fun ω => sourceScaleTrace c (γ ω)) where
  samples := a.samples
  measurable_samples := a.measurable_samples
  full_samples := a.full_samples
  B := fun t ω => (c:ℝ)*a.B (sourceScaleTime c t) ω
  measurable_B := fun t => measurable_const.mul (a.measurable_B _)
  continuous_B := fun ω => continuous_const.mul ((a.continuous_B ω).comp (by unfold sourceScaleTime; fun_prop))
  zero_B := fun ω => by simp [sourceScaleTime,a.zero_B ω]
  brownian := by
    have hh := a.brownian.smul (c := (c^2)⁻¹) (inv_ne_zero (pow_ne_zero 2 hc.ne'))
    simpa only [sourceScaleTime,NNReal.coe_inv,NNReal.coe_pow,Real.sqrt_inv,
      Real.sqrt_sq c.coe_nonneg,inv_inv,div_eq_mul_inv,mul_comm] using hh
  G := fun ω => sourceScaleChart c (a.G ω)
  F := fun ω => sourceScaleChart c (a.F ω)
  witness := fun ω => by
    have hh := source_scale_witness c hc (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (a.F ω) (a.witness ω)
    simpa only [mul_left_comm (c:ℝ) (Real.sqrt κ)] using hh
end RegularSLEPresentation

lemma source_scale_initialGreen (κ : ℝ) (c : ℝ≥0) (hc : 0 < c) (z : ℂ) (hz : 0 ≤ z.im) :
    initialGreen κ ((c:ℂ)*z) = (c:ℝ)^(-codimension κ)*initialGreen κ z := by
  have hcR : 0 < (c:ℝ) := hc
  unfold initialGreen
  rw [Complex.arg_real_mul _ hcR]
  have him : 2*((c:ℂ)*z).im = (c:ℝ)*(2*z.im) := by simp [Complex.mul_im]; ring
  rw [him,Real.mul_rpow hcR.le (mul_nonneg (by norm_num) hz),mul_assoc]
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_scale_area_real_integral (c : ℝ≥0) (hc : 0 < c)
    (f : ℂ → ℝ) (K : Set ℂ) :
    (∫ z in (fun z : ℂ => (c : ℂ) * z) '' K, f z) =
      ((c : ℝ)^2) * ∫ z in K, f ((c : ℂ) * z) := by
  have hcR : 0 < (c : ℝ) := hc
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  let e := Homeomorph.mulLeft₀ (c : ℂ) hcC
  have he (z : ℂ) : e z = (c : ℂ) * z := rfl
  have hvol (s : Set ℂ) : volume (e ⁻¹' s) =
      ENNReal.ofReal (((c : ℝ)^2)⁻¹) * volume s := by
    change volume ((fun z : ℂ => (c : ℂ) * z) ⁻¹' s) = _
    simpa only [Complex.real_smul, smul_eq_mul, Complex.finrank_real_complex,
      abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (c : ℝ)))] using
      (volume : Measure ℂ).addHaar_preimage_smul hcR.ne' s
  have hp : MeasurePreserving e (ENNReal.ofReal ((c : ℝ)^2) • (volume : Measure ℂ)) volume := by
    refine ⟨e.continuous.measurable, ?_⟩
    apply Measure.ext
    intro s hs
    rw [e.measurableEmbedding.map_apply, Measure.smul_apply, smul_eq_mul, hvol, ← mul_assoc,
      ← ENNReal.ofReal_mul (sq_nonneg (c : ℝ)), mul_inv_cancel₀ (pow_ne_zero 2 hcR.ne'),
      ENNReal.ofReal_one, one_mul]
  have hh := hp.setIntegral_image_emb e.measurableEmbedding f K
  rw [Measure.restrict_smul,integral_smul_measure] at hh
  simpa only [he,ENNReal.toReal_ofReal (sq_nonneg (c:ℝ)),smul_eq_mul] using hh

lemma source_scale_spatialRealMass (κ : ℝ) (c : ℝ≥0) (hc : 0 < c)
    (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F) (r : ℝ) (K : Set ℂ) :
    spatialRealMass κ (fun t => (c:ℝ)*U (sourceScaleTime c t))
      (sourceScaleTrace c γ) (sourceScaleChart c G) ((c:ℝ)*r)
      ((fun z : ℂ => (c:ℂ)*z) '' K) =
      (c:ℝ)^dimension κ*spatialRealMass κ U γ G r K := by
  unfold spatialRealMass
  rw [source_scale_area_real_integral c hc]
  simp_rw [source_scale_spatial_greenWeight κ c hc U γ G F hw]
  rw [integral_const_mul,←mul_assoc]
  congr 1
  rw [←Real.rpow_natCast (c:ℝ) 2,←Real.rpow_add (show 0 < (c:ℝ) from hc)]
  congr 1
  simp [codimension]

lemma source_scale_ball (c : ℝ≥0) (hc : 0 < c) (z : ℂ) (r : ℝ) :
    (fun w : ℂ => (c:ℂ)*w) '' Metric.ball z r = Metric.ball ((c:ℂ)*z) ((c:ℝ)*r) := by
  have hcR : 0 < (c:ℝ) := hc
  simpa only [Complex.real_smul,smul_eq_mul,Real.norm_eq_abs,abs_of_pos hcR] using
    Metric.smul_image_ball (α := ℝ) hcR.ne' z r

lemma RegularSLEPresentation.sourceScaled_mass {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (c : ℝ≥0) (hc : 0 < c) (z : ℂ) (r rf : ℝ) (ω : a.samples) :
    spatialRealMass κ (fun t => Real.sqrt κ*(a.sourceScaled c hc).B t ω)
      (sourceScaleTrace c (γ ω)) ((a.sourceScaled c hc).G ω) ((c:ℝ)*rf)
      (Metric.ball ((c:ℂ)*z) ((c:ℝ)*r)) =
      (c:ℝ)^dimension κ*spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (Metric.ball z r) := by
  rw [←source_scale_ball c hc]
  simpa only [RegularSLEPresentation.sourceScaled,mul_left_comm (Real.sqrt κ) (c:ℝ)] using
    source_scale_spatialRealMass κ c hc (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (a.F ω) (a.witness ω) rf (Metric.ball z r)
end
end SLEExactGauge
end

 
section
open Set MeasureTheory
lemma source_tail_threshold_normalize {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (M C A b q K : ℝ)
    (hM : 0 < M) (hC : 0 < C) (_hA : 0 < A) (hb : 0 < b) (hq : 0 < q) (hK : 0 ≤ K)
    (hzero : μ {ω | 0 < X ω} ≤ ENNReal.ofReal (A*K))
    (ht : ∀ u : ℝ, 1 ≤ u → μ {ω | M*u < X ω} ≤ ENNReal.ofReal (C*K*Real.exp (-b*u^q)))
    (u : ℝ) (hu : 1 ≤ u) :
    μ {ω | u < X ω} ≤ ENNReal.ofReal
      ((max C A*Real.exp b)*K*Real.exp (-(b/(max M 1)^q)*u^q)) := by
  let R := max M 1
  have hR : 0 < R := hM.trans_le (le_max_left _ _)
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have he : -(b/R^q)*u^q = -b*(u/R)^q := by
    rw [Real.div_rpow hu0.le hR.le]
    ring
  rw [he]
  by_cases hbig : R ≤ u
  · have hv : 1 ≤ u/R := (le_div_iff₀ hR).mpr (by simpa using hbig)
    have hth : M*(u/R) ≤ u := by
      calc
        _ ≤ R*(u/R) := mul_le_mul_of_nonneg_right (le_max_left _ _) (div_nonneg hu0.le hR.le)
        _ = _ := by field_simp
    apply (measure_mono (show {ω | u < X ω} ⊆ {ω | M*(u/R) < X ω} from
      fun ω hω => hth.trans_lt hω)).trans (ht (u/R) hv |>.trans _)
    apply ENNReal.ofReal_le_ofReal
    gcongr
    calc
      C ≤ max C A := le_max_left _ _
      _ ≤ max C A*Real.exp b := le_mul_of_one_le_right (hC.le.trans (le_max_left _ _))
        (Real.one_le_exp_iff.mpr hb.le)
  · have hv : 0 ≤ u/R := div_nonneg hu0.le hR.le
    have hv1 : u/R ≤ 1 := (div_le_one hR).mpr (le_of_not_ge hbig)
    have hp : (u/R)^q ≤ 1 := Real.rpow_le_one hv hv1 hq.le
    have hexp : 1 ≤ Real.exp b*Real.exp (-b*(u/R)^q) := by
      rw [←Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      nlinarith
    apply (measure_mono (show {ω | u < X ω} ⊆ {ω | 0 < X ω} from
      fun ω hω => hu0.trans hω)).trans (hzero.trans _)
    apply ENNReal.ofReal_le_ofReal
    calc
      A*K ≤ max C A*K := mul_le_mul_of_nonneg_right (le_max_right _ _) hK
      _ ≤ (max C A*K)*(Real.exp b*Real.exp (-b*(u/R)^q)) :=
        le_mul_of_one_le_right (mul_nonneg (hC.le.trans (le_max_left _ _)) hK) hexp
      _ = _ := by ring
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_live_entrance_all_tail (κ : ℝ) (hκ : 4 < κ) (hκ8 : κ < 8) :
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ),
    4 ≤ z₀.im → 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*4)) →
  ∀ (rf u : ℝ), 0 < rf → rf ≤ 1 → 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | u < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1)} ≤
      ENNReal.ofReal (C*initialGreen κ z₀*Real.exp (-c*u^(2/codimension κ))) := by
  obtain ⟨M,C,b,hM,hC,hb,ht⟩ := sourceLiveEntranceTail_proved κ hκ hκ8
  let A := uniformInverseAngleConstant κ 1*(128*Real.pi)^codimension κ*4^codimension κ
  have hk : 0 < κ := by linarith
  have hA : 0 < A := mul_pos (mul_pos (uniformInverseAngleConstant_pos κ 1 hk hκ8 zero_lt_one)
    (Real.rpow_pos_of_pos (by positivity) _)) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨max C A*Real.exp b,b/(max M 1)^(2/codimension κ),
    mul_pos (hC.trans_le (le_max_left _ _)) (Real.exp_pos _),
    div_pos hb (Real.rpow_pos_of_pos (hM.trans_le (le_max_left _ _)) _),?_⟩
  intro Ω m P hP γ a z₀ hz hsmall rf u hf hf1 hu
  let : IsProbabilityMeasure P := hP
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let X := fun ω : a.samples => spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) rf (ball z₀ 1)
  have hK : 0 < initialGreen κ z₀ := initialGreen_pos κ z₀ (by change 0 < z₀.im; linarith)
  have hzero : μ {ω | 0 < X ω} ≤ ENNReal.ofReal (A*initialGreen κ z₀) := by
    apply le_trans (measure_mono (show {ω | 0 < X ω} ⊆
      {ω : a.samples | liveSpatialHitTime (γ ω) z₀ 3 ≠ ⊤} from ?_))
    · apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (mul_pos hA hK).le).mpr
      exact source_live_entrance_bound a hk hκ8 z₀ hz hsmall
    · intro ω hω hn
      have hx : X ω = 0 := by
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro z hz'
        exact source_weight_zero_no_unit_entrance (a.witness ω) κ z₀ hz rf hf1 hn z hz'
      change 0 < X ω at hω
      rw [hx] at hω
      exact (lt_irrefl 0) hω
  exact source_tail_threshold_normalize μ X M C A b (2/codimension κ) (initialGreen κ z₀)
    hM hC hA hb (div_pos (by norm_num) (codimension_pos κ hκ8)) hK.le hzero
    (fun v hv => ht Ω m P hP γ a z₀ hz hsmall rf v hf hf1 hv) u hu
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

def SourcePhysicalBallAllTailTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ) (r : ℝ),
    0 < r → 4*r ≤ z₀.im → 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*(4*r))) →
  ∀ (rf u : ℝ), 0 < rf → rf ≤ r → 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | r^dimension κ*u < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (Metric.ball z₀ r)} ≤
      ENNReal.ofReal (C*r^codimension κ*initialGreen κ z₀*Real.exp (-c*u^(2/codimension κ)))
theorem sourcePhysicalBallAllTail_proved : SourcePhysicalBallAllTailTarget := by
  intro κ hκ hκ8
  obtain ⟨C,b,hC,hb,ht⟩ := source_live_entrance_all_tail κ hκ hκ8
  refine ⟨C,b,hC,hb,?_⟩
  intro Ω m P hP γ a z r hr hz hsmall rf u hf hfr hu
  let : IsProbabilityMeasure P := hP
  let c : ℝ≥0 := ⟨r⁻¹,(inv_pos.mpr hr).le⟩
  have hc : 0 < c := inv_pos.mpr hr
  have hcR : (c:ℝ) = r⁻¹ := rfl
  let a' := a.sourceScaled c hc
  have him : ((c:ℂ)*z).im = r⁻¹*z.im := by simp [hcR,Complex.mul_im]
  have hcr : (c:ℝ)*r = 1 := by rw [hcR,inv_mul_cancel₀ hr.ne']
  have hheight : 4 ≤ ((c:ℂ)*z).im := by
    rw [him,mul_comm,←div_eq_mul_inv]
    exact (le_div_iff₀ hr).mpr hz
  have hsmall' : 1 ≤ Real.log ((2*((c:ℂ)*z).im)/((128*Real.pi)*4)) := by
    have he : (2*((c:ℂ)*z).im)/((128*Real.pi)*4) = (2*z.im)/((128*Real.pi)*(4*r)) := by
      rw [him]
      field_simp
    rwa [he]
  have hf' : 0 < (c:ℝ)*rf := mul_pos hc hf
  have hfr' : (c:ℝ)*rf ≤ 1 := by rw [←hcr]; exact mul_le_mul_of_nonneg_left hfr hc.le
  have htail := ht Ω m P hP (fun ω => sourceScaleTrace c (γ ω)) a' ((c:ℂ)*z)
    hheight hsmall' ((c:ℝ)*rf) u hf' hfr' hu
  change (P.comap (Subtype.val : a.samples → Ω)) {ω : a.samples | u < spatialRealMass κ
      (fun t => Real.sqrt κ*a'.B t ω) (sourceScaleTrace c (γ ω)) (a'.G ω)
      ((c:ℝ)*rf) (ball ((c:ℂ)*z) 1)} ≤
      ENNReal.ofReal (C*initialGreen κ ((c:ℂ)*z)*Real.exp (-b*u^(2/codimension κ))) at htail
  have hp : 0 < (c:ℝ)^dimension κ := Real.rpow_pos_of_pos hc _
  have hrp : 0 < r^dimension κ := Real.rpow_pos_of_pos hr _
  have hmr : (c:ℝ)^dimension κ*(r^dimension κ*u) = u := by
    rw [hcR,Real.inv_rpow hr.le]
    field_simp
  have hx (ω : a.samples) : spatialRealMass κ (fun t => Real.sqrt κ*a'.B t ω)
      (sourceScaleTrace c (γ ω)) (a'.G ω) ((c:ℝ)*rf) (ball ((c:ℂ)*z) 1) =
      (c:ℝ)^dimension κ*spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z r) := by
    simpa only [hcr] using a.sourceScaled_mass c hc z r rf ω
  have he : {ω : a.samples | u < spatialRealMass κ (fun t => Real.sqrt κ*a'.B t ω)
      (sourceScaleTrace c (γ ω)) (a'.G ω) ((c:ℝ)*rf) (ball ((c:ℂ)*z) 1)} =
      {ω : a.samples | r^dimension κ*u < spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
        (γ ω) (a.G ω) rf (ball z r)} := by
    ext ω
    change (u < _) ↔ _
    rw [hx ω]
    conv_lhs => rw [←hmr]
    exact mul_lt_mul_iff_right₀ hp
  rw [he] at htail
  have hg : initialGreen κ ((c:ℂ)*z) = r^codimension κ*initialGreen κ z := by
    rw [source_scale_initialGreen κ c hc z (by nlinarith),hcR,Real.inv_rpow hr.le,Real.rpow_neg hr.le,inv_inv]
  rw [hg] at htail
  convert htail using 1
  congr 1
  ring
end
end SLEExactGauge
end

end OAI
