import Mathlib
import OAI.Probability.SLELocalization.SlabMoments
import OAI.Probability.SLE.ClippedCoordinates
import OAI.Probability.SLE.IntegralLimits
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Mesh estimates. -/

section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.Mesh

lemma interval_square_bound {A : Set ℂ} (hA : volume A ≠ ⊤) (C : ℝ → ℂ → ℝ)
    {T K J R : ℝ} (hT : 0 ≤ T) (hJ : 0 ≤ J)
    (hb : (∫⁻ t, ENNReal.ofReal (|∫ z in A, C t z|^2)) ≤
      2*ENNReal.ofReal (K^2)*ENNReal.ofReal (J*R^2)*volume A) :
    (∫ t in (0:ℝ)..T, (∫ z in A, C t z)^2) ≤ 2*K^2*(J*R^2)*(volume A).toReal := by
  rw [intervalIntegral.integral_of_le hT]
  have hh : ENNReal.ofReal (∫ t in Ioc (0:ℝ) T, (∫ z in A, C t z)^2) ≤
      ∫⁻ t in Ioc (0:ℝ) T, ENNReal.ofReal ((∫ z in A, C t z)^2) := by
    calc
      _ ≤ ‖∫ t in Ioc (0:ℝ) T, (∫ z in A, C t z)^2‖ₑ := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ t in Ioc (0:ℝ) T, ‖(∫ z in A, C t z)^2‖ₑ :=
        enorm_integral_le_lintegral_enorm _
      _ = _ := by
        apply lintegral_congr
        intro t
        rw [← ofReal_norm,Real.norm_of_nonneg (sq_nonneg _)]
  have hh' := hh.trans (lintegral_mono' (μ := volume.restrict (Ioc (0:ℝ) T))
    (ν := volume) Measure.restrict_le_self le_rfl)
  simp only [sq_abs] at hb
  have hrhs : 2*ENNReal.ofReal (K^2)*ENNReal.ofReal (J*R^2)*volume A =
      ENNReal.ofReal (2*K^2*(J*R^2)*(volume A).toReal) := by
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (mul_nonneg hJ (sq_nonneg _))),
      ENNReal.ofReal_toReal hA,ENNReal.ofReal_mul (mul_nonneg (by norm_num) (sq_nonneg _)),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2*K^2*(J*R^2)*(volume A).toReal)).1
  exact (hh'.trans hb).trans_eq hrhs

end SLEExactGauge.Mesh

end

end

section
noncomputable section
open Set Filter Metric MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.MeshSlab
open LoewnerCutoff LoewnerField LoewnerExit LoewnerLocalized Mesh
open BrownianPredictable BrownianIto TaylorMeshes PredictableLimit
local instance meshExponentsCommonRealMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _
local instance meshExponentsCommonRealBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩
local instance meshExponentsCommonComplexMeasurableSpace : MeasurableSpace C(I,ℂ) := borel _
local instance meshExponentsCommonComplexBorelSpace : BorelSpace C(I,ℂ) := ⟨rfl⟩

theorem common_slab_mgf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A : Set ℂ} {u : ℂ → ℝ} (C : FiniteTilt.CommonCutoff A u)
    (hA : MeasurableSet A) [IsFiniteMeasure (volume.restrict A)]
    (κ : ℝ) (hκ : 0 < κ ∧ κ ≤ 4) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ ω ∂P, IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hhalf : ∀ z ∈ A, z ∈ halfPlane) (hu : ∀ z ∈ A, 0 < u z)
    {ρ : ℝ} (hr : ∀ z ∈ A, (2*z.im)*Real.exp (-u z) = ρ)
    (V : Ω → C(I,ℂ)) (hVm : Measurable V)
    (hV : ∀ᵐ ω ∂P, ∀ q : I, V ω q = γ ω ((C.horizon:ℝ)*q))
    (e r : ℝ) (he : 0 < e) (her : e ≤ r) (hes : ∀ z ∈ A, e < z.im)
    (J : ℝ) (hJ : 0 ≤ J)
    (hlayer : ∀ ω, IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω) →
      ∀ t : ℝ, 0 ≤ t → ∀ z ∈ localizationDomain (γ ω) t,
      (∫⁻ w in {w : ℂ | w ∈ localizationDomain (γ ω) t ∧ infDist w (localizationDomain (γ ω) t)ᶜ ≤ r},
        ENNReal.ofReal (halfPlaneGreen (g ω t z) (g ω t w))) ≤ ENNReal.ofReal (J*r^2)) (θ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ*(∫ z in A,
      observedDifference C.height_pos C.horizon.coe_nonneg κ ρ C.angle e r
        ((BrownianDriver.path B (Real.sqrt κ) C.horizon ω,V ω),z)))) ∂P) ≤
      ENNReal.ofReal (Real.exp (θ^2*(2*(Real.sqrt κ*(8/κ-1)*(e/4)^(-(1-κ/8)))^2*
        (J*r^2)*(volume A).toReal)/2)) := by
  have hκ' : 0 < κ ∧ κ < 8 := ⟨hκ.1,by linarith [hκ.2]⟩
  let ν := volume.restrict A
  let X := fun n i => slabCoeff C.height_pos κ B C.horizon (dyadicTime C.horizon n i) ρ C.angle e r
  let Y := fun q : Ω × ℂ => observedDifference C.height_pos C.horizon.coe_nonneg κ ρ C.angle e r
    ((BrownianDriver.path B (Real.sqrt κ) C.horizon q.1,V q.1),q.2)
  have hXm (n i : ℕ) : AEMeasurable (X n i) (P.prod ν) :=
    (coeff_aemeasurable hB ν C.height_pos κ _ _ ρ C.angle e).sub
      (coeff_aemeasurable hB ν C.height_pos κ _ _ ρ C.angle r)
  have hXp (n i : ℕ) : @Measurable (Ω × ℂ) ℝ
      (Prod.instMeasurableSpace (m₁ := pastSigma B (dyadicTime C.horizon n i)) (m₂ := inferInstance)) _ (X n i) :=
    (coeff_measurable_past C.height_pos κ B _ _ ρ C.angle e).sub
      (coeff_measurable_past C.height_pos κ B _ _ ρ C.angle r)
  obtain ⟨K,hK,hbound⟩ := coeff_uniform_bound C.height_pos κ hκ' B C.horizon ρ C.angle
  have hXbound (n i : ℕ) (q : Ω × ℂ) : |X n i q| ≤ 2*K := by
    exact (abs_sub _ _).trans ((add_le_add (hbound e _ q) (hbound r _ q)).trans_eq (by ring))
  have hsum := SpatialLimit.bounded_sums ν hB C.horizon X hXp hXm (2*K) (by positivity) hXbound
  have hY := observedDifference_aemeasurable hB ν C.height_pos κ ρ C.angle e r C.horizon V hVm
  have hlim : ∀ᵐ q ∂P.prod ν, Tendsto
      (fun n => dyadicDriverSum B C.horizon (fun n i ω => X n i (ω,q.2)) n q.1) atTop (𝓝 (Y q)) := by
    apply SpatialLimit.ae_prod_tendsto_of_fibers
      (fun n => SpatialLimit.sums_aemeasurable hB C.horizon X hXm n) hY
    filter_upwards [ae_restrict_mem hA] with z hz
    exact slab_sum_tendsto C κ hκ' B hB γ g f hmaps z hz (hhalf z hz) (hu z hz) (hr z hz) V hV e r
  let Q := fun ω => ∫ t in (0:ℝ)..C.horizon, (∫ z in A,
    pathSlab C.height_pos C.horizon.coe_nonneg κ ρ C.angle e r
      (BrownianDriver.path B (Real.sqrt κ) C.horizon ω) (V ω) (fun t => B t ω) t z)^2
  have hQ : ∀ᵐ ω ∂P, Tendsto (fun n => dyadicVariance C.horizon
      (fun n i ω => ∫ z, X n i (ω,z) ∂ν) n ω) atTop (𝓝 (Q ω)) := by
    filter_upwards [hmaps,hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero,hV] with ω hm hc hb0 hv
    exact slabCoeff_variance_tendsto C hA κ hκ' B γ g f ω hm hc hb0 hhalf hu hr (V ω) hv e r her
  let J' := 2*(Real.sqrt κ*(8/κ-1)*(e/4)^(-(1-κ/8)))^2*(J*r^2)*(volume A).toReal
  have hJ' : ∀ᵐ ω ∂P, Q ω ≤ J' := by
    filter_upwards [hmaps,hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero,hV] with ω hm hc hb0 hv
    have hbr := observed_bracket C hA κ hκ B γ g f ω hm hc hb0 hhalf hu hr (V ω) hv e r he her hes J (hlayer ω hm)
    have hAf : volume A ≠ ⊤ := by
      simpa only [Measure.restrict_apply_univ] using measure_ne_top (volume.restrict A) univ
    exact interval_square_bound hAf _ C.horizon.coe_nonneg hJ hbr
  exact SpatialLimit.spatial_exponential_bound ν hB C.horizon X hsum.1 hXp Y
    (fun n => (hsum.2 n).1) (∫ _ : ℂ, (2*K)^2*(C.horizon:ℝ) ∂ν)
    (fun n => (hsum.2 n).2) hlim Q hQ J' θ hJ'

end SLEExactGauge.MeshSlab

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt
variable {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ → ℂ)
variable (g f : Ω → ℝ → ℂ → ℂ) (sample : Ω)
variable (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
variable {z : ℂ} (hz : z ∈ halfPlane) {u : ℝ} (hu : 0 < u)
variable (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0)
variable {ε : ℝ} (hε : 0 < ε) (hsmall : ε < z.im)
variable (hρ : (2*z.im)*Real.exp (-u) < ε/4)
variable (Cs : ℕ → Cutoff z u) (hCs : Tendsto (fun n => (Cs n).angle) atTop (𝓝 0))
include h hz hu hc hb0 hε hsmall hρ hCs

lemma eventually_physicalValue_at_hit_general (hfin : firstLiveDistanceStop (γ sample) z ε ≠ ⊤) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ((Cs n).physicalValue κ B γ ε sample) =
      physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z ε := by
  obtain ⟨t,ht,hzt,hd,hmin⟩ := PhysicalStop.finite_spec h.1 hfin
  obtain ⟨η,hη,hm⟩ := h.sine_positive_minimum (κ := κ) (B := fun t => B t sample) hc t.coe_nonneg hzt
  have hδ : ∀ᶠ n : ℕ in atTop, (Cs n).angle < η :=
    hCs.eventually (gt_mem_nhds hη)
  filter_upwards [hδ] with n hn
  let C := Cs n
  have htc : (t:ℝ) ≤ C.stopTime κ B sample := by
    by_contra hnot
    have hlt : C.stopTime κ B sample < t := lt_of_not_ge hnot
    rcases C.source_terminal κ B sample h hz hu hc hb0 with hr | hs
    · have hh := h.radius_ge_before_distance_stop hε hsmall
        (t := ⟨C.stopTime κ B sample,(C.bounds κ B sample).1⟩)
        (by rw [ht]; exact ENNReal.coe_le_coe.2 hlt.le)
        (C.source_live κ B sample h hz hu hc hb0)
      change ε/4 ≤ loewnerRadius (g sample) (C.stopTime κ B sample) z at hh
      rw [hr] at hh
      exact (not_lt_of_ge hh) hρ
    · have hh := hm (C.stopTime κ B sample) ⟨(C.bounds κ B sample).1,hlt.le⟩
      rw [hs] at hh
      exact (not_lt_of_ge hh) hn
  have he : C.physicalTime κ B γ ε sample = t := by
    rw [Cutoff.physicalTime,ht,PhysicalStop.cap_coe htc]
  have hp : codimension κ = 1-κ/8 := by unfold codimension dimension; ring
  rw [physicalStoppedDensity,ht,ite_eq_right ENNReal.coe_ne_top,ENNReal.coe_toReal,hp,
    C.physicalValue_eq_source κ B γ g f sample h hz hu hc hb0 ε,he]

lemma tendsto_physicalValue_killed_general (hκ : 0 < κ ∧ κ < 8) :
    Tendsto (fun n : ℕ => ENNReal.ofReal ((Cs n).physicalValue κ B γ ε sample)) atTop
      (𝓝 (physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z ε)) := by
  by_cases he : firstLiveDistanceStop (γ sample) z ε = ⊤
  · rw [physicalStoppedDensity,he,ite_eq_left rfl]
    have ha : 0 < 8/κ-1 := sub_pos.2 ((lt_div_iff₀ hκ.1).2 (by simpa using hκ.2))
    have hlim := hCs.rpow_const_nhds_zero ha
    have hlim' : Tendsto (fun n : ℕ => ((2*z.im)*Real.exp (-u))^(-(1-κ/8)) *
        ((Cs n).angle)^(8/κ-1)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hlim
    have hl : Tendsto (fun n : ℕ => (Cs n).physicalValue κ B γ ε sample) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => (Cs n).physicalValue_nonneg κ B γ ε sample) _ hlim'
      intro n
      let C := Cs n
      have ht : C.physicalTime κ B γ ε sample = C.stopTime κ B sample := by
        simp only [Cutoff.physicalTime,PhysicalStop.cap,he,ite_true]
      have hv : C.physicalValue κ B γ ε sample = C.value κ B sample := by
        simp only [Cutoff.physicalValue,ht,Cutoff.value]
      rw [hv]
      have hs : loewnerAngleSine κ (fun t => B t sample) (g sample) (C.stopTime κ B sample) z = C.angle := by
        rcases C.source_terminal κ B sample h hz hu hc hb0 with hr | hs
        · have hh := h.radius_ge_before_distance_stop hε hsmall
            (t := ⟨C.stopTime κ B sample,(C.bounds κ B sample).1⟩)
            (by rw [he]; exact le_top) (C.source_live κ B sample h hz hu hc hb0)
          change ε/4 ≤ loewnerRadius (g sample) (C.stopTime κ B sample) z at hh
          rw [hr] at hh
          exact False.elim ((not_lt_of_ge hh) hρ)
        · exact hs
      exact C.angle_exit_bound κ B sample h hz hu hc hb0 hκ hs
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hl
  · have hh := eventually_physicalValue_at_hit_general κ B γ g f sample h hz hu hc hb0 hε hsmall hρ Cs hCs he
    exact tendsto_const_nhds.congr' (hh.mono (fun _ heq => heq.symm))

end SLEExactGauge.FiniteTilt

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.JointStopped
open LoewnerCutoff

def good {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I,ℝ)) (z : ℂ) (t : ℝ) : Prop :=
  t ∈ Icc 0 T ∧ ∀ q : I, ε ≤ (position hε hT U z (t*q)).im

lemma good_height {ε T t : ℝ} {hε : 0 < ε} {hT : 0 ≤ T}
    {U : C(I,ℝ)} {z : ℂ} (hg : good hε hT U z t) :
    ∀ s ∈ Icc 0 t, ε ≤ (position hε hT U z s).im := by
  intro s hs
  by_cases ht : t = 0
  · have hz : s=0 := le_antisymm (ht ▸ hs.2) hs.1
    simpa only [ht,hz,zero_mul] using hg.2 (0:I)
  · have htp : 0 < t := lt_of_le_of_ne hg.1.1 (Ne.symm ht)
    let q : I := ⟨s/t,⟨div_nonneg hs.1 hg.1.1,(div_le_one htp).2 hs.2⟩⟩
    have he : t*(q:ℝ) = s := mul_div_cancel₀ _ ht
    simpa only [he] using hg.2 q

lemma good_closed {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) :
    IsClosed {p : (C(I,ℝ) × ℂ) × ℝ | good hε hT p.1.1 p.1.2 p.2} := by
  have ht : IsClosed {p : (C(I,ℝ) × ℂ) × ℝ | p.2 ∈ Icc 0 T} := isClosed_Icc.preimage continuous_snd
  simp only [good,ofPred_and,ofPred_forall]
  apply ht.inter
  apply isClosed_iInter
  intro q
  apply isClosed_le continuous_const
  exact Complex.continuous_im.comp ((continuous_mark_position hε hT).comp
    (continuous_fst.prodMk (continuous_snd.mul continuous_const)))

lemma good_live {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (hm : IsLoewnerTraceUsing driver γ g f)
    {ε T t : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I,ℝ)) (z : ℂ) (hU : EqOn (extendDriver T U) driver (Icc 0 T))
    (hg : good hε hT U z t) :
    z ∈ localizationDomain γ t ∧ EqOn (fun s => g s z) (position hε hT U z) (Icc 0 t) := by
  have hd (s : ℝ) (hs : s ∈ Icc 0 t) :
      HasDerivWithinAt (position hε hT U z)
        (velocity ε (driver s) (position hε hT U z s)) (Icc 0 t) s := by
    have hsT : s ∈ Icc 0 T := ⟨hs.1,hs.2.trans hg.1.2⟩
    rw [← hU hsT]
    exact (position_derivWithin hε hT U z hsT).mono (Icc_subset_Icc le_rfl hg.1.2)
  have hh := hm.cutoff_solution_live hε hg.1.1 hd (good_height hg)
  simpa only [position_initial] using hh

lemma good_of_live {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    {ε T t : ℝ} (hm : IsLoewnerTraceUsing driver γ g f) (hc : ContinuousOn driver (Icc 0 T))
    (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I,ℝ)) (z : ℂ) (hU : EqOn (extendDriver T U) driver (Icc 0 T))
    (ht : t ∈ Icc 0 T) (hz : z ∈ localizationDomain γ t) (hheight : ε ≤ (g t z).im) :
    good hε hT U z t := by
  have hh (s : ℝ) (hs : s ∈ Icc 0 t) : ε ≤ (g s z).im :=
    hheight.trans (hm.height_antitone ht.1 hz hs ⟨ht.1,le_rfl⟩ hs.2)
  have hpos (s : ℝ) (hs : s ∈ Icc 0 t) :
      HasDerivWithinAt (position hε hT U z)
        (velocity ε (extendDriver T U s) (position hε hT U z s)) (Icc 0 t) s :=
    (position_derivWithin hε hT U z ⟨hs.1,hs.2.trans ht.2⟩).mono (Icc_subset_Icc le_rfl ht.2)
  have hsource (s : ℝ) (hs : s ∈ Icc 0 t) :
      HasDerivWithinAt (fun r => g r z) (velocity ε (extendDriver T U s) (g s z)) (Icc 0 t) s := by
    rw [velocity_eq (hh s hs),hU ⟨hs.1,hs.2.trans ht.2⟩]
    exact hm.hasDerivWithinAt_eval ht.1 (hc.mono (Icc_subset_Icc le_rfl ht.2)) hz hs
  have he := solution_eq hε hpos hsource (by rw [position_initial,hm.initial z hz.1.1])
  refine ⟨ht,fun q => ?_⟩
  have hs : t*(q:ℝ) ∈ Icc 0 t := ⟨mul_nonneg ht.1 q.property.1,by simpa only [mul_one] using mul_le_mul_of_nonneg_left q.property.2 ht.1⟩
  rw [he hs]
  exact hh _ hs

lemma log_of_good {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    {ε T t : ℝ} (hm : IsLoewnerTraceUsing driver γ g f) (hc : ContinuousOn driver (Icc 0 T))
    (hε : 0 < ε) (hT : 0 ≤ T)
    (U : C(I,ℝ)) (z : ℂ) (hU : EqOn (extendDriver T U) driver (Icc 0 T))
    (hg : good hε hT U z t) :
    logDerivative hε hT U z t = Real.log ‖deriv (g t) z‖ := by
  have hl := good_live hm hε hT U z hU hg
  have hct := hc.mono (Icc_subset_Icc le_rfl hg.1.2)
  rw [logDerivative_eq_integral hε hT U z hg.1,hm.log_deriv_norm_eq hg.1.1 hct hl.1]
  have hi := (hm.continuous_spatialCoefficient hg.1.1 hct hl.1).intervalIntegrable_of_Icc (μ := volume) hg.1.1
  rw [← Complex.reCLM_apply,← Complex.reCLM.intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hg.1.1] at hs
  unfold variation
  rw [clampIm_eq (by simpa using good_height hg s hs),← hl.2 hs,hU ⟨hs.1,hs.2.trans hg.1.2⟩]
  rfl

end SLEExactGauge.JointStopped

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.JointStopped
open LoewnerCutoff
local instance meshExponentsGreenRealMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _
local instance meshExponentsGreenRealBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩

lemma field_good {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    {ε T t : ℝ} (hm : IsLoewnerTraceUsing driver γ g f) (hc : ContinuousOn driver (Icc 0 T))
    (hε : 0 < ε) (hT : 0 ≤ T) (p a : ℝ)
    (U : C(I,ℝ)) (z : ℂ) (hU : EqOn (extendDriver T U) driver (Icc 0 T))
    (hg : good hε hT U z t) :
    LoewnerField.field hε hT p a 1 U z t (extendDriver T U t) =
      (loewnerRadius g t z)^(-p)*((g t z).im/‖g t z-(driver t:ℂ)‖)^a := by
  have hl := good_live hm hε hT U z hU hg
  have hy : ε ≤ (position hε hT U z t).im := good_height hg t ⟨hg.1.1,le_rfl⟩
  rw [LoewnerField.field,GreenPhysical.green_eq_source _ _ _ _ _ (LoewnerField.height_pos hε hT U z t),
    LoewnerField.height,max_eq_right hy,log_of_good hm hc hε hT U z hU hg,
    Real.exp_log (norm_pos_iff.2 (hm.deriv_ne_zero hg.1.1 hl.1)),← hl.2 ⟨hg.1.1,le_rfl⟩,
    hU hg.1,one_mul]
  simp only [loewnerRadius,Complex.norm_def,Complex.normSq_apply,Complex.sub_re,
    Complex.ofReal_re,Complex.sub_im,Complex.ofReal_im,sub_zero,pow_two]

def killedGreen (driver : ℝ → ℝ) (γ : ℝ → ℂ) (g : ℝ → ℂ → ℂ)
    (p a : ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  if z ∈ localizationDomain γ t then
    (loewnerRadius g t z)^(-p)*((g t z).im/‖g t z-(driver t:ℂ)‖)^a else 0

def greenApprox {T : ℝ} (hT : 0 ≤ T) (p a : ℝ) (n : ℕ)
    (q : (C(I,ℝ) × ℂ) × ℝ) : ℝ :=
  if good (show 0 < 1/((n:ℝ)+1) by positivity) hT q.1.1 q.1.2 q.2 then
    LoewnerField.field (show 0 < 1/((n:ℝ)+1) by positivity) hT p a 1 q.1.1 q.1.2 q.2
      (extendDriver T q.1.1 q.2) else 0

lemma measurable_greenApprox {T : ℝ} (hT : 0 ≤ T) (p a : ℝ) (n : ℕ) :
    Measurable (greenApprox hT p a n) := by
  unfold greenApprox
  exact Measurable.ite (good_closed (show 0 < 1/((n:ℝ)+1) by positivity) hT).measurableSet
    (continuous_mark_green (show 0 < 1/((n:ℝ)+1) by positivity) hT p a).measurable measurable_const

lemma eventually_greenApprox {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    {T t : ℝ} (hm : IsLoewnerTraceUsing driver γ g f) (hc : ContinuousOn driver (Icc 0 T))
    (hT : 0 ≤ T) (p a : ℝ) (U : C(I,ℝ)) (z : ℂ)
    (hU : EqOn (extendDriver T U) driver (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    ∀ᶠ n : ℕ in atTop, greenApprox hT p a n ((U,z),t) = killedGreen driver γ g p a z t := by
  classical
  by_cases hz : z ∈ localizationDomain γ t
  · have hp := hm.im_pos ht.1 hz
    have hlim : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hlim.eventually (gt_mem_nhds hp)] with n hn
    have hg := good_of_live hm hc (show 0 < 1/((n:ℝ)+1) by positivity) hT U z hU ht hz hn.le
    rw [greenApprox,ite_eq_left hg,killedGreen,ite_eq_left hz]
    exact field_good hm hc _ hT p a U z hU hg
  · apply Filter.Eventually.of_forall
    intro n
    have hn : ¬ good (show 0 < 1/((n:ℝ)+1) by positivity) hT U z t :=
      fun hg => hz (good_live hm _ hT U z hU hg).1
    simp only [greenApprox,hn,ite_false,killedGreen,hz]

def observedGreen {T : ℝ} (hT : 0 ≤ T) (p a : ℝ) (q : (C(I,ℝ) × ℂ) × ℝ) : ℝ :=
  ContinuousDriver.selectedLimit 0 (fun n => greenApprox hT p a n q)

lemma measurable_observedGreen {T : ℝ} (hT : 0 ≤ T) (p a : ℝ) :
    Measurable (observedGreen hT p a) :=
  ContinuousDriver.measurable_selectedLimit 0 _ (fun n => measurable_greenApprox hT p a n)

lemma observedGreen_eq {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    {T t : ℝ} (hm : IsLoewnerTraceUsing driver γ g f) (hc : ContinuousOn driver (Icc 0 T))
    (hT : 0 ≤ T) (p a : ℝ) (U : C(I,ℝ)) (z : ℂ)
    (hU : EqOn (extendDriver T U) driver (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    observedGreen hT p a ((U,z),t) = killedGreen driver γ g p a z t := by
  apply ContinuousDriver.selectedLimit_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_greenApprox hm hc hT p a U z hU ht] with n hn
  exact hn.symm

end SLEExactGauge.JointStopped

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.JointStopped
open LoewnerCutoff
local instance meshExponentsObservedRealMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _
local instance meshExponentsObservedRealBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩
local instance meshExponentsObservedComplexMeasurableSpace : MeasurableSpace C(I,ℂ) := borel _
local instance meshExponentsObservedComplexBorelSpace : BorelSpace C(I,ℂ) := ⟨rfl⟩

def observedPhysical {T : ℝ} (hT : 0 ≤ T) (p a e : ℝ)
    (q : (C(I,ℝ) × C(I,ℂ)) × ℂ) : ℝ≥0∞ :=
  if CompactHit.hits e (q.1.2,q.2) then
    ENNReal.ofReal (observedGreen hT p a ((q.1.1,q.2),CompactHit.realTime T e q.1.2 q.2)) else 0

lemma measurable_observedPhysical {T : ℝ} (hT : 0 ≤ T) (p a e : ℝ) :
    Measurable (observedPhysical hT p a e) := by
  have hv : Measurable (fun q : (C(I,ℝ) × C(I,ℂ)) × ℂ => (q.1.2,q.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have ht : Measurable (fun q : (C(I,ℝ) × C(I,ℂ)) × ℂ => CompactHit.realTime T e q.1.2 q.2) :=
    measurable_const.mul (measurable_subtype_coe.comp ((CompactHit.measurable_time e).comp hv))
  apply Measurable.ite ((CompactHit.hits_closed e).measurableSet.preimage hv)
  · exact ENNReal.measurable_ofReal.comp ((measurable_observedGreen hT p a).comp
      ((measurable_fst.fst.prodMk measurable_snd).prodMk ht))
  · exact measurable_const

lemma observedPhysical_eq {κ : ℝ} {B : ℝ≥0 → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    {T : ℝ} (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal) γ g f)
    (hc : ContinuousOn (fun t => Real.sqrt κ*B t.toNNReal) (Icc 0 T))
    (hT : 0 < T) (e : ℝ) (U : C(I,ℝ)) (V : C(I,ℂ)) (z : ℂ)
    (hU : EqOn (extendDriver T U) (fun t => Real.sqrt κ*B t.toNNReal) (Icc 0 T))
    (hV : ∀ q : I, V q = γ (T*q)) :
    observedPhysical hT.le (codimension κ) (8/κ-1) e ((U,V),z) =
      if firstLiveDistanceStop γ z e ≤ ENNReal.ofReal T then
        physicalStoppedDensity κ B γ g z e else 0 := by
  classical
  have heq := CompactHit.live_byTime_iff hT V γ z hm.1 hV (e := e)
  have hg := observedGreen_eq hm hc hT.le (codimension κ) (8/κ-1) U z hU
    (CompactHit.realTime_bounds hT.le e V z)
  unfold observedPhysical
  by_cases hh : CompactHit.hits e (V,z)
  · rw [ite_eq_left hh,hg]
    by_cases hl : z ∈ localizationDomain γ (CompactHit.realTime T e V z)
    · have hstop := CompactHit.realTime_stop hT V γ z hV hh hl
      rw [ite_eq_left (heq.2 ⟨hh,hl⟩),physicalStoppedDensity,hstop,ite_eq_right ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (CompactHit.realTime_bounds hT.le e V z).1,
        killedGreen,ite_eq_left hl]
      simp only [loewnerAngleSine,Complex.ofReal_mul]
    · rw [ite_eq_right (fun h => hl (heq.1 h).2),killedGreen,ite_eq_right hl,ENNReal.ofReal_zero]
  · rw [ite_eq_right hh,ite_eq_right (fun h => hh (heq.1 h).1)]

end SLEExactGauge.JointStopped

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.ContinuousDriver
local instance meshExponentsDriverRealMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _
local instance meshExponentsDriverRealBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩
local instance meshExponentsDriverComplexMeasurableSpace : MeasurableSpace C(I,ℂ) := borel _
local instance meshExponentsDriverComplexBorelSpace : BorelSpace C(I,ℂ) := ⟨rfl⟩

def complexParts (p : C(I,ℝ) × C(I,ℝ)) : C(I,ℂ) :=
  ⟨fun q => (p.1 q:ℂ)+(p.2 q:ℂ)*Complex.I,
    (Complex.continuous_ofReal.comp p.1.continuous).add
      ((Complex.continuous_ofReal.comp p.2.continuous).mul continuous_const)⟩

lemma continuous_complexParts : Continuous complexParts := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (Complex.continuous_ofReal.comp (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd))).add
    ((Complex.continuous_ofReal.comp (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd))).mul continuous_const)

def complexPath (x : I → ℂ) : C(I,ℂ) :=
  complexParts (path (fun q => (x q).re),path (fun q => (x q).im))

lemma complexPath_eval {x : I → ℂ} (hx : Continuous x) (q : I) : complexPath x q = x q := by
  change (path (fun q => (x q).re) q:ℂ)+(path (fun q => (x q).im) q:ℂ)*Complex.I = x q
  rw [path_eval_of_continuous (show Continuous (fun q => (x q).re) from Complex.continuous_re.comp hx),
    path_eval_of_continuous (show Continuous (fun q => (x q).im) from Complex.continuous_im.comp hx)]
  exact Complex.re_add_im _

lemma aemeasurable_complexPath {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (x : Ω → I → ℂ) (hx : ∀ q, AEMeasurable (fun sample => x sample q) P) :
    AEMeasurable (fun sample => complexPath (x sample)) P := by
  exact continuous_complexParts.measurable.comp_aemeasurable
    ((aemeasurable_path (fun sample q => (x sample q).re) (fun q => Complex.measurable_re.comp_aemeasurable (hx q))).prodMk
    (aemeasurable_path (fun sample q => (x sample q).im) (fun q => Complex.measurable_im.comp_aemeasurable (hx q))))

lemma exists_measurable_trace_path {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (γ : Ω → ℝ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hc : ∀ᵐ sample ∂P, ContinuousOn (γ sample) (Ici 0))
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ V : Ω → C(I,ℂ), Measurable V ∧ ∀ᵐ sample ∂P, ∀ q : I, V sample q = γ sample (T*q) := by
  let V₀ := fun sample => complexPath (fun q : I => γ sample (T*q))
  have hV : AEMeasurable V₀ P := aemeasurable_complexPath _ (fun q => hγ _ (mul_nonneg hT q.property.1))
  refine ⟨hV.mk V₀,hV.measurable_mk,?_⟩
  filter_upwards [hV.ae_eq_mk,hc] with sample he hcont
  intro q
  rw [← he]
  apply complexPath_eval
  exact hcont.comp_continuous (continuous_const.mul continuous_subtype_val) (fun q => mul_nonneg hT q.property.1)

end SLEExactGauge.ContinuousDriver

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge
local instance meshExponentsJointRealMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _
local instance meshExponentsJointRealBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩
local instance meshExponentsJointComplexMeasurableSpace : MeasurableSpace C(I,ℂ) := borel _
local instance meshExponentsJointComplexBorelSpace : BorelSpace C(I,ℂ) := ⟨rfl⟩

theorem jointFiniteTimePhysicalDensity {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (_hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (T : ℝ) (hT : 0 < T) (e : ℝ) (_he : 0 < e) :
    ∃ W : Ω × ℂ → ℝ≥0∞, Measurable W ∧ ∀ᵐ sample ∂P, ∀ z : ℂ,
      W (sample,z) = if firstLiveDistanceStop (γ sample) z e ≤ ENNReal.ofReal T
        then physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z e
        else 0 := by
  have hcont : ∀ᵐ sample ∂P, ContinuousOn (γ sample) (Ici 0) := hmaps.mono (fun _ hm => hm.1)
  obtain ⟨V,hVm,hVe⟩ := ContinuousDriver.exists_measurable_trace_path γ hγ hcont T hT.le
  let S : ℝ≥0 := ⟨T,hT.le⟩
  have hu := BrownianDriver.path_aemeasurable hB (Real.sqrt κ) S
  let U := hu.mk (BrownianDriver.path B (Real.sqrt κ) S)
  have hUm : Measurable U := hu.measurable_mk
  let W := fun q : Ω × ℂ => JointStopped.observedPhysical hT.le (codimension κ) (8/κ-1) e
    ((U q.1,V q.1),q.2)
  refine ⟨W,?_,?_⟩
  · exact (JointStopped.measurable_observedPhysical hT.le (codimension κ) (8/κ-1) e).comp
      (((hUm.comp measurable_fst).prodMk (hVm.comp measurable_fst)).prodMk measurable_snd)
  · filter_upwards [hmaps,hB.cont,hu.ae_eq_mk,hVe] with sample hm hb huEq hvEq
    change BrownianDriver.path B (Real.sqrt κ) S sample = U sample at huEq
    intro z
    apply JointStopped.observedPhysical_eq (κ := κ) (B := fun t => B t sample) hm
      (continuous_const.mul (hb.comp continuous_real_toNNReal)).continuousOn hT e (U sample) (V sample) z _ hvEq
    intro t ht
    rw [← huEq]
    exact BrownianDriver.extend_eq B (Real.sqrt κ) S sample hb ht

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

theorem jointPhysicalDensity {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun ω => γ ω t) P)
    (hmaps : ∀ᵐ ω ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (e : ℝ) (he : 0 < e) :
    ∃ W : Ω × ℂ → ℝ≥0∞, Measurable W ∧ ∀ᵐ ω ∂P, ∀ z,
      W (ω,z) = physicalStoppedDensity κ (fun t => B t ω) (γ ω) (g ω) z e := by
  choose W hW hWe using (fun n : ℕ => jointFiniteTimePhysicalDensity κ hκ B hB γ g f hγ hmaps
    ((n:ℝ)+1) (by positivity) e he)
  refine ⟨fun q => ⨆ n, W n q,Measurable.iSup hW,?_⟩
  filter_upwards [ae_all_iff.2 hWe] with ω hω z
  simp only [hω]
  by_cases ht : firstLiveDistanceStop (γ ω) z e = ⊤
  · simp only [physicalStoppedDensity,ht,ite_true,ite_self,iSup_const]
  · have hf := ENNReal.ofReal_toReal ht
    obtain ⟨n,hn⟩ := exists_nat_gt (firstLiveDistanceStop (γ ω) z e).toReal
    have hb : firstLiveDistanceStop (γ ω) z e ≤ ENNReal.ofReal ((n:ℝ)+1) := by
      rw [← hf]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    apply le_antisymm
    · apply iSup_le
      intro m
      split_ifs
      · exact le_rfl
      · exact zero_le
    · exact le_iSup_of_le n (by rw [ite_eq_left hb])

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.MeshSlab
open FiniteTilt
local instance meshExponentsDensityRealMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _
local instance meshExponentsDensityRealBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩
local instance meshExponentsDensityComplexMeasurableSpace : MeasurableSpace C(I,ℂ) := borel _
local instance meshExponentsDensityComplexBorelSpace : BorelSpace C(I,ℂ) := ⟨rfl⟩

lemma physicalStoppedDensity_ne_top (κ : ℝ) (B : ℝ≥0 → ℝ) (γ : ℝ → ℂ)
    (g : ℝ → ℂ → ℂ) (z : ℂ) (e : ℝ) : physicalStoppedDensity κ B γ g z e ≠ ⊤ := by
  simp only [physicalStoppedDensity]
  split_ifs <;> simp

lemma physicalValue_real_tendsto {Ω : Type*}
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ → ℂ)
    (g f : Ω → ℝ → ℂ → ℂ) (ω : Ω)
    (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    {z : ℂ} (hz : z ∈ halfPlane) {u : ℝ} (hu : 0 < u)
    (hc : Continuous (fun t => B t ω)) (hb0 : B 0 ω = 0)
    {e : ℝ} (he : 0 < e) (hes : e < z.im)
    (hr : (2*z.im)*Real.exp (-u) < e/4)
    (Cs : ℕ → Cutoff z u) (hCs : Tendsto (fun n => (Cs n).angle) atTop (𝓝 0)) :
    Tendsto (fun n => (Cs n).physicalValue κ B γ e ω) atTop
      (𝓝 (physicalStoppedDensity κ (fun t => B t ω) (γ ω) (g ω) z e).toReal) := by
  have hh := tendsto_physicalValue_killed_general κ B γ g f ω hm hz hu hc hb0 he hes hr Cs hCs hκ
  have ht := (ENNReal.continuousAt_toReal (physicalStoppedDensity_ne_top κ (fun t => B t ω)
    (γ ω) (g ω) z e)).tendsto.comp hh
  simpa only [Function.comp_def,ENNReal.toReal_ofReal ((Cs _).physicalValue_nonneg κ B γ e ω)] using ht

lemma exponential_bound_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hX : ∀ n, AEMeasurable (X n) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (K θ : ℝ)
    (hb : ∀ n, (∫⁻ ω, ENNReal.ofReal (Real.exp (θ*X n ω)) ∂P) ≤ ENNReal.ofReal (Real.exp K)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ*Y ω)) ∂P) ≤ ENNReal.ofReal (Real.exp K) := by
  have hm (n : ℕ) := ((hX n).const_mul θ).exp.ennreal_ofReal
  have hl : ∀ᵐ ω ∂P, Tendsto (fun n => ENNReal.ofReal (Real.exp (θ*X n ω))) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (θ*Y ω)))) := by
    filter_upwards [hlim] with ω hω
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Real.continuous_exp.continuousAt.tendsto.comp (hω.const_mul θ))
  calc
    _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (Real.exp (θ*X n ω))) atTop ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hl] with ω hω
      exact hω.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (Real.exp (θ*X n ω)) ∂P) atTop := lintegral_liminf_le' hm
    _ ≤ _ := liminf_le_of_frequently_le (Filter.Eventually.frequently (Filter.Eventually.of_forall hb))

lemma common_slab_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A : Set ℂ} {u : ℂ → ℝ} (Cs : ℕ → CommonCutoff A u)
    (hCs : Tendsto (fun n => (Cs n).angle) atTop (𝓝 0))
    (hA : MeasurableSet A) [IsFiniteMeasure (volume.restrict A)]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ ω ∂P, IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
    (hhalf : ∀ z ∈ A, z ∈ halfPlane) (hu : ∀ z ∈ A, 0 < u z)
    {ρ : ℝ} (hr : ∀ z ∈ A, (2*z.im)*Real.exp (-u z) = ρ)
    (V : ℕ → Ω → C(I,ℂ)) (hVm : ∀ n, Measurable (V n))
    (hV : ∀ n, ∀ᵐ ω ∂P, ∀ q : I, V n ω q = γ ω (((Cs n).horizon:ℝ)*q))
    (e r : ℝ) (he : 0 < e) (her : e ≤ r) (hrs : ∀ z ∈ A, r < z.im) (hρ : ρ < e/4) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∫ z in A,
      observedDifference (Cs n).height_pos (Cs n).horizon.coe_nonneg κ ρ (Cs n).angle e r
        ((BrownianDriver.path B (Real.sqrt κ) (Cs n).horizon ω,V n ω),z)) atTop
      (𝓝 (∫ z in A, (physicalStoppedDensity κ (fun t => B t ω) (γ ω) (g ω) z e).toReal -
        (physicalStoppedDensity κ (fun t => B t ω) (γ ω) (g ω) z r).toReal)) := by
  let F := fun n (q : Ω × ℂ) => observedDifference (Cs n).height_pos (Cs n).horizon.coe_nonneg κ ρ (Cs n).angle e r
    ((BrownianDriver.path B (Real.sqrt κ) (Cs n).horizon q.1,V n q.1),q.2)
  have hm (n : ℕ) : AEStronglyMeasurable (F n) (P.prod (volume.restrict A)) :=
    (observedDifference_aemeasurable hB _ (Cs n).height_pos κ ρ (Cs n).angle e r (Cs n).horizon (V n) (hVm n)).aestronglyMeasurable
  have hf (n : ℕ) : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun z => F n (ω,z)) (volume.restrict A) := (hm n).prodMk_left
  filter_upwards [hmaps,hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero,ae_all_iff.2 hV,ae_all_iff.2 hf]
    with ω hw hc hb0 hv hfω
  have heq (n : ℕ) (z : ℂ) (hz : z ∈ A) : F n (ω,z) =
      ((Cs n).at z hz).physicalValue κ B γ e ω - ((Cs n).at z hz).physicalValue κ B γ r ω := by
    dsimp only [F,observedDifference]
    rw [observedValue_eq (Cs n) κ B γ g f ω hw hc hb0 z hz (hhalf z hz) (hu z hz) (hr z hz) (V n ω) (hv n) e,
      observedValue_eq (Cs n) κ B γ g f ω hw hc hb0 z hz (hhalf z hz) (hu z hz) (hr z hz) (V n ω) (hv n) r]
  apply tendsto_integral_of_dominated_convergence (fun _ : ℂ => 2*ρ^(-(1-κ/8))) hfω (integrable_const _)
  · intro n
    filter_upwards [ae_restrict_mem hA] with z hz
    rw [heq n z hz,Real.norm_eq_abs]
    have hn (s : ℝ) := ((Cs n).at z hz).physicalValue_nonneg κ B γ s ω
    have hb (s : ℝ) := ((Cs n).at z hz).physicalValue_bound κ hκ B γ s ω (hhalf z hz) (hu z hz) hc hb0
    rw [hr z hz] at hb
    calc
      _ ≤ |((Cs n).at z hz).physicalValue κ B γ e ω| + |((Cs n).at z hz).physicalValue κ B γ r ω| := abs_sub _ _
      _ ≤ 2*ρ^(-(1-κ/8)) := by rw [abs_of_nonneg (hn e),abs_of_nonneg (hn r)]; linarith [hb e,hb r]
  · filter_upwards [ae_restrict_mem hA] with z hz
    have hl (s : ℝ) (hs : 0 < s) (hse : s < z.im) (hρs : ρ < s/4) := physicalValue_real_tendsto κ hκ B γ g f ω hw
      (hhalf z hz) (hu z hz) hc hb0 hs hse (by rw [hr z hz]; exact hρs) (fun n => (Cs n).at z hz) hCs
    exact ((hl e he (her.trans_lt (hrs z hz)) hρ).sub (hl r (he.trans_le her) (hrs z hz) (by linarith))).congr
      (fun n => (heq n z hz).symm)

end SLEExactGauge.MeshSlab

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge.FiniteTilt

lemma compact_log_cutoffs {A : Set ℂ} (hA : IsCompact A) (hne : A.Nonempty)
    (hy : ∀ z ∈ A, 1 ≤ z.im) {ρ : ℝ} (hρ : 0 < ρ) (hρs : ρ < 1) :
    ∃ Cs : ℕ → CommonCutoff A (fun z => Real.log (2*z.im/ρ)),
      Tendsto (fun n => (Cs n).angle) atTop (𝓝 0) := by
  have hy0 (z : ℂ) (hz : z ∈ A) : 0 < z.im := lt_of_lt_of_le (by norm_num) (hy z hz)
  have hR (z : ℂ) (hz : z ∈ A) : 1 < 2*z.im/ρ := (lt_div_iff₀ hρ).2 (by linarith [hy z hz])
  have hu (z : ℂ) (hz : z ∈ A) : 0 < Real.log (2*z.im/ρ) := Real.log_pos (hR z hz)
  have huc : ContinuousOn (fun z : ℂ => Real.log (2*z.im/ρ)) A :=
    ((continuous_const.mul Complex.continuous_im).div_const ρ).continuousOn.log (fun z hz => (lt_trans zero_lt_one (hR z hz)).ne')
  have hsc : ContinuousOn (fun z : ℂ => z.im/‖z‖) A := Complex.continuous_im.continuousOn.div
    continuous_norm.continuousOn (fun z hz => norm_ne_zero_iff.2 (by intro he; simpa [he] using hy0 z hz))
  obtain ⟨zH,hzH,hH⟩ := hA.exists_isMaxOn hne Complex.continuous_im.continuousOn
  obtain ⟨zU,hzU,hU⟩ := hA.exists_isMaxOn hne huc
  obtain ⟨zS,hzS,hS⟩ := hA.exists_isMinOn hne hsc
  exact commonCutoffs (hy zH hzH) (hu zU hzU).le (initial_sine_pos (hy0 zS hzS))
    (fun z hz => ⟨hy z hz,hH hz⟩) (fun z hz => ⟨(hu z hz).le,hU hz⟩) (fun z hz => hS hz)

lemma logRadius_pos {z : ℂ} (hz : 1 ≤ z.im) {ρ : ℝ} (hρ : 0 < ρ) (hρs : ρ < 1) :
    0 < Real.log (2*z.im/ρ) := Real.log_pos ((lt_div_iff₀ hρ).2 (by linarith))

lemma logRadius_eq {z : ℂ} (hz : 0 < z.im) {ρ : ℝ} (hρ : 0 < ρ) :
    (2*z.im)*Real.exp (-Real.log (2*z.im/ρ)) = ρ := by
  rw [Real.exp_neg,Real.exp_log (by positivity)]
  field_simp

lemma collar_height {z₀ : ℂ} (hcollar : closedBall z₀ 2 ⊆ halfPlane) :
    ∀ z ∈ closedBall z₀ 1, 1 ≤ z.im := by
  have hbase : 2 < z₀.im := by
    have hm : z₀-2*Complex.I ∈ closedBall z₀ 2 := by
      rw [mem_closedBall,dist_eq_norm]
      simp
    have hh := hcollar hm
    change 0 < (z₀-2*Complex.I).im at hh
    norm_num at hh
    linarith
  intro z hz
  have hd := mem_closedBall.1 hz
  have hi := Complex.abs_im_le_norm (z-z₀)
  rw [Complex.sub_im,← dist_eq_norm] at hi
  have hlo := neg_le_abs (z.im-z₀.im)
  linarith

end SLEExactGauge.FiniteTilt

end

end

section
noncomputable section
open Set Filter Metric MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.MeshSlab
open FiniteTilt
local instance meshExponentsMgfRealMeasurableSpace : MeasurableSpace C(I,ℝ) := borel _
local instance meshExponentsMgfRealBorelSpace : BorelSpace C(I,ℝ) := ⟨rfl⟩
local instance meshExponentsMgfComplexMeasurableSpace : MeasurableSpace C(I,ℂ) := borel _
local instance meshExponentsMgfComplexBorelSpace : BorelSpace C(I,ℂ) := ⟨rfl⟩

theorem physical_slab_mgf :
    ∃ J : ℝ, 0 < J ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {A : Set ℂ}, IsCompact A → A.Nonempty → (∀ z ∈ A, 1 ≤ z.im) →
      ∀ (κ : ℝ), 0 < κ ∧ κ ≤ 4 → ∀ (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
      ∀ (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ),
      (∀ t, 0 ≤ t → AEMeasurable (fun ω => γ ω t) P) →
      (∀ᵐ ω ∂P, IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω)) →
      ∀ e r : ℝ, 0 < e → e ≤ r → r < 1 → ∀ θ : ℝ,
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ*(∫ z in A,
        (physicalStoppedDensity κ (fun t => B t ω) (γ ω) (g ω) z e).toReal -
        (physicalStoppedDensity κ (fun t => B t ω) (γ ω) (g ω) z r).toReal))) ∂P) ≤
      ENNReal.ofReal (Real.exp (θ^2*(2*(Real.sqrt κ*(8/κ-1)*(e/4)^(-(1-κ/8)))^2*
        (J*r^2)*(volume A).toReal)/2)) := by
  obtain ⟨J,hJ,hJb⟩ := Mesh.loewner_boundary_layer
  refine ⟨J,hJ,?_⟩
  intro Ω m P hP A hA hne hy κ hκ B hB γ g f hγ hmaps e r he her hr θ
  have hκ' : 0 < κ ∧ κ < 8 := ⟨hκ.1,by linarith [hκ.2]⟩
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.2 hA.measure_lt_top.ne
  let ρ := e/8
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρs : ρ < 1 := by dsimp [ρ]; linarith
  obtain ⟨Cs,hCs⟩ := compact_log_cutoffs hA hne hy hρ hρs
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (γ ω) (Ici 0) := hmaps.mono (fun _ hw => hw.1)
  choose V hVm hV using (fun n => ContinuousDriver.exists_measurable_trace_path γ hγ hcont
    ((Cs n).horizon:ℝ) (Cs n).horizon.coe_nonneg)
  have hh (z : ℂ) (hz : z ∈ A) : z ∈ halfPlane := lt_of_lt_of_le zero_lt_one (hy z hz)
  have hu (z : ℂ) (hz : z ∈ A) : 0 < Real.log (2*z.im/ρ) := logRadius_pos (hy z hz) hρ hρs
  have hrad (z : ℂ) (hz : z ∈ A) : (2*z.im)*Real.exp (-Real.log (2*z.im/ρ)) = ρ := logRadius_eq (hh z hz) hρ
  let X := fun n ω => ∫ z in A, observedDifference (Cs n).height_pos (Cs n).horizon.coe_nonneg κ ρ (Cs n).angle e r
    ((BrownianDriver.path B (Real.sqrt κ) (Cs n).horizon ω,V n ω),z)
  have hXm (n : ℕ) : AEMeasurable (X n) P :=
    (observedDifference_aemeasurable hB (volume.restrict A) (Cs n).height_pos κ ρ (Cs n).angle e r
      (Cs n).horizon (V n) (hVm n)).aestronglyMeasurable.integral_prod_right'.aemeasurable
  have hlim := common_slab_limit Cs hCs hA.measurableSet κ hκ' B hB γ g f hmaps hh hu hrad
    V hVm hV e r he her (fun z hz => hr.trans_le (hy z hz)) (by dsimp [ρ]; linarith)
  apply exponential_bound_of_ae_tendsto P X _ hXm hlim _ θ
  intro n
  exact common_slab_mgf (Cs n) hA.measurableSet κ hκ B hB γ g f hmaps hh hu hrad (V n) (hVm n) (hV n)
    e r he her (fun z hz => her.trans_lt (hr.trans_le (hy z hz))) J hJ.le
    (fun ω hw t ht z hz => hJb _ _ _ _ hw t ht z hz r (he.trans_le her)) θ

end SLEExactGauge.MeshSlab

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.MeshSlab

lemma physicalDensity_bound {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (hm : IsLoewnerTraceUsing driver γ g f) (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → ℝ) {z : ℂ} {e : ℝ} (he : 0 < e) (hes : e < z.im) :
    (physicalStoppedDensity κ B γ g z e).toReal ≤ (e/4)^(-codimension κ) := by
  by_cases hf : firstLiveDistanceStop γ z e = ⊤
  · simp only [physicalStoppedDensity,hf,ite_true,ENNReal.toReal_zero]
    positivity
  obtain ⟨t,ht,hzt,hd,hmin⟩ := PhysicalStop.finite_spec hm.1 hf
  have hR := hm.radius_ge_before_distance_stop he hes (t := t) (by rw [ht]) hzt
  have hp : 0 ≤ codimension κ := by unfold codimension dimension; linarith [hκ.2]
  have ha : 0 ≤ 8/κ-1 := by have hh : (1:ℝ) ≤ 8/κ := (le_div_iff₀ hκ.1).2 (by simpa using hκ.2.le); linarith
  have hy := hm.im_pos t.coe_nonneg hzt
  let w := g t z - (Real.sqrt κ*B t : ℂ)
  have hwi : w.im = (g t z).im := by simp [w]
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 (by intro hh; have hi := congrArg Complex.im hh; rw [hwi] at hi; simpa using hy.ne' hi)
  have hs0 : 0 ≤ loewnerAngleSine κ B g t z := by unfold loewnerAngleSine; positivity
  have hs1 : loewnerAngleSine κ B g t z ≤ 1 := by
    simp only [loewnerAngleSine,Real.toNNReal_coe]
    change (g t z).im / ‖w‖ ≤ 1
    apply (div_le_one hwn).2
    rw [← hwi]
    exact Complex.im_le_norm w
  have hs := Real.rpow_le_one hs0 hs1 ha
  have hR0 : 0 < loewnerRadius g t z := (by positivity : 0 < e/4).trans_le hR
  have hrpow := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < e/4) hR (neg_nonpos.2 hp)
  have hv0 : 0 ≤ loewnerRadius g t z ^ (-codimension κ) * loewnerAngleSine κ B g t z ^ (8/κ-1) := by positivity
  rw [physicalStoppedDensity,ht,ite_eq_right ENNReal.coe_ne_top,ENNReal.coe_toReal,ENNReal.toReal_ofReal hv0]
  exact (mul_le_of_le_one_right (Real.rpow_nonneg hR0.le _) hs).trans hrpow

def physicalMass {Ω : Type*} (A : Set ℂ) (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g : Ω → ℝ → ℂ → ℂ) (e : ℝ) (ω : Ω) : ℝ :=
  ∫ z in A, (physicalStoppedDensity κ (fun t => B t ω) (γ ω) (g ω) z e).toReal

lemma physicalMass_nonneg {Ω : Type*} (A : Set ℂ) (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g : Ω → ℝ → ℂ → ℂ) (e : ℝ) (ω : Ω) :
    0 ≤ physicalMass A κ B γ g e ω := integral_nonneg (fun _ => ENNReal.toReal_nonneg)

end SLEExactGauge.MeshSlab

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.MeshSlab
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable (A : Set ℂ) [sfiniteVolume : SFinite (volume.restrict A)]
variable (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
variable (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
variable (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun ω => γ ω t) P)
variable (hmaps : ∀ᵐ ω ∂P, IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω))
variable (e : ℝ) (he : 0 < e)
include hκ hB hγ hmaps he

lemma physicalMass_aemeasurable : AEMeasurable (physicalMass A κ B γ g e) P := by
  obtain ⟨W,hW,hWe⟩ := jointPhysicalDensity κ hκ B hB γ g f hγ hmaps e he
  apply (hW.ennreal_toReal.stronglyMeasurable.integral_prod_right' (ν := volume.restrict A)).aemeasurable.congr
  filter_upwards [hWe] with ω hw
  exact integral_congr_ae (Filter.Eventually.of_forall (fun z => congrArg ENNReal.toReal (hw z)))

omit sfiniteVolume in
lemma physicalDensity_integrable [SFinite (volume.restrict A)] [IsFiniteMeasure (volume.restrict A)] (hA : MeasurableSet A)
    (hes : ∀ z ∈ A, e < z.im) :
    ∀ᵐ ω ∂P, Integrable (fun z => (physicalStoppedDensity κ (fun t => B t ω) (γ ω) (g ω) z e).toReal) (volume.restrict A) := by
  obtain ⟨W,hW,hWe⟩ := jointPhysicalDensity κ hκ B hB γ g f hγ hmaps e he
  filter_upwards [hWe,hmaps] with ω hw hm
  have hwm : Measurable (fun z => (physicalStoppedDensity κ (fun t => B t ω) (γ ω) (g ω) z e).toReal) := by
    have hh : Measurable (fun z : ℂ => (W (ω,z)).toReal) := hW.ennreal_toReal.comp (measurable_const.prodMk measurable_id)
    convert hh using 1
    funext z
    rw [hw z]
  apply Integrable.of_bound hwm.aestronglyMeasurable ((e/4)^(-codimension κ))
  filter_upwards [ae_restrict_mem hA] with z hz
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  exact physicalDensity_bound hm κ hκ (fun t => B t ω) he (hes z hz)

lemma physicalMass_lintegral [IsFiniteMeasure (volume.restrict A)] (hA : MeasurableSet A)
    (hes : ∀ z ∈ A, e < z.im) :
    ∀ᵐ ω ∂P, ENNReal.ofReal (physicalMass A κ B γ g e ω) =
      ∫⁻ z in A, physicalStoppedDensity κ (fun t => B t ω) (γ ω) (g ω) z e := by
  filter_upwards [physicalDensity_integrable A κ hκ B hB γ g f hγ hmaps e he hA hes] with ω hi
  rw [physicalMass,ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
  apply lintegral_congr
  intro z
  exact ENNReal.ofReal_toReal (physicalStoppedDensity_ne_top _ _ _ _ _ _)

lemma physicalMass_bound [IsFiniteMeasure (volume.restrict A)] (hA : MeasurableSet A)
    (hes : ∀ z ∈ A, e < z.im) :
    ∀ᵐ ω ∂P, physicalMass A κ B γ g e ω ≤ (volume A).toReal*(e/4)^(-codimension κ) := by
  filter_upwards [physicalDensity_integrable A κ hκ B hB γ g f hγ hmaps e he hA hes,hmaps] with ω hi hm
  have hh := integral_mono_ae hi (integrable_const ((e/4)^(-codimension κ))) (μ := volume.restrict A) (by
    filter_upwards [ae_restrict_mem hA] with z hz
    exact physicalDensity_bound hm κ hκ (fun t => B t ω) he (hes z hz))
  simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,physicalMass] using hh

end SLEExactGauge.MeshSlab

end

end

section
noncomputable section
open Set Filter Metric MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.MeshSlab

lemma slab_radius_scale (p : ℝ) {r : ℝ} (hr : 0 < r) :
    (r/8)^(-p)*r = (8:ℝ)^p*r^(1-p) := by
  rw [Real.div_rpow hr.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 8),div_inv_eq_mul,
    show 1-p = 1+(-p) by ring,Real.rpow_add hr,Real.rpow_one]
  ring

theorem slab_mass_mgf (κ : ℝ) (hκ : 0 < κ ∧ κ ≤ 4) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
      ∀ (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ),
      (∀ t, 0 ≤ t → AEMeasurable (fun ω => γ ω t) P) →
      (∀ᵐ ω ∂P, IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal ω) (γ ω) (g ω) (f ω)) →
      ∀ (z₀ : ℂ), closedBall z₀ 2 ⊆ halfPlane → ∀ e r : ℝ,
      0 < e → e ≤ r → r/2 ≤ e → r < 1 → ∀ θ : ℝ,
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ*(physicalMass (closedBall z₀ 1) κ B γ g e ω -
        physicalMass (closedBall z₀ 1) κ B γ g r ω))) ∂P) ≤
      ENNReal.ofReal (Real.exp (θ^2*(K*r^(1-codimension κ))^2/2)) := by
  obtain ⟨J,hJ,hmgf⟩ := physical_slab_mgf
  let L := Real.sqrt κ*(8/κ-1)*(8:ℝ)^(codimension κ)
  have hp : 0 ≤ codimension κ := by unfold codimension dimension; linarith [hκ.2]
  have ha : 0 < 8/κ-1 := sub_pos.2 ((lt_div_iff₀ hκ.1).2 (by linarith [hκ.2]))
  have hL : 0 < L := mul_pos (mul_pos (Real.sqrt_pos.2 hκ.1) ha) (Real.rpow_pos_of_pos (by norm_num) _)
  let K := Real.sqrt (2*J*Real.pi)*L
  have hJπ : 0 < 2*J*Real.pi := by positivity
  refine ⟨K,mul_pos (Real.sqrt_pos.2 hJπ) hL,?_⟩
  intro Ω m P hP B hB γ g f hγ hmaps z₀ hcollar e r he her hel hr θ
  let A := closedBall z₀ (1:ℝ)
  have hAc : IsCompact A := isCompact_closedBall _ _
  have hAm : MeasurableSet A := hAc.measurableSet
  have hy := FiniteTilt.collar_height hcollar
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.2 hAc.measure_lt_top.ne
  have hκ' : 0 < κ ∧ κ < 8 := ⟨hκ.1,by linarith [hκ.2]⟩
  have hh := hmgf hAc (nonempty_closedBall.2 (by norm_num)) hy κ hκ B hB γ g f hγ hmaps e r he her hr θ
  have hIe := physicalDensity_integrable A κ hκ' B hB γ g f hγ hmaps e he hAm
    (fun z hz => her.trans_lt (hr.trans_le (hy z hz)))
  have hIr := physicalDensity_integrable A κ hκ' B hB γ g f hγ hmaps r (he.trans_le her) hAm
    (fun z hz => hr.trans_le (hy z hz))
  have heq : (∫⁻ ω, ENNReal.ofReal (Real.exp (θ*(physicalMass A κ B γ g e ω - physicalMass A κ B γ g r ω))) ∂P) =
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ*(∫ z in A,
        (physicalStoppedDensity κ (fun t => B t ω) (γ ω) (g ω) z e).toReal -
        (physicalStoppedDensity κ (fun t => B t ω) (γ ω) (g ω) z r).toReal))) ∂P) := by
    apply lintegral_congr_ae
    filter_upwards [hIe,hIr] with ω hie hir
    rw [integral_sub hie hir]
    rfl
  rw [heq]
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left _ (sq_nonneg θ)) (by norm_num)
  have hr0 := he.trans_le her
  have hrad := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < r/8) (by linarith : r/8 ≤ e/4) (neg_nonpos.2 hp)
  have hmul : (Real.sqrt κ*(8/κ-1)*(e/4)^(-codimension κ))*r ≤ L*r^(1-codimension κ) := by
    calc
      _ ≤ (Real.sqrt κ*(8/κ-1)*(r/8)^(-codimension κ))*r := by gcongr
      _ = _ := by rw [mul_assoc,slab_radius_scale _ hr0]; dsimp [L]; ring
  have hleft : 0 ≤ (Real.sqrt κ*(8/κ-1)*(e/4)^(-codimension κ))*r := by positivity
  have hsq := pow_le_pow_left₀ hleft hmul 2
  have hv : (volume A).toReal = Real.pi := by
    dsimp [A]
    rw [Complex.volume_closedBall]
    norm_num [ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [hv]
  have hcode : 1-κ/8 = codimension κ := by unfold codimension dimension; ring
  rw [hcode]
  have hmul' := mul_le_mul_of_nonneg_left hsq hJπ.le
  dsimp [K] at *
  have hsqrt := Real.sq_sqrt hJπ.le
  nlinarith

end SLEExactGauge.MeshSlab

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.MeshSlab

lemma finite_mgf_sum {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (t : Finset ι) (Y : ι → Ω → ℝ) (σ : ι → ℝ)
    (hσ : ∀ i ∈ t, 0 < σ i) (hY : ∀ i ∈ t, AEMeasurable (Y i) P)
    (hmgf : ∀ i ∈ t, ∀ θ : ℝ, (∫⁻ ω, ENNReal.ofReal (Real.exp (θ*Y i ω)) ∂P) ≤
      ENNReal.ofReal (Real.exp (θ^2*(σ i)^2/2))) (θ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ*(∑ i ∈ t, Y i ω))) ∂P) ≤
      ENNReal.ofReal (Real.exp (θ^2*(∑ i ∈ t, σ i)^2/2)) := by
  classical
  by_cases ht : t.Nonempty
  · let S := ∑ i ∈ t, σ i
    have hS : 0 < S := Finset.sum_pos (fun i hi => hσ i hi) ht
    let w := fun i => σ i/S
    have hw (i : ι) (hi : i ∈ t) : 0 ≤ w i := (div_pos (hσ i hi) hS).le
    have hw1 : ∑ i ∈ t, w i = 1 := by simp only [w,← Finset.sum_div,S,div_self hS.ne']
    have hpoint (ω : Ω) : Real.exp (θ*(∑ i ∈ t, Y i ω)) ≤
        ∑ i ∈ t, w i * Real.exp ((θ*S/σ i)*Y i ω) := by
      have hh := convexOn_exp.map_sum_le (t := t) (w := w) (p := fun i => (θ*S/σ i)*Y i ω)
        hw hw1 (fun _ _ => mem_univ _)
      have he : (∑ i ∈ t, w i • ((θ*S/σ i)*Y i ω)) = θ*(∑ i ∈ t, Y i ω) := by
        conv_rhs => rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [w]
        field_simp [hS.ne', (hσ i hi).ne']
      rw [he] at hh
      simpa only [smul_eq_mul] using hh
    calc
      _ ≤ ∫⁻ ω, ∑ i ∈ t, ENNReal.ofReal (w i) * ENNReal.ofReal (Real.exp ((θ*S/σ i)*Y i ω)) ∂P := by
        apply lintegral_mono
        intro ω
        calc
          _ ≤ ENNReal.ofReal (∑ i ∈ t, w i * Real.exp ((θ*S/σ i)*Y i ω)) := ENNReal.ofReal_le_ofReal (hpoint ω)
          _ = _ := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg (hw i hi) (Real.exp_pos _).le)]
            apply Finset.sum_congr rfl
            intro i hi
            exact ENNReal.ofReal_mul (hw i hi)
      _ = ∑ i ∈ t, ENNReal.ofReal (w i) * (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ*S/σ i)*Y i ω)) ∂P) := by
        rw [lintegral_finsetSum' _ (fun i hi => ((hY i hi).const_mul _).exp.ennreal_ofReal.const_mul _)]
        apply Finset.sum_congr rfl
        intro i hi
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ∑ i ∈ t, ENNReal.ofReal (w i) * ENNReal.ofReal (Real.exp (θ^2*S^2/2)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := hmgf i hi (θ*S/σ i)
        have he : (θ*S/σ i)^2*(σ i)^2/2 = θ^2*S^2/2 := by field_simp [(hσ i hi).ne']
        rw [he] at hh
        exact mul_le_mul_right hh _
      _ = _ := by
        rw [← Finset.sum_mul,← ENNReal.ofReal_sum_of_nonneg hw,hw1,ENNReal.ofReal_one,one_mul]
  · have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.1 ht
    simp [he]

lemma geo_radius_power {δ : ℝ} (hδ : 0 < δ) (a : ℝ) (n : ℕ) :
    (δ*(1/2:ℝ)^n)^a = δ^a*((1/2:ℝ)^a)^n := by
  rw [Real.mul_rpow hδ.le (by positivity),← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 1/2),
    mul_comm (n:ℝ) a,Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 1/2)]

end SLEExactGauge.MeshSlab

end

end

end OAI
