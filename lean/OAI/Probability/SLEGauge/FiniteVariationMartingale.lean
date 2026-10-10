import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.PostStopPotential

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.FiniteVariationMartingale
open MeshEnergy TaylorVariation
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}
variable {M : ℝ≥0 → Ω → ℝ}

 

lemma integral_weighted_increment (hM : Martingale M ℱ P)
    {s t : ℝ≥0} (hst : s≤t) {H : Ω → ℝ}
    (hm : StronglyMeasurable[ℱ s] H) {L : ℝ}
    (hb : ∀ᵐ ω ∂P, ‖H ω‖≤L) :
    ∫ ω, H ω*(M t ω-M s ω) ∂P = 0 := by
  have hi := (hM.integrable t).sub (hM.integrable s)
  have hprod : Integrable (H*(M t-M s)) P :=
    hi.bdd_mul (hm.mono (ℱ.le s)).aestronglyMeasurable hb
  have hzero : P[M t-M s | ℱ s] =ᵐ[P] 0 := by
    have hc := condExp_sub (hM.integrable t) (hM.integrable s) (ℱ s)
    have hs := condExp_of_stronglyMeasurable (ℱ.le s) (hM.stronglyMeasurable s)
      (hM.integrable s)
    filter_upwards [hc,hM.condExp_ae_eq hst] with ω he ht
    simp only [Pi.sub_apply,hs,ht,sub_self] at he
    exact he
  have hp := condExp_mul_of_stronglyMeasurable_left hm hprod hi
  calc
    _ = ∫ ω, P[H*(M t-M s) | ℱ s] ω ∂P := (integral_condExp (ℱ.le s)).symm
    _ = ∫ ω, (0:ℝ) ∂P := by
      apply integral_congr_ae
      filter_upwards [hp,hzero] with ω he hz
      simpa [hz] using he
    _ = 0 := integral_zero _ _

omit [IsFiniteMeasure P] in
lemma integrable_detector [IsFiniteMeasure P] (hM : Martingale M ℱ P) (t : ℝ≥0) :
    Integrable (fun ω => detector (M t ω)) P :=
  (hM.integrable t).norm.mono'
    (lipschitz_detector.continuous.comp_aestronglyMeasurable
      (hM.integrable t).aestronglyMeasurable)
    (ae_of_all _ fun ω => abs_detector_le (M t ω))

 

theorem ae_eq_zero_at (hM : Martingale M ℱ P)
    (hz : M 0 =ᵐ[P] 0) (C : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => C t ω) (Icc 0 T))
    (hcontrol : ∀ᵐ ω ∂P, ∀ s t, s≤t → t≤T → |M t ω-M s ω|≤C t ω-C s ω)
    (hint : Integrable (fun ω => C T ω-C 0 ω) P) : M T =ᵐ[P] 0 := by
  let H (n i : ℕ) (ω : Ω) := detectorDeriv (M (grid T n i) ω)
  have hm (n i : ℕ) : StronglyMeasurable[ℱ (grid T n i)] (H n i) :=
    lipschitz_detectorDeriv.continuous.comp_stronglyMeasurable (hM.stronglyMeasurable _)
  have hb (n i : ℕ) : ∀ᵐ ω ∂P, ‖H n i ω‖≤1 :=
    ae_of_all _ fun ω => abs_detectorDeriv_le _
  have hi (n i : ℕ) : Integrable
      (fun ω => H n i ω * (M (grid T n (i+1)) ω-M (grid T n i) ω)) P :=
    ((hM.integrable _).sub (hM.integrable _)).bdd_mul
      ((hm n i).mono (ℱ.le _)).aestronglyMeasurable (hb n i)
  have hzero (n i : ℕ) : (∫ ω, H n i ω *
      (M (grid T n (i+1)) ω-M (grid T n i) ω) ∂P)=0 :=
    integral_weighted_increment hM (grid_mono T n (Nat.le_succ i)) (hm n i) (hb n i)
  have hsint (n : ℕ) : Integrable (fun ω => ∑ i ∈ Finset.range (n+1), H n i ω *
      (M (grid T n (i+1)) ω-M (grid T n i) ω)) P :=
    integrable_finsetSum _ fun i _ => hi n i
  have hsz (n : ℕ) : (∫ ω, ∑ i ∈ Finset.range (n+1), H n i ω *
      (M (grid T n (i+1)) ω-M (grid T n i) ω) ∂P)=0 := by
    rw [integral_finsetSum _ (fun i _ => hi n i)]
    simp only [hzero,Finset.sum_const_zero]
  let F (n : ℕ) (ω : Ω) := error detector detectorDeriv (fun t => M t ω) T n
  have hFi (n : ℕ) : Integrable (F n) P :=
    ((integrable_detector hM T).sub (integrable_detector hM 0)).sub (hsint n)
  have hz0 : (∫ ω, detector (M 0 ω) ∂P)=0 := by
    calc
      _ = ∫ ω, (0:ℝ) ∂P := integral_congr_ae (hz.mono fun ω he => by simp [he])
      _ = 0 := integral_zero _ _
  have hFint (n : ℕ) : (∫ ω, F n ω ∂P) = ∫ ω, detector (M T ω) ∂P := by
    change (∫ ω, detector (M T ω)-detector (M 0 ω)-
      ∑ i ∈ Finset.range (n+1), H n i ω *
        (M (grid T n (i+1)) ω-M (grid T n i) ω) ∂P)=_
    have hh := integral_sub ((integrable_detector hM T).sub (integrable_detector hM 0)) (hsint n)
    simp only [Pi.sub_apply] at hh
    rw [hh, integral_sub (integrable_detector hM T) (integrable_detector hM 0),
      hz0,hsz,sub_zero,sub_zero]
  have hFb (n : ℕ) : ∀ᵐ ω ∂P, ‖F n ω‖≤2*(C T ω-C 0 ω) := by
    filter_upwards [hcontrol] with ω hω
    simpa [F] using abs_error_le_variation detector detectorDeriv hasDerivAt_detector
      (L := 1) abs_detectorDeriv_le (fun t => M t ω) (fun t => C t ω) T hω n
  have hFl : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 0) := by
    filter_upwards [hc,hcontrol] with ω hcω hω
    exact tendsto_error_zero detector detectorDeriv hasDerivAt_detector
      lipschitz_detectorDeriv (fun t => M t ω) (fun t => C t ω) T hcω hω
  have hlim : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun ω => 2*(C T ω-C 0 ω)) (fun n => (hFi n).aestronglyMeasurable)
      (hint.const_mul 2) hFb hFl
  simp only [hFint] at hlim
  have he : (∫ ω, detector (M T ω) ∂P)=0 :=
    tendsto_nhds_unique tendsto_const_nhds hlim
  have hdet := (integral_eq_zero_iff_of_nonneg
    (fun ω => detector_nonneg (M T ω)) (integrable_detector hM T)).mp he
  filter_upwards [hdet] with ω hω
  exact (detector_eq_zero_iff _).mp hω

 
theorem ae_all_eq_zero (hM : Martingale M ℱ P) (hz : M 0 =ᵐ[P] 0)
    (hmc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (C : ℝ≥0 → Ω → ℝ) (hc : ∀ᵐ ω ∂P, Continuous (fun t => C t ω))
    (hcontrol : ∀ᵐ ω ∂P, ∀ s t, s≤t → |M t ω-M s ω|≤C t ω-C s ω)
    (hint : ∀ T, Integrable (fun ω => C T ω-C 0 ω) P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω=0 := by
  obtain ⟨D,hD,hd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have heq : ∀ᵐ ω ∂P, ∀ t∈D, M t ω=0 := by
    apply (ae_ball_iff hD).mpr
    intro t _
    exact ae_eq_zero_at hM hz C t (hc.mono fun _ h => h.continuousOn)
      (hcontrol.mono fun _ h s u hsu _ => h s u hsu) (hint t)
  filter_upwards [heq,hmc] with ω hω hmω
  have he : (fun t => M t ω)=(fun _ => (0:ℝ)) :=
    Continuous.ext_on hd hmω continuous_const hω
  exact fun t => congrFun he t

end SLEExactGauge.FiniteVariationMartingale
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.CompensatorUniqueness
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}
variable {A B : ℝ≥0 → Ω → ℝ} {TA TB : Ω → ℝ}

 

omit [IsFiniteMeasure P] in
lemma integrable_at [IsFiniteMeasure P] (hm : StronglyAdapted ℱ A)
    (hz : A 0 =ᵐ[P] 0) (hmono : ∀ᵐ ω ∂P, Monotone (fun t => A t ω))
    (hdom : ∀ᵐ ω ∂P, ∀ t, A t ω ≤ TA ω) (hi : Integrable TA P) (t : ℝ≥0) :
    Integrable (A t) P := by
  apply hi.norm.mono' ((hm t).mono (ℱ.le t)).aestronglyMeasurable
  filter_upwards [hz,hmono,hdom] with ω hzω hmω hdω
  have hnonneg : 0 ≤ A t ω := by simpa only [hzω,Pi.zero_apply] using hmω (show 0 ≤ t from bot_le)
  simpa only [Real.norm_eq_abs,abs_of_nonneg hnonneg] using
    (hdω t).trans (le_abs_self (TA ω))

 

lemma martingale_sub (hAm : StronglyAdapted ℱ A) (hBm : StronglyAdapted ℱ B)
    (hAi : ∀ t, Integrable (A t) P) (hBi : ∀ t, Integrable (B t) P)
    (hTA : Integrable TA P) (hTB : Integrable TB P)
    (hpot : ∀ t, P[TA - A t | ℱ t] =ᵐ[P] P[TB - B t | ℱ t]) :
    Martingale (A-B) ℱ P := by
  apply (martingale_condExp (TA-TB) ℱ P).congr (hAm.sub hBm)
  intro t
  have ha := condExp_of_stronglyMeasurable (ℱ.le t) (hAm t) (hAi t)
  have hb := condExp_of_stronglyMeasurable (ℱ.le t) (hBm t) (hBi t)
  filter_upwards [condExp_sub hTA hTB (ℱ t),condExp_sub hTA (hAi t) (ℱ t),
    condExp_sub hTB (hBi t) (ℱ t),hpot t] with ω hab hae hbe hp
  simp only [Pi.sub_apply,ha,hb] at hab hae hbe ⊢
  linarith

 

theorem ae_all_eq (hAm : StronglyAdapted ℱ A) (hBm : StronglyAdapted ℱ B)
    (hAz : A 0 =ᵐ[P] 0) (hBz : B 0 =ᵐ[P] 0)
    (hAc : ∀ᵐ ω ∂P, Continuous (fun t => A t ω))
    (hBc : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hAo : ∀ᵐ ω ∂P, Monotone (fun t => A t ω))
    (hBo : ∀ᵐ ω ∂P, Monotone (fun t => B t ω))
    (hAd : ∀ᵐ ω ∂P, ∀ t, A t ω ≤ TA ω)
    (hBd : ∀ᵐ ω ∂P, ∀ t, B t ω ≤ TB ω)
    (hTA : Integrable TA P) (hTB : Integrable TB P)
    (hpot : ∀ t, P[TA-A t | ℱ t] =ᵐ[P] P[TB-B t | ℱ t]) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, A t ω=B t ω := by
  have hAi := integrable_at hAm hAz hAo hAd hTA
  have hBi := integrable_at hBm hBz hBo hBd hTB
  have hM := martingale_sub hAm hBm hAi hBi hTA hTB hpot
  have hz : (A-B) 0 =ᵐ[P] 0 := by
    filter_upwards [hAz,hBz] with ω ha hb
    simp only [Pi.sub_apply,ha,hb,sub_self,Pi.zero_apply]
  have hmc : ∀ᵐ ω ∂P, Continuous (fun t => (A-B) t ω) := by
    filter_upwards [hAc,hBc] with ω ha hb
    exact ha.sub hb
  have hc : ∀ᵐ ω ∂P, Continuous (fun t => (A+B) t ω) := by
    filter_upwards [hAc,hBc] with ω ha hb
    exact ha.add hb
  have hcontrol : ∀ᵐ ω ∂P, ∀ s t, s≤t →
      |(A-B) t ω-(A-B) s ω|≤(A+B) t ω-(A+B) s ω := by
    filter_upwards [hAo,hBo] with ω ha hb s t hst
    have hat := ha hst
    have hbt := hb hst
    simp only [Pi.sub_apply,Pi.add_apply]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hint (T : ℝ≥0) : Integrable (fun ω => (A+B) T ω-(A+B) 0 ω) P :=
    ((hAi T).add (hBi T)).sub ((hAi 0).add (hBi 0))
  have he := FiniteVariationMartingale.ae_all_eq_zero hM hz hmc (A+B) hc hcontrol hint
  filter_upwards [he] with ω hω t
  exact sub_eq_zero.mp (hω t)

 
omit [IsFiniteMeasure P] in
theorem ae_terminal_eq_of_ae_all_eq [IsFiniteMeasure P]
    (hab : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, A t ω=B t ω)
    (hAl : ∀ᵐ ω ∂P, Tendsto (fun t => A t ω) atTop (𝓝 (TA ω)))
    (hBl : ∀ᵐ ω ∂P, Tendsto (fun t => B t ω) atTop (𝓝 (TB ω))) :
    TA =ᵐ[P] TB := by
  filter_upwards [hab,hAl,hBl] with ω he ha hb
  simp only [he] at ha
  exact tendsto_nhds_unique ha hb

end SLEExactGauge.CompensatorUniqueness
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.CompensatorUniqueness
open MassVersions
variable {Ω X : Type*} [mΩ : MeasurableSpace Ω]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}
    (μ ν : ℝ≥0 → Ω → Measure X) (Tμ Tν : Ω → Measure X)
    [∀ t ω, (μ t ω).Regular] [∀ t ω, (ν t ω).Regular]
    [∀ ω, (Tμ ω).Regular] [∀ ω, (Tν ω).Regular]

 
theorem ae_all_measure_eq
    (hμm : ∀ f : C_c(X,ℝ), StronglyAdapted ℱ (fun t ω => ∫x,f x∂μ t ω))
    (hνm : ∀ f : C_c(X,ℝ), StronglyAdapted ℱ (fun t ω => ∫x,f x∂ν t ω))
    (hμ0 : μ 0 =ᵐ[P] 0) (hν0 : ν 0 =ᵐ[P] 0)
    (hμc : ∀ f : C_c(X,ℝ), ∀ᵐ ω ∂P, Continuous (fun t => ∫x,f x∂μ t ω))
    (hνc : ∀ f : C_c(X,ℝ), ∀ᵐ ω ∂P, Continuous (fun t => ∫x,f x∂ν t ω))
    (hμo : ∀ᵐ ω ∂P, Monotone (fun t => μ t ω))
    (hνo : ∀ᵐ ω ∂P, Monotone (fun t => ν t ω))
    (hμd : ∀ᵐ ω ∂P, ∀ t, μ t ω≤Tμ ω)
    (hνd : ∀ᵐ ω ∂P, ∀ t, ν t ω≤Tν ω)
    (hμi : ∀ f : C_c(X,ℝ), Integrable (fun ω => ∫x,f x∂Tμ ω) P)
    (hνi : ∀ f : C_c(X,ℝ), Integrable (fun ω => ∫x,f x∂Tν ω) P)
    (hpot : ∀ f : C_c(X,ℝ), (∀ x, 0≤f x) → ∀ t,
      P[(fun ω => (∫x,f x∂Tμ ω)-(∫x,f x∂μ t ω)) | ℱ t] =ᵐ[P]
        P[(fun ω => (∫x,f x∂Tν ω)-(∫x,f x∂ν t ω)) | ℱ t]) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, μ t ω=ν t ω := by
  have hpos (f : C_c(X,ℝ)) (hf : ∀ x,0≤f x) :
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∫x,f x∂μ t ω)=∫x,f x∂ν t ω := by
    have hμz : (fun ω => ∫x,f x∂μ 0 ω) =ᵐ[P] 0 := by
      filter_upwards [hμ0] with ω hω
      simp only [hω,Pi.zero_apply,integral_zero_measure]
    have hνz : (fun ω => ∫x,f x∂ν 0 ω) =ᵐ[P] 0 := by
      filter_upwards [hν0] with ω hω
      simp only [hω,Pi.zero_apply,integral_zero_measure]
    have hμo' : ∀ᵐ ω ∂P, Monotone (fun t => ∫x,f x∂μ t ω) := by
      filter_upwards [hμo] with ω hω s t hst
      exact integral_mono_measure (hω hst) (Eventually.of_forall hf) f.integrable
    have hνo' : ∀ᵐ ω ∂P, Monotone (fun t => ∫x,f x∂ν t ω) := by
      filter_upwards [hνo] with ω hω s t hst
      exact integral_mono_measure (hω hst) (Eventually.of_forall hf) f.integrable
    have hμd' : ∀ᵐ ω ∂P, ∀ t, (∫x,f x∂μ t ω)≤∫x,f x∂Tμ ω := by
      filter_upwards [hμd] with ω hω t
      exact integral_mono_measure (hω t) (Eventually.of_forall hf) f.integrable
    have hνd' : ∀ᵐ ω ∂P, ∀ t, (∫x,f x∂ν t ω)≤∫x,f x∂Tν ω := by
      filter_upwards [hνd] with ω hω t
      exact integral_mono_measure (hω t) (Eventually.of_forall hf) f.integrable
    exact ae_all_eq (hμm f) (hνm f) hμz hνz (hμc f) (hνc f)
      hμo' hνo' hμd' hνd' (hμi f) (hνi f) (hpot f hf)
  apply ae_all_measure_eq_of_test_eq P μ ν
  intro i
  let f : C_c(X,ℝ) := determiningTests i
  filter_upwards [hpos (positiveTest f) (positiveTest_nonneg f),
    hpos (positiveTest (-f)) (positiveTest_nonneg (-f))] with ω hp hn t
  calc
    (∫x,f x∂μ t ω) = (∫x,positiveTest f x∂μ t ω)-(∫x,positiveTest (-f) x∂μ t ω) :=
      (integral_positiveTest_sub f _).symm
    _ = (∫x,positiveTest f x∂ν t ω)-(∫x,positiveTest (-f) x∂ν t ω) := by rw [hp t,hn t]
    _ = (∫x,f x∂ν t ω) := integral_positiveTest_sub f _

 
omit [IsFiniteMeasure P] [∀ time sample, (μ time sample).Regular]
    [∀ time sample, (ν time sample).Regular] in
theorem ae_terminal_measure_eq [IsFiniteMeasure P]
    [∀ time sample, (μ time sample).Regular] [∀ time sample, (ν time sample).Regular]
    (he : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, μ t ω=ν t ω)
    (hμl : ∀ f : C_c(X,ℝ), ∀ᵐ ω ∂P,
      Tendsto (fun t : ℝ≥0 => ∫x,f x∂μ t ω) atTop (𝓝 (∫x,f x∂Tμ ω)))
    (hνl : ∀ f : C_c(X,ℝ), ∀ᵐ ω ∂P,
      Tendsto (fun t : ℝ≥0 => ∫x,f x∂ν t ω) atTop (𝓝 (∫x,f x∂Tν ω))) :
    Tμ =ᵐ[P] Tν := by
  have hi (i : ℕ) : (fun ω => ∫x,determiningTests i x∂Tμ ω) =ᵐ[P]
      (fun ω => ∫x,determiningTests i x∂Tν ω) := by
    filter_upwards [he,hμl (determiningTests i),hνl (determiningTests i)] with ω hω hμω hνω
    simp only [hω] at hμω
    exact tendsto_nhds_unique hμω hνω
  filter_upwards [ae_all_iff.mpr hi] with ω hω
  exact measure_eq_of_determiningTests _ _ hω

 

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [BorelSpace X]
    [IsFiniteMeasure P] [∀ time sample, (μ time sample).Regular]
    [∀ time sample, (ν time sample).Regular] in
theorem ae_all_random_weight_eq [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [BorelSpace X] [IsFiniteMeasure P]
    [∀ time sample, (μ time sample).Regular] [∀ time sample, (ν time sample).Regular]
    (he : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, μ t ω=ν t ω) :
    ∀ᵐ ω ∂P, ∀ (t : Ω → ℝ≥0) (w : Ω → X → ℝ≥0∞),
      (∫⁻x,w ω x∂μ (t ω) ω)=∫⁻x,w ω x∂ν (t ω) ω := by
  filter_upwards [he] with ω hω t w
  rw [hω (t ω)]

end SLEExactGauge.CompensatorUniqueness
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.CompensatorUniqueness
open MassVersions
variable {Ω X : Type*} [mΩ : MeasurableSpace Ω]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}

 

theorem ae_all_measure_eq_of_ae_regular
    (μ ν : ℝ≥0 → Ω → Measure X) (Tμ Tν : Ω → Measure X)
    (hμr : ∀ᵐ ω ∂P, ∀t, (μ t ω).Regular)
    (hνr : ∀ᵐ ω ∂P, ∀t, (ν t ω).Regular)
    (hTμr : ∀ᵐ ω ∂P, (Tμ ω).Regular)
    (hTνr : ∀ᵐ ω ∂P, (Tν ω).Regular)
    (hμm : ∀ f : C_c(X,ℝ), StronglyAdapted ℱ (fun t ω => ∫x,f x∂μ t ω))
    (hνm : ∀ f : C_c(X,ℝ), StronglyAdapted ℱ (fun t ω => ∫x,f x∂ν t ω))
    (hμ0 : μ 0 =ᵐ[P] 0) (hν0 : ν 0 =ᵐ[P] 0)
    (hμc : ∀ f : C_c(X,ℝ), ∀ᵐ ω ∂P, Continuous (fun t => ∫x,f x∂μ t ω))
    (hνc : ∀ f : C_c(X,ℝ), ∀ᵐ ω ∂P, Continuous (fun t => ∫x,f x∂ν t ω))
    (hμo : ∀ᵐ ω ∂P, Monotone (fun t => μ t ω))
    (hνo : ∀ᵐ ω ∂P, Monotone (fun t => ν t ω))
    (hμd : ∀ᵐ ω ∂P, ∀ t, μ t ω≤Tμ ω)
    (hνd : ∀ᵐ ω ∂P, ∀ t, ν t ω≤Tν ω)
    (hμi : ∀ f : C_c(X,ℝ), Integrable (fun ω => ∫x,f x∂Tμ ω) P)
    (hνi : ∀ f : C_c(X,ℝ), Integrable (fun ω => ∫x,f x∂Tν ω) P)
    (hpot : ∀ f : C_c(X,ℝ), (∀ x, 0≤f x) → ∀ t,
      P[(fun ω => (∫x,f x∂Tμ ω)-(∫x,f x∂μ t ω)) | ℱ t] =ᵐ[P]
        P[(fun ω => (∫x,f x∂Tν ω)-(∫x,f x∂ν t ω)) | ℱ t]) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, μ t ω=ν t ω := by
  have hpos (f : C_c(X,ℝ)) (hf : ∀ x,0≤f x) :
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∫x,f x∂μ t ω)=∫x,f x∂ν t ω := by
    have hμz : (fun ω => ∫x,f x∂μ 0 ω) =ᵐ[P] 0 := by
      filter_upwards [hμ0] with ω hω
      simp only [hω,Pi.zero_apply,integral_zero_measure]
    have hνz : (fun ω => ∫x,f x∂ν 0 ω) =ᵐ[P] 0 := by
      filter_upwards [hν0] with ω hω
      simp only [hω,Pi.zero_apply,integral_zero_measure]
    have hμo' : ∀ᵐ ω ∂P, Monotone (fun t => ∫x,f x∂μ t ω) := by
      filter_upwards [hμo,hμr] with ω hω hr s t hst
      let := hr t
      exact integral_mono_measure (hω hst) (Eventually.of_forall hf) f.integrable
    have hνo' : ∀ᵐ ω ∂P, Monotone (fun t => ∫x,f x∂ν t ω) := by
      filter_upwards [hνo,hνr] with ω hω hr s t hst
      let := hr t
      exact integral_mono_measure (hω hst) (Eventually.of_forall hf) f.integrable
    have hμd' : ∀ᵐ ω ∂P, ∀ t, (∫x,f x∂μ t ω)≤∫x,f x∂Tμ ω := by
      filter_upwards [hμd,hTμr] with ω hω hr t
      let := hr
      exact integral_mono_measure (hω t) (Eventually.of_forall hf) f.integrable
    have hνd' : ∀ᵐ ω ∂P, ∀ t, (∫x,f x∂ν t ω)≤∫x,f x∂Tν ω := by
      filter_upwards [hνd,hTνr] with ω hω hr t
      let := hr
      exact integral_mono_measure (hω t) (Eventually.of_forall hf) f.integrable
    exact ae_all_eq (hμm f) (hνm f) hμz hνz (hμc f) (hνc f)
      hμo' hνo' hμd' hνd' (hμi f) (hνi f) (hpot f hf)
  have he (i : ℕ) : ∀ᵐ ω ∂P, ∀t,
      (∫x,determiningTests i x∂μ t ω)=∫x,determiningTests i x∂ν t ω := by
    let f : C_c(X,ℝ) := determiningTests i
    filter_upwards [hμr,hνr,hpos (positiveTest f) (positiveTest_nonneg f),
      hpos (positiveTest (-f)) (positiveTest_nonneg (-f))] with ω hr hs hp hn t
    let := hr t
    let := hs t
    calc
      (∫x,f x∂μ t ω) = (∫x,positiveTest f x∂μ t ω)-(∫x,positiveTest (-f) x∂μ t ω) :=
        (integral_positiveTest_sub f _).symm
      _ = (∫x,positiveTest f x∂ν t ω)-(∫x,positiveTest (-f) x∂ν t ω) := by rw [hp t,hn t]
      _ = (∫x,f x∂ν t ω) := integral_positiveTest_sub f _
  filter_upwards [ae_all_iff.mpr he,hμr,hνr] with ω hω hr hs t
  let := hr t
  let := hs t
  exact measure_eq_of_determiningTests _ _ (fun i => hω i t)

 
omit [IsFiniteMeasure P] in
theorem ae_terminal_measure_eq_of_ae_regular [IsFiniteMeasure P]
    (μ ν : ℝ≥0 → Ω → Measure X) (Tμ Tν : Ω → Measure X)
    (hTμr : ∀ᵐ ω ∂P, (Tμ ω).Regular)
    (hTνr : ∀ᵐ ω ∂P, (Tν ω).Regular)
    (he : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, μ t ω=ν t ω)
    (hμl : ∀ f : C_c(X,ℝ), ∀ᵐ ω ∂P,
      Tendsto (fun t : ℝ≥0 => ∫x,f x∂μ t ω) atTop (𝓝 (∫x,f x∂Tμ ω)))
    (hνl : ∀ f : C_c(X,ℝ), ∀ᵐ ω ∂P,
      Tendsto (fun t : ℝ≥0 => ∫x,f x∂ν t ω) atTop (𝓝 (∫x,f x∂Tν ω))) :
    Tμ =ᵐ[P] Tν := by
  have hi (i : ℕ) : (fun ω => ∫x,determiningTests i x∂Tμ ω) =ᵐ[P]
      (fun ω => ∫x,determiningTests i x∂Tν ω) := by
    filter_upwards [he,hμl (determiningTests i),hνl (determiningTests i)] with ω hω hμω hνω
    simp only [hω] at hμω
    exact tendsto_nhds_unique hμω hνω
  filter_upwards [ae_all_iff.mpr hi,hTμr,hTνr] with ω hω hr hs
  let := hr
  let := hs
  exact measure_eq_of_determiningTests _ _ hω

end SLEExactGauge.CompensatorUniqueness
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.MassVersions

 

lemma integrable_test_of_ae_measure_le {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (W : Measure Ω) (M T : Ω→Measure X) {f : X→ℝ} (hf : ∀x,0≤f x)
    (hm : AEStronglyMeasurable (fun ω => ∫x,f x∂M ω) W)
    (hl : ∀ᵐ ω ∂W, Integrable f (T ω))
    (hi : Integrable (fun ω => ∫x,f x∂T ω) W)
    (hd : ∀ᵐ ω ∂W, M ω≤T ω) : Integrable (fun ω => ∫x,f x∂M ω) W := by
  apply hi.norm.mono' hm
  filter_upwards [hl,hd] with ω hω hdω
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (integral_nonneg (μ:=M ω) hf),abs_of_nonneg (integral_nonneg (μ:=T ω) hf)]
  exact integral_mono_measure hdω (Eventually.of_forall hf) hω

lemma double_lintegral_ofReal_eq {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (W : Measure Ω) (M : Ω→Measure X) {f : X→ℝ} (hf : ∀x,0≤f x)
    (hlocal : ∀ᵐ ω ∂W, Integrable f (M ω))
    (hmean : Integrable (fun ω => ∫x,f x∂M ω) W) (A : Set Ω) :
    (∫⁻ω in A,∫⁻x,ENNReal.ofReal (f x)∂M ω∂W)=
      ENNReal.ofReal (∫ω in A,∫x,f x∂M ω∂W) := by
  calc
    _ = ∫⁻ω in A,ENNReal.ofReal (∫x,f x∂M ω)∂W := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae hlocal] with ω hω
      exact (ofReal_integral_eq_lintegral_ofReal hω (Eventually.of_forall hf)).symm
    _ = _ := (ofReal_integral_eq_lintegral_ofReal hmean.restrict
      (Eventually.of_forall fun ω => integral_nonneg hf)).symm

 

lemma condExp_sub_eq_of_lintegral_potential {Ω X : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace X] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (W : @Measure Ω mΩ) [IsFiniteMeasure W]
    (K L TK TL : Ω→Measure X) {f : X→ℝ} (hf : ∀x,0≤f x)
    (hKi : Integrable (fun ω => ∫x,f x∂K ω) W)
    (hLi : Integrable (fun ω => ∫x,f x∂L ω) W)
    (hTKi : Integrable (fun ω => ∫x,f x∂TK ω) W)
    (hTLi : Integrable (fun ω => ∫x,f x∂TL ω) W)
    (hKl : ∀ᵐ ω ∂W, Integrable f (K ω))
    (hLl : ∀ᵐ ω ∂W, Integrable f (L ω))
    (hTKl : ∀ᵐ ω ∂W, Integrable f (TK ω))
    (hTLl : ∀ᵐ ω ∂W, Integrable f (TL ω))
    (V : Set Ω→ℝ≥0∞)
    (hK : ∀A,MeasurableSet[m] A →
      (∫⁻ω in A,∫⁻x,ENNReal.ofReal (f x)∂TK ω∂W)=
        (∫⁻ω in A,∫⁻x,ENNReal.ofReal (f x)∂K ω∂W)+V A)
    (hL : ∀A,MeasurableSet[m] A →
      (∫⁻ω in A,∫⁻x,ENNReal.ofReal (f x)∂TL ω∂W)=
        (∫⁻ω in A,∫⁻x,ENNReal.ofReal (f x)∂L ω∂W)+V A) :
    W[(fun ω => (∫x,f x∂TK ω)-(∫x,f x∂K ω)) | m] =ᵐ[W]
      W[(fun ω => (∫x,f x∂TL ω)-(∫x,f x∂L ω)) | m] := by
  apply ae_eq_condExp_of_forall_setIntegral_eq hm (hTLi.sub hLi)
    (fun _ _ _ => integrable_condExp.integrableOn) _
    stronglyMeasurable_condExp.aestronglyMeasurable
  intro A hA _
  have hk : Integrable (fun ω => (∫x,f x∂TK ω)-(∫x,f x∂K ω)) W := hTKi.sub hKi
  rw [setIntegral_condExp hm hk hA]
  simp only [Pi.sub_apply]
  rw [integral_sub hTKi.restrict hKi.restrict,integral_sub hTLi.restrict hLi.restrict]
  have he : (∫⁻ω in A,∫⁻x,ENNReal.ofReal (f x)∂TK ω∂W)+
      (∫⁻ω in A,∫⁻x,ENNReal.ofReal (f x)∂L ω∂W)=
      (∫⁻ω in A,∫⁻x,ENNReal.ofReal (f x)∂TL ω∂W)+
      (∫⁻ω in A,∫⁻x,ENNReal.ofReal (f x)∂K ω∂W) := by
    rw [hK A hA,hL A hA]
    ac_rfl
  rw [@double_lintegral_ofReal_eq Ω X mΩ _ W TK f hf hTKl hTKi,
    @double_lintegral_ofReal_eq Ω X mΩ _ W L f hf hLl hLi,
    @double_lintegral_ofReal_eq Ω X mΩ _ W TL f hf hTLl hTLi,
    @double_lintegral_ofReal_eq Ω X mΩ _ W K f hf hKl hKi] at he
  have hh := congrArg ENNReal.toReal he
  have hn (M : Ω→Measure X) : 0≤∫ω in A,∫x,f x∂M ω∂W :=
    integral_nonneg (fun _ => integral_nonneg hf)
  simp only [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (hn TK),ENNReal.toReal_ofReal (hn L),
    ENNReal.toReal_ofReal (hn TL),ENNReal.toReal_ofReal (hn K)] at hh
  linarith

end SLEExactGauge.MassVersions
end
end

end OAI
