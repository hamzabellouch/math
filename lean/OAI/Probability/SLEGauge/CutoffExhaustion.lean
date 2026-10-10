import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.RadiusComparison

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
open Filter
open Filter Set
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain ExactSLEStops
open scoped Classical
lemma unfinishedCutoff_exhausts {m : ℕ} (a : ℝ) (ha : 0<a)
    (z : Fin m → ℂ) (hz : ∀ i, 0<(z i).im)
    (ρ : Fin m → ℝ) (hρ : ∀ i, 0<ρ i) (hr : ∀ i, ρ i≤(z i).im)
    (b : ExactSLEGenerator.Driver) (hb : ∀ i, radialTime a b.1 (z i) (ρ i)<∞) :
    ∀ᶠ n in Filter.atTop, ∀ i, radialTime a b.1 (z i) (ρ i) <
      (unfinishedCutoff a ha z hz ρ hρ hr n b : ℝ≥0∞) := by
  have he : ∀ᶠ n in atTop, ∀ i, (radialStop a ha (z i) (hz i) (ρ i) (hρ i) (hr i) n b : ℝ≥0∞)=
      radialTime a b.1 (z i) (ρ i) := by
    rw [Filter.eventually_all]
    intro i
    exact radialStop_eventually_eq a ha (z i) (hz i) (ρ i) (hρ i) (hr i) b (hb i).ne
  have hn : ∀ᶠ n : ℕ in atTop, ∀ i, radialTime a b.1 (z i) (ρ i)<(n:ℝ≥0∞) := by
    rw [Filter.eventually_all]
    intro i
    obtain ⟨N,hN⟩ := ENNReal.exists_nat_gt (hb i).ne
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact hN.trans_le (by exact_mod_cast hn)
  filter_upwards [he,hn] with n he hn i
  rw [unfinishedCutoff_coe,unfinishedCutoffTop]
  have hi : (Finset.univ.inf fun j =>
      if (radialStop a ha (z j) (hz j) (ρ j) (hρ j) (hr j) n b : ℝ≥0∞)=radialTime a b.1 (z j) (ρ j)
      then ∞ else (radialStop a ha (z j) (hz j) (ρ j) (hρ j) (hr j) n b : ℝ≥0∞))=∞ := by
    apply top_unique
    apply Finset.le_inf
    intro j hj
    rw [ite_eq_left (he j)]
  rw [hi,min_top_right]
  exact hn i
end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
 

theorem actual_unfinished_cutoff {m : ℕ} (a : ℝ) (ha : 0<a)
    (z : Fin m → ℂ) (hz : ∀ i, 0<(z i).im)
    (ρ : Fin m → ℝ) (hρ : ∀ i, 0<ρ i) (hr : ∀ i, ρ i≤(z i).im) :
    (∀ n, IsStoppingTime rawFiltration
      (fun b => (unfinishedCutoff a ha z hz ρ hρ hr n b : WithTop ℝ≥0))) ∧
    (∀ n b t i, t≤unfinishedCutoff a ha z hz ρ hρ hr n b →
      (t:ℝ≥0∞)≤radialTime a b.1 (z i) (ρ i) → alive a b.1 t (z i)) ∧
    (∀ b, (∀ i, radialTime a b.1 (z i) (ρ i)<∞) →
      ∀ᶠ n in Filter.atTop, ∀ i, radialTime a b.1 (z i) (ρ i) <
        (unfinishedCutoff a ha z hz ρ hρ hr n b : ℝ≥0∞)) := by
  refine ⟨unfinishedCutoff_stopping a ha z hz ρ hρ hr,?_,unfinishedCutoff_exhausts a ha z hz ρ hρ hr⟩
  intro n b t i ht hti
  exact radialStop_actual a ha (z i) (hz i) (ρ i) (hρ i) (hr i) n b t
    (unfinishedCutoff_before_individual a ha z hz ρ hρ hr n b t i ht hti)
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain ExactSLEFlow
open Set Filter
lemma localState_noiseFree_deriv (a ε : ℝ) (hε : 0<ε) (z : ℂ)
    (b : ExactSLEGenerator.Driver) (T : ℝ≥0) (u : ℝ) (hu : u∈Icc (0:ℝ) T) :
    HasDerivWithinAt (fun v : ℝ => localState a ε hε z v.toNNReal b-b.1 v.toNNReal • noise)
      (cutoffDrift a ε (localState a ε hε z u.toNNReal b)) (Icc (0:ℝ) T) u := by
  have hc : Continuous (fun v : ℝ => cutoffDrift a ε (localState a ε hε z v.toNNReal b)) :=
    (cutoffDrift_lipschitz a ε hε).continuous.comp
      ((localState_continuous a ε hε z b).comp continuous_real_toNNReal)
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 u)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add ((z,0):State)
  apply hd.hasDerivWithinAt.congr_of_mem _ hu
  intro v hv
  rw [localState_eq_zero,Real.coe_toNNReal _ hv.1]
  abel
lemma localState_lower_cutoff (a η ε : ℝ) (hη : 0<η) (hε : 0<ε) (hηε : η≤ε)
    (z : ℂ) (b : ExactSLEGenerator.Driver) (T : ℝ≥0)
    (hy : ∀ t≤T, ε≤Y (localState a ε hε z t b)) (t : ℝ≥0) (ht : t≤T) :
    localState a η hη z t b=localState a ε hε z t b := by
  let f : ℝ → State := fun u => localState a η hη z u.toNNReal b-b.1 u.toNNReal • noise
  let g : ℝ → State := fun u => localState a ε hε z u.toNNReal b-b.1 u.toNNReal • noise
  let u : ℝ → State := fun v => b.1 v.toNNReal • noise
  have hf : Continuous f := ((localState_continuous a η hη z b).comp continuous_real_toNNReal).sub
    ((b.1.continuous.comp continuous_real_toNNReal).smul continuous_const)
  have hg : Continuous g := ((localState_continuous a ε hε z b).comp continuous_real_toNNReal).sub
    ((b.1.continuous.comp continuous_real_toNNReal).smul continuous_const)
  have hfd (v : ℝ) (hv : v∈Icc (0:ℝ) T) :
      HasDerivWithinAt f (cutoffDrift a η (f v+u v)) (Icc (0:ℝ) T) v := by
    simpa only [f,u,sub_add_cancel] using localState_noiseFree_deriv a η hη z b T v hv
  have hgd (v : ℝ) (hv : v∈Icc (0:ℝ) T) :
      HasDerivWithinAt g (cutoffDrift a η (g v+u v)) (Icc (0:ℝ) T) v := by
    have hvT : v.toNNReal≤T := (Real.toNNReal_le_toNNReal hv.2).trans_eq (by simp)
    have he : cutoffDrift a ε (localState a ε hε z v.toNNReal b)=
        cutoffDrift a η (localState a ε hε z v.toNNReal b) := by
      rw [cutoffDrift_eq_physical a ε _ (hy _ hvT),cutoffDrift_eq_physical a η _ (hηε.trans (hy _ hvT))]
    simpa only [g,u,sub_add_cancel,←he] using localState_noiseFree_deriv a ε hε z b T v hv
  have he := additive_flow_unique (cutoffDrift_lipschitz a η hη) hf.continuousOn hg.continuousOn
    hfd hgd (by simp [f,g,localState_zero]) (show (t:ℝ)∈Icc (0:ℝ) T from ⟨t.coe_nonneg,ht⟩)
  simpa only [f,g,Real.toNNReal_coe,sub_left_inj] using he
lemma localState_noise_bounds (a η : ℝ) (hη : 0<η) (z : ℂ)
    (b : ExactSLEGenerator.Driver) (t : ℝ≥0) :
    ‖localState a η hη z t b‖≤‖z‖+|b.1 t|+max (|a|/η) (|a|/η^2)*t ∧
    |b.1 t|≤‖localState a η hη z t b‖+‖z‖+max (|a|/η) (|a|/η^2)*t := by
  let K := max (|a|/η) (|a|/η^2)
  let I : State := ∫ v in (0:ℝ)..(t:ℝ), cutoffDrift a η (localState a η hη z v.toNNReal b)
  have hI : ‖I‖≤K*t := by
    simpa only [sub_zero,abs_of_nonneg t.coe_nonneg] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a:=(0:ℝ)) (b:=(t:ℝ))
        (C:=K) (fun v _ => cutoffDrift_bound a η hη _)
  have hn : ‖noise‖=1 := by simp [noise,Prod.norm_def]
  have hnoise : ‖b.1 t • noise‖=|b.1 t| := by rw [norm_smul,hn,mul_one,Real.norm_eq_abs]
  have hz : ‖((z,0):State)‖=‖z‖ := by simp [Prod.norm_def]
  have he : localState a η hη z t b=(z,0)+b.1 t • noise+I := localState_eq_zero a η hη z t b
  constructor
  · rw [he]
    calc
      _ ≤ ‖((z,0):State)+b.1 t • noise‖+‖I‖ := norm_add_le _ _
      _ ≤ ‖((z,0):State)‖+‖b.1 t • noise‖+K*t := add_le_add (norm_add_le _ _) hI
      _ = _ := by rw [hz,hnoise]
  · have he' : b.1 t • noise=localState a η hη z t b-(z,0)-I := by rw [he]; abel
    rw [←hnoise,he']
    calc
      _ ≤ ‖localState a η hη z t b-(z,0)‖+‖I‖ := norm_sub_le _ _
      _ ≤ ‖localState a η hη z t b‖+‖((z,0):State)‖+K*t := add_le_add (norm_sub_le _ _) hI
      _ = _ := by rw [hz]
lemma finite_pos_lower {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i∈s,0<f i) :
    ∃ η : ℝ, 0<η ∧ ∀ i∈s, η≤f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨η,hη,hηs⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min (f i) η,lt_min (hf i (Finset.mem_insert_self _ _)) hη,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl|hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hηs j hj)
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
 

theorem actual_common_cutoff_safe {m : ℕ} (a : ℝ) (ha : 0<a)
    (z : Fin m → ℂ) (hz : ∀ i, 0<(z i).im)
    (ρ : Fin m → ℝ) (hρ : ∀ i, 0<ρ i) (hr : ∀ i, ρ i≤(z i).im) (n : ℕ) :
    ∃ η : ℝ, ∃ hη : 0<η, ∃ M : ℝ≥0, ∀ (b : ExactSLEGenerator.Driver) (t : ℝ≥0),
      t≤unfinishedCutoff a ha z hz ρ hρ hr n b →
      (∃ i, (t:ℝ≥0∞)≤radialTime a b.1 (z i) (ρ i)) →
      ‖vectorState a η hη z t b‖≤M ∧
      ∀ i, (t:ℝ≥0∞)≤radialTime a b.1 (z i) (ρ i) →
        η≤Y (vectorState a η hη z t b i) ∧
        vectorState a η hη z t b i=actualState a b.1 t (z i) := by
  let L := fun i => radialLocalization a ha (z i) (hz i) (ρ i) (angleThreshold (z i) n)
    (hρ i) (hr i) (angleThreshold_pos (z i) (hz i) n) (angleThreshold_initial (z i) (hz i) n)
  obtain ⟨η,hη,hηi⟩ := finite_pos_lower Finset.univ (fun i => (L i).ε) (fun i _ => (L i).hε)
  let N : ℝ≥0 := Finset.univ.sup (fun i => (L i).N)
  let K : ℝ := max (|a|/η) (|a|/η^2)
  have hK : 0≤K := le_trans (by positivity : 0≤|a|/η) (le_max_left _ _)
  let M : ℝ≥0 := ⟨N+2*‖z‖+2*K*n,by positivity⟩
  refine ⟨η,hη,M,?_⟩
  intro b t ht hex
  have htN : (t:ℝ)≤n := by
    have hcut : (unfinishedCutoff a ha z hz ρ hρ hr n b : ℝ≥0∞)≤(n:ℝ≥0∞) := by
      rw [unfinishedCutoff_coe]
      exact unfinishedCutoffTop_le a ha z hz ρ hρ hr n b
    have h : (t:ℝ≥0∞)≤(n:ℝ≥0∞) := (ENNReal.coe_le_coe.mpr ht).trans hcut
    exact_mod_cast h
  have hstate (i : Fin m) (hi : (t:ℝ≥0∞)≤radialTime a b.1 (z i) (ρ i)) :
      η≤Y (vectorState a η hη z t b i) ∧
      vectorState a η hη z t b i=actualState a b.1 t (z i) ∧
      ‖vectorState a η hη z t b i‖≤(L i).N := by
    have hti := unfinishedCutoff_before_individual a ha z hz ρ hρ hr n b t i ht hi
    have he : localState a η hη (z i) t b=localState a (L i).ε (L i).hε (z i) t b :=
      localState_lower_cutoff a η (L i).ε hη (L i).hε (hηi i (Finset.mem_univ i)) (z i) b
        (radialStop a ha (z i) (hz i) (ρ i) (hρ i) (hr i) n b)
        (fun u hu => (regionStop_safe a (L i).ε (L i).hε (z i) (L i).N (ρ i)
          (angleThreshold (z i) n) (L i).B (L i).initial b u hu).1) t hti
    have hs := regionStop_safe a (L i).ε (L i).hε (z i) (L i).N (ρ i)
      (angleThreshold (z i) n) (L i).B (L i).initial b t hti
    have ha' := regionStop_actualState a (L i).ε (L i).hε (z i) (L i).N (ρ i)
      (angleThreshold (z i) n) (L i).B (L i).initial b t hti
    change η≤Y (localState a η hη (z i) t b) ∧
      localState a η hη (z i) t b=actualState a b.1 t (z i) ∧ _
    rw [he]
    exact ⟨(hηi i (Finset.mem_univ i)).trans hs.1,ha'.2.symm,by simpa only [vectorState,he] using hs.2.1⟩
  obtain ⟨j,hj⟩ := hex
  have hjN : ((L j).N:ℝ)≤N := by exact_mod_cast Finset.le_sup (f:=fun i => (L i).N) (Finset.mem_univ j)
  have hbn : |b.1 t|≤N+‖z‖+K*n := by
    have h := (localState_noise_bounds a η hη (z j) b t).2
    have hs := (hstate j hj).2.2.trans hjN
    have hzj := norm_le_pi_norm z j
    have hkt := mul_le_mul_of_nonneg_left htN hK
    change ‖localState a η hη (z j) t b‖≤(N:ℝ) at hs
    dsimp only [K] at *
    linarith
  constructor
  · apply (pi_norm_le_iff_of_nonneg M.coe_nonneg).mpr
    intro i
    have h := (localState_noise_bounds a η hη (z i) b t).1
    have hzj := norm_le_pi_norm z i
    have hkt := mul_le_mul_of_nonneg_left htN hK
    change ‖localState a η hη (z i) t b‖≤N+2*‖z‖+2*K*n
    dsimp only [K] at *
    linarith
  · intro i hi
    exact ⟨(hstate i hi).1,(hstate i hi).2.1⟩
end ExactSLEGreen
namespace ExactSLEStops
open Set Filter
open scoped Classical
variable {Ω : Type*} [MeasurableSpace Ω]
noncomputable def clip (τ : Ω → ℝ≥0∞) (B : Ω → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (min (τ ω) (B ω : ℝ≥0∞)).toNNReal
omit [MeasurableSpace Ω] in
lemma clip_coe (τ : Ω → ℝ≥0∞) (B : Ω → ℝ≥0) (ω : Ω) :
    (clip τ B ω : ℝ≥0∞)=min (τ ω) (B ω : ℝ≥0∞) :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top (by simp) (min_le_right _ _))
omit [MeasurableSpace Ω] in
lemma clip_le (τ : Ω → ℝ≥0∞) (B : Ω → ℝ≥0) (ω : Ω) : clip τ B ω≤B ω := by
  apply ENNReal.coe_le_coe.mp
  rw [clip_coe]
  exact min_le_right _ _
omit [MeasurableSpace Ω] in
lemma le_clip_iff (τ : Ω → ℝ≥0∞) (B : Ω → ℝ≥0) (ω : Ω) (t : ℝ≥0) :
    t≤clip τ B ω ↔ (t:ℝ≥0∞)≤τ ω ∧ t≤B ω := by
  rw [←ENNReal.coe_le_coe,clip_coe,le_min_iff,ENNReal.coe_le_coe]
omit [MeasurableSpace Ω] in
lemma clip_le_time (τ : Ω → ℝ≥0∞) (B : Ω → ℝ≥0) (ω : Ω) :
    (clip τ B ω : ℝ≥0∞)≤τ ω := by rw [clip_coe]; exact min_le_left _ _
lemma clip_stopping (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (τ : Ω → ℝ≥0∞) (B : Ω → ℝ≥0) (hτ : IsStoppingTime F τ)
    (hB : IsStoppingTime F (fun ω => (B ω : WithTop ℝ≥0))) :
    IsStoppingTime F (fun ω => (clip τ B ω : WithTop ℝ≥0)) := by
  have h := hτ.min hB
  intro t
  have ht := h t
  change MeasurableSet[F t] {ω | min (τ ω) (B ω : ℝ≥0∞)≤(t:ℝ≥0∞)} at ht
  change MeasurableSet[F t] {ω | (clip τ B ω : ℝ≥0∞)≤(t:ℝ≥0∞)}
  simpa only [clip_coe] using ht
 
noncomputable def phase (A B C : ℝ≥0∞) (t : ℝ≥0) : Fin 4 :=
  if C≤(t:ℝ≥0∞) then 3 else if B≤(t:ℝ≥0∞) then 2 else if A≤(t:ℝ≥0∞) then 1 else 0
lemma phase_measurable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (A B C : Ω → ℝ≥0∞) (S : Ω → ℝ≥0)
    (hA : IsStoppingTime F A) (hB : IsStoppingTime F B) (hC : IsStoppingTime F C)
    (hS : IsStoppingTime F (fun ω => (S ω : WithTop ℝ≥0))) :
    Measurable[hS.measurableSpace] (fun ω => phase (A ω) (B ω) (C ω) (S ω)) := by
  have hA' : MeasurableSet[hS.measurableSpace] {ω | A ω≤(S ω : ℝ≥0∞)} := hA.measurableSet_stopping_time_le hS
  have hB' : MeasurableSet[hS.measurableSpace] {ω | B ω≤(S ω : ℝ≥0∞)} := hB.measurableSet_stopping_time_le hS
  have hC' : MeasurableSet[hS.measurableSpace] {ω | C ω≤(S ω : ℝ≥0∞)} := hC.measurableSet_stopping_time_le hS
  exact measurable_const.ite hC' (measurable_const.ite hB' (measurable_const.ite hA' measurable_const))
lemma phase_one_iff (A B C : ℝ≥0∞) (t : ℝ≥0) (_hAB : A≤B) (hBC : B≤C) :
    phase A B C t=1 ↔ A≤(t:ℝ≥0∞) ∧ (t:ℝ≥0∞)<B := by
  unfold phase
  split_ifs with hC hB hA <;> simp_all
  order
lemma phase_two_iff (A B C : ℝ≥0∞) (t : ℝ≥0) (_hAB : A≤B) (_hBC : B≤C) :
    phase A B C t=2 ↔ B≤(t:ℝ≥0∞) ∧ (t:ℝ≥0∞)<C := by
  unfold phase
  split_ifs with hC hB hA <;> simp_all
lemma phase_zero_iff (A B C : ℝ≥0∞) (t : ℝ≥0) (hAB : A≤B) (hBC : B≤C) :
    phase A B C t=0 ↔ (t:ℝ≥0∞)<A := by
  unfold phase
  split_ifs with hC hB hA <;> simp_all <;> order
lemma phase_three_iff (A B C : ℝ≥0∞) (t : ℝ≥0) :
    phase A B C t=3 ↔ C≤(t:ℝ≥0∞) := by
  unfold phase
  split_ifs <;> simp_all
 
omit [MeasurableSpace Ω] in
lemma no_actual_change_between (l : List (Ω → ℝ≥0)) (B : Ω → ℝ≥0) (τ : Ω → ℝ≥0∞)
    (hτ : clip τ B∈l) (ω : Ω) (k : ℕ) (hk : k+1<(sort l).length)
    (hB : (sort l)[k+1] ω≤B ω) :
    τ ω≤((sort l)[k] ω : ℝ≥0∞) ∨ ((sort l)[k+1] ω : ℝ≥0∞)≤τ ω := by
  rcases no_change_between l ω k hk (clip τ B) hτ with h|h
  · by_cases ht : τ ω≤((sort l)[k] ω : ℝ≥0∞)
    · exact Or.inl ht
    · right
      have hs : B ω≤(sort l)[k] ω := by
        have h' := ENNReal.coe_le_coe.mpr h
        rw [clip_coe,min_le_iff] at h'
        exact ENNReal.coe_le_coe.mp (h'.resolve_left ht)
      exact (ENNReal.coe_le_coe.mpr (hB.trans hs)).trans (not_le.mp ht).le
  · exact Or.inr ((le_clip_iff τ B ω _).mp h).1
end ExactSLEStops

 
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt Set Filter
open scoped ENNReal NNReal
lemma radialTime_antitone (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (ρ σ : ℝ) (hρ : 0<ρ) (hρσ : ρ≤σ) (hσ : σ≤z.im) (b : ExactSLEGenerator.Driver) :
    radialTime a b.1 z σ≤radialTime a b.1 z ρ := by
  rcases hρσ.eq_or_lt with rfl|h
  · exact le_rfl
  · by_cases ht : radialTime a b.1 z ρ=∞
    · rw [ht]; exact le_top
    · exact (radialTime_strict_of_finite a ha z hz ρ σ hρ h hσ b ht).le
lemma actual_radius_before_target (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (ρ : ℝ) (hρ : 0<ρ) (hr : ρ≤z.im) (b : ExactSLEGenerator.Driver) (t : ℝ≥0)
    (ht : alive a b.1 t z) (htr : (t:ℝ≥0∞)≤radialTime a b.1 z ρ) :
    ρ≤physicalRadius (actualState a b.1 t z) := by
  rcases htr.eq_or_lt with he|he
  · have hn : radialTime a b.1 z ρ≠∞ := by rw [←he]; simp
    have h := (radialTime_attained a ha z hz ρ hρ hr b hn).2
    rw [←he,ENNReal.toNNReal_coe] at h
    exact h.ge
  · obtain ⟨n,hn⟩ := (radialStop_after_survival a ha z hz ρ hρ hr b t ht he).exists
    let L := radialLocalization a ha z hz ρ (angleThreshold z n) hρ hr
      (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
    have hs := regionStop_safe a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b t hn.le
    have heq := regionStop_actualState a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b t hn.le
    rw [heq.2]
    exact hs.2.2.1
lemma actual_physicalClock_le (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (cap ρ : ℝ) (hcap : 0<cap) (hρ : 0<ρ) (hr : ρ≤z.im) (b : ExactSLEGenerator.Driver) (t : ℝ≥0)
    (ht : alive a b.1 t z) (htr : (t:ℝ≥0∞)≤radialTime a b.1 z ρ) :
    physicalClock a cap (actualState a b.1 t z)≤Real.log (cap/(2*ρ))/(2*a) := by
  have hy : 0<Y (actualState a b.1 t z) := by
    obtain ⟨f,hf⟩ := ht
    simpa only [actualState,Y_apply,Complex.sub_im,Complex.ofReal_im,sub_zero,loewnerMap_eq hf]
      using (hf.2 t ⟨t.coe_nonneg,le_rfl⟩).1
  have hR := actual_radius_before_target a ha z hz ρ hρ hr b t ht htr
  have hR0 : 0<physicalRadius (actualState a b.1 t z) := hρ.trans_le hR
  rw [physicalClock_radius a cap hcap _ hy]
  apply (div_le_div_iff_of_pos_right (by positivity : 0<2*a)).mpr
  apply Real.log_le_log (by positivity)
  exact div_le_div_of_nonneg_left hcap.le (by positivity) (by linarith)
lemma actual_physicalClock_at (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (cap ρ : ℝ) (hcap : 0<cap) (hρ : 0<ρ) (hr : ρ≤z.im) (b : ExactSLEGenerator.Driver)
    (hf : radialTime a b.1 z ρ≠∞) :
    physicalClock a cap (actualState a b.1 (radialTime a b.1 z ρ).toNNReal z)=
      Real.log (cap/(2*ρ))/(2*a) := by
  have h := radialTime_attained a ha z hz ρ hρ hr b hf
  have hy : 0<Y (actualState a b.1 (radialTime a b.1 z ρ).toNNReal z) := by
    obtain ⟨f,hf⟩ := h.1
    simpa only [actualState,Y_apply,Complex.sub_im,Complex.ofReal_im,sub_zero,loewnerMap_eq hf]
      using (hf.2 _ ⟨(radialTime a b.1 z ρ).toNNReal.coe_nonneg,le_rfl⟩).1
  rw [physicalClock_radius a cap hcap _ hy,h.2]
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt Set Filter
open scoped ENNReal NNReal
noncomputable def levelRadius (a cap u : ℝ) : ℝ := cap/2*Real.exp (-2*a*u)
noncomputable def levelTime (a : ℝ) (b : ExactSLEGenerator.Driver) (z : ℂ) (cap u : ℝ) : ℝ≥0∞ :=
  radialTime a b.1 z (levelRadius a cap u)
lemma levelRadius_pos (a cap u : ℝ) (hc : 0<cap) : 0<levelRadius a cap u := by
  unfold levelRadius; positivity
lemma levelRadius_le {a cap u : ℝ} (ha : 0<a) (hc : 0<cap) (hu : 0≤u) :
    levelRadius a cap u≤cap/2 := by
  have h := Real.exp_le_one_iff.mpr (show -2*a*u≤0 by nlinarith)
  simpa only [levelRadius,mul_one] using mul_le_mul_of_nonneg_left h (show 0≤cap/2 by positivity)
lemma levelRadius_antitone {a cap : ℝ} (ha : 0<a) (hc : 0<cap) :
    Antitone (levelRadius a cap) := by
  intro u v huv
  apply mul_le_mul_of_nonneg_left _ (show 0≤cap/2 by positivity)
  exact Real.exp_le_exp.mpr (by nlinarith)
lemma levelTime_mono (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (cap : ℝ) (hc : 0<cap) (hr : cap≤2*z.im) (b : ExactSLEGenerator.Driver)
    (u v : ℝ) (hu : 0≤u) (huv : u≤v) :
    levelTime a b z cap u≤levelTime a b z cap v := by
  apply radialTime_antitone a ha z hz _ _ (levelRadius_pos a cap v hc)
    (levelRadius_antitone ha hc huv)
  exact (levelRadius_le ha hc hu).trans (by linarith)
lemma levelRadius_clock {a cap u : ℝ} (ha : a≠0) (hc : 0<cap) :
    Real.log (cap/(2*levelRadius a cap u))/(2*a)=u := by
  have h : cap/(2*levelRadius a cap u)=Real.exp (2*a*u) := by
    unfold levelRadius
    rw [show 2*(cap/2*Real.exp (-2*a*u))=cap*Real.exp (-(2*a*u)) by ring_nf,
      Real.exp_neg,div_mul_eq_div_div,div_self hc.ne',one_div,inv_inv]
  rw [h,Real.log_exp]
  field_simp
lemma levelTime_clock (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (cap u : ℝ) (hc : 0<cap) (hr : cap≤2*z.im) (hu : 0≤u) (b : ExactSLEGenerator.Driver)
    (hf : levelTime a b z cap u≠∞) :
    physicalClock a cap (actualState a b.1 (levelTime a b z cap u).toNNReal z)=u := by
  unfold levelTime
  rw [actual_physicalClock_at a ha z hz cap _ hc (levelRadius_pos a cap u hc)
    ((levelRadius_le ha hc hu).trans (by linarith)) b hf,levelRadius_clock ha.ne' hc]
lemma levelTime_fullRadius (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (cap : ℝ) (hc : 0<cap) (hr : cap≤2*z.im) (b : ExactSLEGenerator.Driver)
    (hf : levelTime a b z cap 0≠∞) :
    fullLoewnerRadius a b.1 z (levelTime a b z cap 0).toNNReal=cap := by
  have h := radialTime_attained a ha z hz _ (levelRadius_pos a cap 0 hc)
    ((levelRadius_le ha hc le_rfl).trans (by linarith)) b hf
  unfold levelTime
  rw [←actual_radius_eq_full b.1.continuous h.1,h.2]
  simp [levelRadius]
  ring
lemma actual_physicalClock_mono (a : ℝ) (ha : 0<a) (cap : ℝ) (_hc : 0<cap)
    (b : ExactSLEGenerator.Driver) (z : ℂ) (S T : ℝ≥0) (hST : S≤T) (hT : alive a b.1 T z) :
    physicalClock a cap (actualState a b.1 S z)≤physicalClock a cap (actualState a b.1 T z) := by
  obtain ⟨f,hf⟩ := hT
  have hS : alive a b.1 S z := ⟨f,odeUntil_mono hf hST⟩
  have hy : 0<Y (actualState a b.1 S z) := by
    simpa only [actualState,Y_apply,Complex.sub_im,Complex.ofReal_im,sub_zero,loewnerMap_eq (odeUntil_mono hf hST)]
      using (hf.2 S ⟨S.coe_nonneg,by exact_mod_cast hST⟩).1
  have hR : 0<fullLoewnerRadius a b.1 z S := by
    rw [←actual_radius_eq_full b.1.continuous hS]
    unfold physicalRadius
    positivity
  have heT := actual_clock_eq ha.ne' hR b.1.continuous hf hST le_rfl rfl
  have heS := actual_clock_eq ha.ne' hR b.1.continuous hf hST hST rfl
  have hS0 : activeODEClock b.1 T S f S=0 := by simp [activeODEClock]
  have hu := activeODEClock_nonneg (b:=b.1) (T:=T) (σ:=S) (f:=f) (show (S:ℝ)≤T from hST)
  rw [hS0] at heS
  have he : physicalClock a cap (actualState a b.1 T z)-physicalClock a cap (actualState a b.1 S z)=
      physicalClock a (fullLoewnerRadius a b.1 z S) (actualState a b.1 T z)-
      physicalClock a (fullLoewnerRadius a b.1 z S) (actualState a b.1 S z) := by
    unfold physicalClock
    ring
  rw [heT,heS,sub_zero] at he
  linarith
lemma levelTime_clock_le (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (cap u : ℝ) (hc : 0<cap) (hr : cap≤2*z.im) (hu : 0≤u) (b : ExactSLEGenerator.Driver)
    (t : ℝ≥0) (ht : alive a b.1 t z) (htt : (t:ℝ≥0∞)≤levelTime a b z cap u) :
    physicalClock a cap (actualState a b.1 t z)≤u := by
  have h := actual_physicalClock_le a ha z hz cap _ hc (levelRadius_pos a cap u hc)
    ((levelRadius_le ha hc hu).trans (by linarith)) b t ht htt
  rwa [levelRadius_clock ha.ne' hc] at h
lemma levelTime_clock_ge (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (cap u : ℝ) (hc : 0<cap) (hr : cap≤2*z.im) (hu : 0≤u) (b : ExactSLEGenerator.Driver)
    (t : ℝ≥0) (ht : alive a b.1 t z) (htt : levelTime a b z cap u≤(t:ℝ≥0∞)) :
    u≤physicalClock a cap (actualState a b.1 t z) := by
  have hf : levelTime a b z cap u≠∞ := ne_top_of_le_ne_top (by simp) htt
  have hs : (levelTime a b z cap u).toNNReal≤t := by
    exact ENNReal.coe_le_coe.mp (ENNReal.coe_toNNReal_le_self.trans htt)
  rw [←levelTime_clock a ha z hz cap u hc hr hu b hf]
  exact actual_physicalClock_mono a ha cap hc b z _ t hs ht
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt
open scoped Classical
abbrev PhaseVector (m : ℕ) := Fin m → Fin 4
noncomputable def phaseActive {m : ℕ} (p : PhaseVector m) : Finset (Fin m) :=
  Finset.univ.filter fun i => p i=1 ∨ p i=2
noncomputable def phaseSigma {m : ℕ} (a : ℝ) (p : PhaseVector m) (i : Fin m) : ℝ :=
  if p i=2 then regBeta a else -regBeta a
noncomputable def phaseOffset {m : ℕ} (a : ℝ) (U : Fin m → ℝ) (p : PhaseVector m) (i : Fin m) : ℝ :=
  if p i=2 then -regBeta a*U i else 0
noncomputable def phaseConstant {m : ℕ} (a : ℝ) (U : Fin m → ℝ) (p : PhaseVector m) : ℝ :=
  ∏ i, if p i=3 then Real.exp (regP a*U i/2)/3 else 1
noncomputable def phaseProduct {m : ℕ} (a : ℝ) (cap U : Fin m → ℝ)
    (p : PhaseVector m) (v : Fin m → State) : ℝ :=
  phaseConstant a U p*regularizedProduct (phaseActive p) a cap (phaseSigma a p) (phaseOffset a U p) v
end ExactSLEGreen
end

end OAI
