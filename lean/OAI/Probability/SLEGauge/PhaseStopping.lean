import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.CutoffExhaustion

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
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt
open scoped Classical
lemma phaseActive_mem {m : ℕ} (p : PhaseVector m) (i : Fin m) :
    i∈phaseActive p ↔ p i=1 ∨ p i=2 := by simp [phaseActive]
lemma phaseConstant_pos {m : ℕ} (a : ℝ) (U : Fin m → ℝ) (p : PhaseVector m) :
    0<phaseConstant a U p := by
  apply Finset.prod_pos
  intro i hi
  split_ifs <;> positivity
lemma phaseSigma_bound {m : ℕ} {a : ℝ} (ha : 1/4<a) (p : PhaseVector m) (i : Fin m) :
    |phaseSigma a p i|≤regBeta a := by
  unfold phaseSigma
  split_ifs <;> simp [abs_of_pos (regBeta_pos ha)]
lemma physicalRegularized_pos (a cap σ off : ℝ) (v : State) :
    0<physicalRegularized a cap σ off v := by
  have hs := Real.sin_pos_of_pos_of_lt_pi (physicalTheta_mem v).1 (physicalTheta_mem v).2
  unfold physicalRegularized regFactor sinePower clockExp physicalDelta
  positivity
lemma regularizedProduct_pos {m : ℕ} (s : Finset (Fin m)) (a : ℝ)
    (cap σ off : Fin m → ℝ) (v : Fin m → State) :
    0<regularizedProduct s a cap σ off v :=
  Finset.prod_pos fun i _ => physicalRegularized_pos a (cap i) (σ i) (off i) (v i)
lemma phaseProduct_pos {m : ℕ} (a : ℝ) (cap U : Fin m → ℝ)
    (p : PhaseVector m) (v : Fin m → State) : 0<phaseProduct a cap U p v :=
  mul_pos (phaseConstant_pos a U p) (regularizedProduct_pos _ a cap _ _ v)
lemma physicalRegularized_activation {a cap σ off : ℝ} (ha : 1/4<a) (v : State)
    (hu : physicalClock a cap v=0) (ho : off=0) : physicalRegularized a cap σ off v≤1 := by
  have hθ := physicalTheta_mem v
  have hb := (regFactor_bounds ha (by norm_num : (0:ℝ)<1) le_rfl
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)).2.2.2
  simpa [physicalRegularized,clockExp,physicalDelta,hu,ho,div_eq_mul_inv,mul_comm] using (div_le_div_of_nonneg_right hb (by norm_num : (0:ℝ)≤3))
lemma physicalRegularized_completion {a cap σ off U : ℝ} (ha : 1/4<a) (v : State)
    (hu : physicalClock a cap v=U) (ho : off+σ*U=0) :
    Real.exp (regP a*U/2)/3≤physicalRegularized a cap σ off v := by
  have hθ := physicalTheta_mem v
  have hb := (regFactor_bounds ha (by norm_num : (0:ℝ)<1) le_rfl
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)).2.1
  have h := mul_le_mul_of_nonneg_left hb (show 0≤Real.exp (regP a*U/2)/3 by positivity)
  simpa [physicalRegularized,clockExp,physicalDelta,hu,ho,mul_div_assoc,div_mul_eq_mul_div] using h
lemma physicalRegularized_midpoint (a cap U : ℝ) (v : State)
    (hu : physicalClock a cap v=U/2) :
    physicalRegularized a cap (regBeta a) (-regBeta a*U) v=
      physicalRegularized a cap (-regBeta a) 0 v := by
  unfold physicalRegularized physicalDelta
  rw [hu]
  congr 3
  ring
lemma physicalRegularized_measurable (a cap σ off : ℝ) : Measurable (physicalRegularized a cap σ off) := by
  unfold physicalRegularized clockExp physicalDelta physicalClock regFactor sinePower physicalTheta
  have hX := X.continuous.measurable
  have hY := Y.continuous.measurable
  have hJ := J.continuous.measurable
  fun_prop
lemma phaseProduct_measurable {m : ℕ} (a : ℝ) (cap U : Fin m → ℝ) (p : PhaseVector m) :
    Measurable (phaseProduct a cap U p) := by
  unfold phaseProduct regularizedProduct
  apply measurable_const.mul
  exact Finset.measurable_prod _ fun i _ => (physicalRegularized_measurable a (cap i) _ _).comp (measurable_pi_apply i)
end ExactSLEGreen

 
namespace ExactSLEStops
open scoped ENNReal NNReal
lemma phase_mono (A B C : ℝ≥0∞) : Monotone (phase A B C) := by
  intro S T hST
  have hst : (S:ℝ≥0∞)≤T := ENNReal.coe_le_coe.mpr hST
  unfold phase
  split_ifs <;> norm_num [Fin.le_def] at * <;>
    have hst' : (S:ℝ≥0∞)≤T := ENNReal.coe_le_coe.mpr hST
  all_goals exfalso; order
lemma boundary_eq {τ : ℝ≥0∞} {S T : ℝ≥0}
    (h : τ≤(S:ℝ≥0∞) ∨ (T:ℝ≥0∞)≤τ) (hS : (S:ℝ≥0∞)<τ) (hT : τ≤(T:ℝ≥0∞)) : τ=(T:ℝ≥0∞) :=
  le_antisymm hT (h.resolve_left (not_le.mpr hS))
end ExactSLEStops
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt ExactSLEStops
open scoped Classical ENNReal NNReal
noncomputable def phaseFactor (a cap U : ℝ) (p : Fin 4) (v : State) : ℝ :=
  if p=0 then 1 else if p=3 then Real.exp (regP a*U/2)/3 else
    physicalRegularized a cap (if p=2 then regBeta a else -regBeta a)
      (if p=2 then -regBeta a*U else 0) v
lemma phaseProduct_eq_prod {m : ℕ} (a : ℝ) (cap U : Fin m → ℝ) (p : PhaseVector m)
    (v : Fin m → State) : phaseProduct a cap U p v=∏ i, phaseFactor a (cap i) (U i) (p i) (v i) := by
  unfold phaseProduct phaseConstant regularizedProduct phaseActive
  rw [Finset.prod_filter,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  unfold phaseSigma phaseOffset phaseFactor
  generalize hp : p i=j
  fin_cases j <;> norm_num [Fin.ext_iff]
lemma phaseFactor_pos (a cap U : ℝ) (p : Fin 4) (v : State) : 0<phaseFactor a cap U p v := by
  unfold phaseFactor
  split_ifs
  · norm_num
  · positivity
  · exact physicalRegularized_pos _ _ _ _ _
  · exact physicalRegularized_pos _ _ _ _ _
 
lemma phaseFactor_transition {a cap U : ℝ} (ha : 1/4<a) (v : State)
    (A B C : ℝ≥0∞) (S T : ℝ≥0) (hAB : A≤B) (hBC : B≤C) (hST : S≤T)
    (hA : A≤(S:ℝ≥0∞) ∨ (T:ℝ≥0∞)≤A)
    (hB : B≤(S:ℝ≥0∞) ∨ (T:ℝ≥0∞)≤B)
    (hC : C≤(S:ℝ≥0∞) ∨ (T:ℝ≥0∞)≤C)
    (huA : A=(T:ℝ≥0∞) → physicalClock a cap v=0)
    (huB : B=(T:ℝ≥0∞) → physicalClock a cap v=U/2)
    (huC : C=(T:ℝ≥0∞) → physicalClock a cap v=U) :
    phaseFactor a cap U (phase A B C T) v≤phaseFactor a cap U (phase A B C S) v := by
  generalize hp : phase A B C S=p
  generalize hq : phase A B C T=q
  have hpq : p≤q := by rw [←hp,←hq]; exact phase_mono A B C hST
  fin_cases p <;> fin_cases q <;> try (norm_num [Fin.le_def] at hpq) <;> try exact le_rfl
  · have hsa := (phase_zero_iff A B C S hAB hBC).mp hp
    have hat := ((phase_one_iff A B C T hAB hBC).mp hq).1
    have hu := huA (boundary_eq hA hsa hat)
    simpa [phaseFactor,Fin.ext_iff] using physicalRegularized_activation (σ := -regBeta a) (off := 0) ha v hu rfl
  · have hsa := (phase_zero_iff A B C S hAB hBC).mp hp
    have hbt := ((phase_two_iff A B C T hAB hBC).mp hq).1
    have hua := huA (boundary_eq hA hsa (hAB.trans hbt))
    have hub := huB (boundary_eq hB (hsa.trans_le hAB) hbt)
    have hu0 : U=0 := by linarith
    simpa [phaseFactor,Fin.ext_iff,hu0] using
      physicalRegularized_activation (σ := regBeta a) (off := 0) ha v hua rfl
  · have hsa := (phase_zero_iff A B C S hAB hBC).mp hp
    have hct := (phase_three_iff A B C T).mp hq
    have hua := huA (boundary_eq hA hsa (hAB.trans (hBC.trans hct)))
    have huc := huC (boundary_eq hC (hsa.trans_le (hAB.trans hBC)) hct)
    have hu0 : U=0 := by linarith
    norm_num [phaseFactor,Fin.ext_iff,hu0]
  · have hsb := ((phase_one_iff A B C S hAB hBC).mp hp).2
    have hbt := ((phase_two_iff A B C T hAB hBC).mp hq).1
    have hu := huB (boundary_eq hB hsb hbt)
    simpa [phaseFactor,Fin.ext_iff] using (physicalRegularized_midpoint a cap U v hu).le
  · have hsb := ((phase_one_iff A B C S hAB hBC).mp hp).2
    have hct := (phase_three_iff A B C T).mp hq
    have hub := huB (boundary_eq hB hsb (hBC.trans hct))
    have huc := huC (boundary_eq hC (hsb.trans_le hBC) hct)
    have hu0 : U=0 := by linarith
    have h := physicalRegularized_completion (σ := -regBeta a) (off := 0) ha v huc (by rw [hu0]; ring)
    simpa [phaseFactor,Fin.ext_iff] using h
  · have hsc := ((phase_two_iff A B C S hAB hBC).mp hp).2
    have hct := (phase_three_iff A B C T).mp hq
    have hu := huC (boundary_eq hC hsc hct)
    have h := physicalRegularized_completion (σ := regBeta a) (off := -regBeta a*U) ha v hu (by ring)
    simpa [phaseFactor,Fin.ext_iff] using h
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt ExactSLEStops MeasureTheory Set Filter
open scoped Classical NNReal ENNReal
noncomputable def actualPhase {m : ℕ} (a : ℝ) (z : Fin m → ℂ) (cap U : Fin m → ℝ)
    (t : ℝ≥0) (b : ExactSLEGenerator.Driver) : PhaseVector m := fun i =>
  phase (levelTime a b (z i) (cap i) 0) (levelTime a b (z i) (cap i) (U i/2))
    (levelTime a b (z i) (cap i) (U i)) t
lemma actualPhase_measurable {m : ℕ} (a : ℝ) (ha : 0<a) (z : Fin m → ℂ)
    (hz : ∀ i, 0<(z i).im) (cap U : Fin m → ℝ) (hc : ∀ i,0<cap i)
    (hr : ∀ i, cap i≤2*(z i).im) (hu : ∀ i,0≤U i)
    (S : ExactSLEGenerator.Driver → ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0))) :
    Measurable[hS.measurableSpace] (fun b => actualPhase a z cap U (S b) b) := by
  apply @Measurable.of_eval _ _ _ hS.measurableSpace _
  intro i
  apply phase_measurable rawFiltration _ _ _ S _ _ _ hS
  all_goals apply radialTime_stopping a ha (z i) (hz i) _ (levelRadius_pos _ _ _ (hc i))
  · exact (levelRadius_le ha (hc i) le_rfl).trans (by have := hr i; linarith)
  · exact (levelRadius_le ha (hc i) (by have := hu i; linarith : 0≤U i/2)).trans (by have := hr i; linarith)
  · exact (levelRadius_le ha (hc i) (hu i)).trans (by have := hr i; linarith)
lemma active_phase_interval {A B C : ℝ≥0∞} {S T : ℝ≥0} (hAB : A≤B) (hBC : B≤C)
    (hC : C≤(S:ℝ≥0∞) ∨ (T:ℝ≥0∞)≤C)
    (hi : phase A B C S=1 ∨ phase A B C S=2) :
    A≤(S:ℝ≥0∞) ∧ (T:ℝ≥0∞)≤C ∧ (phase A B C S=2 → B≤(S:ℝ≥0∞)) := by
  rcases hi with hi|hi
  · have hp := (phase_one_iff A B C S hAB hBC).mp hi
    refine ⟨hp.1,hC.resolve_left (not_le.mpr (hp.2.trans_le hBC)),?_⟩
    intro hh
    have : (1:Fin 4)=2 := hi.symm.trans hh
    norm_num [Fin.ext_iff] at this
  · have hp := (phase_two_iff A B C S hAB hBC).mp hi
    exact ⟨hAB.trans hp.1,hC.resolve_left (not_le.mpr hp.2),fun _ => hp.1⟩
lemma phase_delta_le {a cap U : ℝ} (ha : 1/4<a) (p : Fin 4) (v : State)
    (hlo : 0≤physicalClock a cap v) (hhi : physicalClock a cap v≤U) :
    physicalDelta a cap (if p=2 then regBeta a else -regBeta a)
      (if p=2 then -regBeta a*U else 0) v≤1 := by
  unfold physicalDelta
  apply Real.exp_le_one_iff.mpr
  split_ifs
  · nlinarith [regBeta_pos ha]
  · nlinarith [regBeta_pos ha]
 

lemma actual_phase_interval_safe {m : ℕ} {a : ℝ} (ha : 1/4<a)
    (z : Fin m → ℂ) (hz : ∀ i,0<(z i).im) (cap U : Fin m → ℝ)
    (hc : ∀ i,0<cap i) (hr : ∀ i,cap i≤2*(z i).im) (hu : ∀ i,0≤U i)
    (η : ℝ) (hη : 0<η) (M : ℝ≥0) (b : ExactSLEGenerator.Driver) (S T : ℝ≥0)
    (_hST : S≤T) (hne : (phaseActive (actualPhase a z cap U S b)).Nonempty)
    (hboundary : ∀ i, levelTime a b (z i) (cap i) (U i)≤(S:ℝ≥0∞) ∨
      (T:ℝ≥0∞)≤levelTime a b (z i) (cap i) (U i))
    (hsafe : ∀ t≤T, (∃ i, (t:ℝ≥0∞)≤levelTime a b (z i) (cap i) (U i)) →
      ‖vectorState a η hη z t b‖≤M ∧ ∀ i,
      (t:ℝ≥0∞)≤levelTime a b (z i) (cap i) (U i) →
      alive a b.1 t (z i) ∧ η≤Y (vectorState a η hη z t b i) ∧
      vectorState a η hη z t b i=actualState a b.1 t (z i)) :
    ∀ t, S≤t → t≤T → ‖vectorState a η hη z t b‖≤M ∧
      ∀ i∈phaseActive (actualPhase a z cap U S b),
      η≤Y (vectorState a η hη z t b i) ∧
      physicalDelta a (cap i) (phaseSigma a (actualPhase a z cap U S b) i)
        (phaseOffset a U (actualPhase a z cap U S b) i) (vectorState a η hη z t b i)≤1 := by
  have ha0 : 0<a := by linarith
  have htimes (i) (hi : i∈phaseActive (actualPhase a z cap U S b)) :=
    active_phase_interval
      (levelTime_mono a ha0 (z i) (hz i) (cap i) (hc i) (hr i) b 0 (U i/2) le_rfl (by have := hu i; linarith))
      (levelTime_mono a ha0 (z i) (hz i) (cap i) (hc i) (hr i) b (U i/2) (U i) (by have := hu i; linarith) (by have := hu i; linarith))
      (hboundary i) ((phaseActive_mem (actualPhase a z cap U S b) i).mp hi)
  intro t hts htt
  obtain ⟨j,hj⟩ := hne
  have hti (i) (hi : i∈phaseActive (actualPhase a z cap U S b)) :
      (t:ℝ≥0∞)≤levelTime a b (z i) (cap i) (U i) :=
    (ENNReal.coe_le_coe.mpr htt).trans (htimes i hi).2.1
  have hs := hsafe t htt ⟨j,hti j hj⟩
  refine ⟨hs.1,fun i hi => ⟨(hs.2 i (hti i hi)).2.1,?_⟩⟩
  rw [(hs.2 i (hti i hi)).2.2]
  apply phase_delta_le ha
  · exact levelTime_clock_ge a ha0 (z i) (hz i) (cap i) 0 (hc i) (hr i) le_rfl b t
      (hs.2 i (hti i hi)).1 ((htimes i hi).1.trans (ENNReal.coe_le_coe.mpr hts))
  · exact levelTime_clock_le a ha0 (z i) (hz i) (cap i) (U i) (hc i) (hr i) (hu i) b t
      (hs.2 i (hti i hi)).1 (hti i hi)
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFiniteTilt ExactSLEStops MeasureTheory Set Filter
open scoped Classical NNReal ENNReal
lemma levelTime_clock_at_eq (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (cap u : ℝ) (hc : 0<cap) (hr : cap≤2*z.im) (hu : 0≤u) (b : ExactSLEGenerator.Driver)
    (t : ℝ≥0) (he : levelTime a b z cap u=(t:ℝ≥0∞)) :
    physicalClock a cap (actualState a b.1 t z)=u := by
  have h := levelTime_clock a ha z hz cap u hc hr hu b (by rw [he]; simp)
  simpa only [he,ENNReal.toNNReal_coe] using h
lemma actual_phase_transition {m : ℕ} {a : ℝ} (ha : 1/4<a)
    (z : Fin m → ℂ) (hz : ∀ i,0<(z i).im) (cap U : Fin m → ℝ)
    (hc : ∀ i,0<cap i) (hr : ∀ i,cap i≤2*(z i).im) (hu : ∀ i,0≤U i)
    (η : ℝ) (hη : 0<η) (b : ExactSLEGenerator.Driver) (S T : ℝ≥0) (hST : S≤T)
    (hboundary : ∀ i, ∀ u∈({0,U i/2,U i}:Finset ℝ),
      levelTime a b (z i) (cap i) u≤(S:ℝ≥0∞) ∨
      (T:ℝ≥0∞)≤levelTime a b (z i) (cap i) u)
    (hagree : ∀ i, (T:ℝ≥0∞)≤levelTime a b (z i) (cap i) (U i) →
      vectorState a η hη z T b i=actualState a b.1 T (z i)) :
    phaseProduct a cap U (actualPhase a z cap U T b) (vectorState a η hη z T b)≤
    phaseProduct a cap U (actualPhase a z cap U S b) (vectorState a η hη z T b) := by
  have ha0 : 0<a := by linarith
  rw [phaseProduct_eq_prod,phaseProduct_eq_prod]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact (phaseFactor_pos _ _ _ _ _).le
  · intro i hi
    have hAB := levelTime_mono a ha0 (z i) (hz i) (cap i) (hc i) (hr i) b 0 (U i/2) le_rfl (by have := hu i; linarith)
    have hBC := levelTime_mono a ha0 (z i) (hz i) (cap i) (hc i) (hr i) b (U i/2) (U i) (by have := hu i; linarith) (by have := hu i; linarith)
    apply phaseFactor_transition ha _ _ _ _ S T hAB hBC hST
      (hboundary i 0 (by simp)) (hboundary i (U i/2) (by simp)) (hboundary i (U i) (by simp))
    · intro he
      rw [hagree i (by rw [←he]; exact hAB.trans hBC)]
      exact levelTime_clock_at_eq a ha0 (z i) (hz i) (cap i) 0 (hc i) (hr i) le_rfl b T he
    · intro he
      rw [hagree i (by rw [←he]; exact hBC)]
      exact levelTime_clock_at_eq a ha0 (z i) (hz i) (cap i) (U i/2) (hc i) (hr i) (by have := hu i; linarith) b T he
    · intro he
      rw [hagree i he.symm.le]
      exact levelTime_clock_at_eq a ha0 (z i) (hz i) (cap i) (U i) (hc i) (hr i) (hu i) b T he
end ExactSLEGreen
namespace ExactSLEGreen
open ProbabilityTheory MeasureTheory ExactSLEGenerator ExactSLEFiniteTilt ExactSLECalculus Set Filter
open scoped Classical NNReal ENNReal
lemma vectorState_stopped_measurable {m : ℕ} (a η : ℝ) (hη : 0<η) (z : Fin m → ℂ)
    (S : Driver → ℝ≥0) (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0))) :
    Measurable[hS.measurableSpace] (fun b => vectorState a η hη z (S b) b) := by
  have hA : StronglyAdapted rawFiltration (vectorState a η hη z) :=
    fun t => (vectorState_adapted a η hη z t).stronglyMeasurable
  exact measurable_stoppedValue (hA.isStronglyProgressive_of_continuous
    (vectorState_continuous a η hη z)) hS
lemma regimeState_stopped_measurable {m : ℕ} (s : Finset (Fin m)) (a ε η : ℝ)
    (hη : 0<η) (N : ℝ≥0) (cap σ off : Fin m → ℝ) (z : Fin m → ℂ)
    (S : Driver → ℝ≥0) (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0))) :
    Measurable[hS.measurableSpace] (fun b => regimeState s a ε η hη N cap σ off z (S b) b) := by
  have hA : StronglyAdapted rawFiltration (regimeState s a ε η hη N cap σ off z) :=
    fun t => (regimeState_adapted s a ε η hη N cap σ off z t).stronglyMeasurable
  exact measurable_stoppedValue (hA.isStronglyProgressive_of_continuous
    (regimeState_continuous s a ε η hη N cap σ off z)) hS
lemma regularizedProduct_measurable {m : ℕ} (s : Finset (Fin m)) (a : ℝ)
    (cap σ off : Fin m → ℝ) : Measurable (regularizedProduct s a cap σ off) := by
  unfold regularizedProduct
  exact Finset.measurable_prod _ fun i _ =>
    (physicalRegularized_measurable a (cap i) (σ i) (off i)).comp (measurable_pi_apply i)
lemma regularizedProduct_bound {m : ℕ} (s : Finset (Fin m)) (a η : ℝ) (hη : 0<η)
    (N : ℝ≥0) (cap σ off : Fin m → ℝ) : ∃ C : ℝ, ∀ v : Fin m → State,
    ‖v‖≤N → (∀ i∈s, η≤Y (v i)) → ‖regularizedProduct s a cap σ off v‖≤C := by
  obtain ⟨C,hC⟩ := (regimeCutoff_compact s a η N cap σ off).exists_bound_of_continuous
    (regimeCutoff_smooth s a η hη N cap σ off).continuous
  refine ⟨C,fun v hv hy => ?_⟩
  have he := (regimeCutoff_eq_near s a η hη N cap σ off (v,0)
    (max_le hv (by simp)) hy).eq_of_nhds
  simpa only [he,discountedProduct,neg_zero,Real.exp_zero,one_mul] using hC (v,0)
lemma regimeState_discount_bound {m : ℕ} (s : Finset (Fin m)) (a ε η : ℝ)
    (hη : 0<η) (N B : ℝ≥0) (cap σ off : Fin m → ℝ) (z : Fin m → ℂ) :
    ∃ L : ℝ, 0≤L ∧ ∀ (b : Driver) (t : ℝ≥0), t≤B →
      |(regimeState s a ε η hη N cap σ off z t b).2|≤L := by
  obtain ⟨K,hK,hKb⟩ := regimeDiscountCut_bound s a ε η hη N cap σ off
  refine ⟨K*B,by positivity,fun b t ht => ?_⟩
  change ‖∫ u in (0:ℝ)..(t:ℝ), regimeDiscountCut s a ε η N cap σ off
    (vectorState a η hη z u.toNNReal b)‖≤_
  calc
    _ ≤ K*|(t:ℝ)-0| := intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => hKb _
    _ ≤ K*B := by rw [sub_zero,abs_of_nonneg t.coe_nonneg]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast ht) hK
lemma regularizedProduct_indicator_integrable {m : ℕ} (s : Finset (Fin m)) (a η : ℝ)
    (hη : 0<η) (N : ℝ≥0) (cap σ off : Fin m → ℝ) (z : Fin m → ℂ)
    (W : Measure Driver) [IsProbabilityMeasure W] (S : Driver → ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)))
    (E : Set Driver) (hE : MeasurableSet E)
    (hsafe : ∀ b∈E, ‖vectorState a η hη z (S b) b‖≤N ∧
      ∀ i∈s, η≤Y (vectorState a η hη z (S b) b i)) :
    Integrable (fun b => if b∈E then regularizedProduct s a cap σ off
      (vectorState a η hη z (S b) b) else 0) W := by
  obtain ⟨C,hC⟩ := regularizedProduct_bound s a η hη N cap σ off
  have hm := (regularizedProduct_measurable s a cap σ off).comp
    ((vectorState_stopped_measurable a η hη z S hS).mono hS.measurableSpace_le le_rfl)
  apply Integrable.of_bound (hm.ite hE measurable_const).aestronglyMeasurable (max C 0)
  apply Eventually.of_forall
  intro b
  split_ifs with hb
  · exact (hC _ (hsafe b hb).1 (hsafe b hb).2).trans (le_max_left _ _)
  · simpa only [norm_zero] using le_max_right C 0
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEFiniteTilt ExactSLECalculus ProbabilityTheory MeasureTheory Set Filter
open scoped Classical NNReal ENNReal
 

theorem vector_regime_event_comparison {m : ℕ} (s : Finset (Fin m)) {a ε η : ℝ}
    (ha : 1/4<a) (hε : 0<ε) (hη : 0<η) (hsize : ε*((s.card:ℝ)-1)≤regK a/2)
    (M : ℝ≥0) (cap σ off : Fin m → ℝ) (hσ : ∀ i∈s, |σ i|≤regBeta a)
    (z : Fin m → ℂ) (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (S T : Driver → ℝ≥0) (B : ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)))
    (hT : IsStoppingTime rawFiltration (fun b => (T b : WithTop ℝ≥0)))
    (hST : ∀ b, S b≤T b) (hTB : ∀ b, T b≤B)
    (E : Set Driver) (hE : MeasurableSet[hS.measurableSpace] E)
    (hsafe : ∀ b∈E, ∀ t, S b≤t → t≤T b →
      ‖vectorState a η hη z t b‖≤M ∧
      ∀ i∈s, η≤Y (vectorState a η hη z t b i) ∧
        physicalDelta a (cap i) (σ i) (off i) (vectorState a η hη z t b i)≤1)
    (D : ℝ) (hD : ∀ b∈E,
      (regimeState s a ε η hη M cap σ off z (T b) b).2-
      (regimeState s a ε η hη M cap σ off z (S b) b).2≤D) :
    (∫ b, (if b∈E then regularizedProduct s a cap σ off (vectorState a η hη z (T b) b) else 0) ∂W) ≤
    Real.exp D*(∫ b, (if b∈E then regularizedProduct s a cap σ off (vectorState a η hη z (S b) b) else 0) ∂W) := by
  let R := fun t b => (regimeState s a ε η hη M cap σ off z t b).2
  let P := fun t b => regularizedProduct s a cap σ off (vectorState a η hη z t b)
  obtain ⟨L,hL,hLb⟩ := regimeState_discount_bound s a ε η hη M B cap σ off z
  have hSB : ∀ b, S b≤B := fun b => (hST b).trans (hTB b)
  have hRS : Measurable[hS.measurableSpace] (fun b => R (S b) b) :=
    (regimeState_stopped_measurable s a ε η hη M cap σ off z S hS).snd
  have hRT : Measurable (fun b => R (T b) b) :=
    ((regimeState_stopped_measurable s a ε η hη M cap σ off z T hT).mono hT.measurableSpace_le le_rfl).snd
  have hRs : Measurable (fun b => R (S b) b) := hRS.mono hS.measurableSpace_le le_rfl
  let w : Driver → ℝ := fun b => if b∈E then Real.exp (R (S b) b) else 0
  have hw : StronglyMeasurable[hS.measurableSpace] w := (hRS.exp.ite hE measurable_const).stronglyMeasurable
  have hw0 : ∀ b, 0≤w b := by intro b; dsimp [w]; split_ifs <;> positivity
  have hwb : ∀ b, ‖w b‖≤Real.exp L := by
    intro b
    dsimp [w]
    split_ifs
    · simp only [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hLb b (S b) (hSB b)))
    · simpa using (Real.exp_pos L).le
  have hopt := vector_regime_weighted_optional_bounded s ha hε hη hsize M cap σ off hσ z W hW
    S T B hS hT hST hTB E hE w hw hw0 (Real.exp L) hwb
    (by intro b hb; simp [w,hb]) hsafe
  have hE' : MeasurableSet E := hS.measurableSpace_le E hE
  have hPi (Q : Driver → ℝ≥0) (hQ : IsStoppingTime rawFiltration (fun b => (Q b : WithTop ℝ≥0)))
      (hSQ : ∀ b,S b≤Q b) (hQT : ∀ b,Q b≤T b) :
      Integrable (fun b => if b∈E then P (Q b) b else 0) W := by
    apply regularizedProduct_indicator_integrable s a η hη M cap σ off z W Q hQ E hE'
    intro b hb
    exact ⟨(hsafe b hb _ (hSQ b) (hQT b)).1,fun i hi => (hsafe b hb _ (hSQ b) (hQT b)).2 i hi |>.1⟩
  have hFi := hPi T hT hST (fun _ => le_rfl)
  have hGi := hPi S hS (fun _ => le_rfl) hST
  let F := fun b => if b∈E then Real.exp (R (S b) b-R (T b) b)*P (T b) b else 0
  have hF_eq : F=fun b => Real.exp (R (S b) b-R (T b) b)*(if b∈E then P (T b) b else 0) := by
    funext b; dsimp [F]; split_ifs <;> simp
  have hFint : Integrable F W := by
    rw [hF_eq]
    apply hFi.bdd_mul (hRs.sub hRT).exp.aestronglyMeasurable
    apply Eventually.of_forall
    intro b
    simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr (show R (S b) b-R (T b) b≤2*L from ?_)
    have h1 := (abs_le.mp (hLb b (S b) (hSB b))).2
    have h2 := (abs_le.mp (hLb b (T b) (hTB b))).1
    change R (S b) b≤L at h1
    change -L≤R (T b) b at h2
    linarith
  have heT : (fun b => w b*discountedProduct s a cap σ off
      (regimeState s a ε η hη M cap σ off z (T b) b))=F := by
    funext b
    dsimp [w,F,discountedProduct,P,R,regimeState]
    split_ifs <;> simp [Real.exp_sub,div_eq_mul_inv,Real.exp_neg,mul_assoc]
  have heS : (fun b => w b*discountedProduct s a cap σ off
      (regimeState s a ε η hη M cap σ off z (S b) b))=(fun b => if b∈E then P (S b) b else 0) := by
    funext b
    dsimp [w,discountedProduct,P,R,regimeState]
    split_ifs <;> simp [Real.exp_neg,Real.exp_ne_zero]
  rw [heT,heS] at hopt
  calc
    _ ≤ ∫ b, Real.exp D*F b ∂W := integral_mono hFi (hFint.const_mul _) (fun b => by
      dsimp [F]
      split_ifs with hb
      · have h : 1≤Real.exp D*Real.exp (R (S b) b-R (T b) b) := by
          rw [←Real.exp_add]
          apply Real.one_le_exp_iff.mpr
          have hd := hD b hb
          change R (T b) b-R (S b) b≤D at hd
          linarith
        have h0 := (regularizedProduct_pos s a cap σ off (vectorState a η hη z (T b) b)).le
        simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right h h0
      · simp)
    _ = Real.exp D*(∫ b,F b ∂W) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hopt (Real.exp_pos D).le
end ExactSLEGreen
open MeasureTheory
open scoped Classical
namespace ExactSLEPasting
end ExactSLEPasting
end

end OAI
