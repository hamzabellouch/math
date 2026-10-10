import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.SpatialPastTail

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SLEExactGauge.AdaptedFailure

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

 
def failed (success : ℕ→Set Ω) : ℕ→Set Ω
  | 0 => univ
  | n+1 => failed success n \ success n

omit m₀ in
lemma failed_iff [MeasurableSpace Ω] (success : ℕ→Set Ω) (n : ℕ) (ω : Ω) :
    ω∈failed success n ↔ ∀i<n,ω∉success i := by
  induction n with
  | zero => simp [failed]
  | succ n ih =>
    simp only [failed,Set.mem_sdiff,ih,Nat.lt_succ_iff_lt_or_eq]
    constructor
    · rintro ⟨h,h'⟩ i (hi | rfl)
      · exact h i hi
      · exact h'
    · intro h
      exact ⟨fun i hi=>h i (Or.inl hi),h n (Or.inr rfl)⟩

lemma failed_measurable (ℱ : Filtration ℕ m₀)
    (success : ℕ→Set Ω) (hs : ∀i,MeasurableSet[ℱ (i+1)] (success i)) (n : ℕ) :
    MeasurableSet[ℱ n] (failed success n) := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih => exact (ℱ.mono (Nat.le_succ n) _ ih).diff (hs n)

 

theorem failure_product (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m₀) (success : ℕ→Set Ω)
    (hs : ∀i,MeasurableSet[ℱ (i+1)] (success i)) (p : ℕ→ℝ)
    (hp1 : ∀i,p i≤1)
    (htest : ∀i,∀A : Set Ω,MeasurableSet[ℱ i] A →
      p i*P.real A≤P.real (A∩success i)) (n : ℕ) :
    P.real (failed success n)≤∏i∈Finset.range n,(1-p i) := by
  induction n with
  | zero => simp [failed]
  | succ n ih =>
    have hs' : MeasurableSet (success n) := ℱ.le (n+1) _ (hs n)
    have hsplit := measureReal_inter_add_sdiff (μ := P) (s := failed success n) hs'
    have hstep := htest n (failed success n) (failed_measurable ℱ success hs n)
    calc
      P.real (failed success (n+1))≤(1-p n)*P.real (failed success n) := by
        change P.real (failed success n \ success n)≤_
        nlinarith
      _ ≤ (1-p n)*(∏i∈Finset.range n,(1-p i)) :=
        mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hp1 n))
      _ = _ := by rw [Finset.prod_range_succ]; ring

lemma product_le_exp (p : ℕ→ℝ) (hp1 : ∀i,p i≤1) (n : ℕ) :
    (∏i∈Finset.range n,(1-p i))≤Real.exp (-(∑i∈Finset.range n,p i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = (∏i∈Finset.range n,(1-p i))*(1-p n) := Finset.prod_range_succ _ _
      _ ≤ Real.exp (-(∑i∈Finset.range n,p i))*Real.exp (-p n) :=
        mul_le_mul ih (Real.one_sub_le_exp_neg _) (sub_nonneg.mpr (hp1 n)) (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add,Finset.sum_range_succ,neg_add_rev]; congr 1; ring

 

lemma tested_of_conditional (P : Measure Ω) [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    (S : Set Ω) (hS : MeasurableSet[m₀] S) (p : ℝ)
    (hp : ∀ᵐ ω∂P,p≤P[S.indicator (fun _=> (1:ℝ)) | m] ω)
    (A : Set Ω) (hA : MeasurableSet[m] A) :
    p*P.real A≤P.real (A∩S) := by
  have hInt : Integrable (S.indicator (fun _ : Ω=>(1:ℝ))) P :=
    (integrable_const 1).indicator hS
  calc
    p*P.real A = ∫ω in A,p∂P := by simp only [setIntegral_const,smul_eq_mul]; ring
    _ ≤ ∫ω in A,P[S.indicator (fun _=>(1:ℝ)) | m] ω∂P :=
      integral_mono_ae (integrable_const _) integrable_condExp.integrableOn
        (ae_restrict_of_ae hp)
    _ = ∫ω in A,S.indicator (fun _=>(1:ℝ)) ω∂P := setIntegral_condExp hm hInt hA
    _ = P.real (A∩S) := by rw [setIntegral_indicator hS]; simp

 

theorem conditional_failure (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m₀) (success : ℕ→Set Ω)
    (hs : ∀i,MeasurableSet[ℱ (i+1)] (success i)) (p : ℕ→ℝ)
    (hp1 : ∀i,p i≤1)
    (hp : ∀i,∀ᵐ ω∂P,p i≤P[(success i).indicator (fun _=>(1:ℝ)) | ℱ i] ω)
    (n : ℕ) (B : ℝ) (hB : B≤∑i∈Finset.range n,p i) :
    P.real (failed success n)≤Real.exp (-B) := by
  refine (failure_product P ℱ success hs p hp1 ?_ n).trans
    ((product_le_exp p hp1 n).trans (Real.exp_le_exp.mpr (neg_le_neg hB)))
  intro i A hA
  exact tested_of_conditional P (ℱ.le i) (success i) (ℱ.le (i+1) _ (hs i))
    (p i) (hp i) A hA

 

lemma weighted_past_bound (P : Measure Ω) [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    (f : Ω→ℝ) (hf : Integrable f P) (K : ℝ)
    (hb : ∀ᵐ ω∂P,P[f | m] ω≤K) (A : Set Ω) (hA : MeasurableSet[m] A) :
    (∫ω in A,f ω∂P)≤K*P.real A := by
  calc
    (∫ω in A,f ω∂P) = ∫ω in A,P[f | m] ω∂P := (setIntegral_condExp hm hf hA).symm
    _ ≤ ∫ω in A,K∂P := integral_mono_ae integrable_condExp.integrableOn
      (integrable_const _) (ae_restrict_of_ae hb)
    _ = K*P.real A := by simp only [setIntegral_const,smul_eq_mul]; ring

 

theorem weighted_conditional_failure (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m₀) (success : ℕ→Set Ω)
    (hs : ∀i,MeasurableSet[ℱ (i+1)] (success i)) (p : ℕ→ℝ)
    (hp1 : ∀i,p i≤1)
    (hp : ∀i,∀ᵐ ω∂P,p i≤P[(success i).indicator (fun _=>(1:ℝ)) | ℱ i] ω)
    (n : ℕ) (B : ℝ) (hB : B≤∑i∈Finset.range n,p i)
    (f : Ω→ℝ) (hf : Integrable f P) (K : ℝ) (hK : 0≤K)
    (hb : ∀ᵐ ω∂P,P[f | ℱ n] ω≤K) :
    (∫ω in failed success n,f ω∂P)≤K*Real.exp (-B) :=
  (weighted_past_bound P (ℱ.le n) f hf K hb (failed success n)
    (failed_measurable ℱ success hs n)).trans
    (mul_le_mul_of_nonneg_left (conditional_failure P ℱ success hs p hp1 hp n B hB) hK)

end SLEExactGauge.AdaptedFailure
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator
open LoewnerRestart CompactSequence MomentBatches AdaptedFailure

 

structure RadialTestSchedule (a y : ℝ) where
  start : ℕ → ℝ
  boundary : ℕ → ℝ
  level : ℕ
  threshold : ℕ → ℝ
  boundary_pos : ∀i,0 < boundary i
  boundary_le : ∀i,boundary i ≤ y
  start_pos : ∀i,0 < start i
  start_le : ∀i,start i ≤ boundary i
  next : ∀i,boundary (i+1)=start i*Real.exp (-2*a*level)
  threshold_nonneg : ∀i,0 ≤ threshold i
  gap : ∀i,∃s : ℝ,Jacobi.mixingTime (4*a) ≤ s ∧ start i=boundary i*Real.exp (-2*a*s)

namespace CenteredMomentModel
variable {κ a : ℝ} {ha : 1/4 < a} {W : Measure GDriver} (M : CenteredMomentModel κ a ha W)

def testSuccess (z : ℂ) (D : RadialTestSchedule a z.im) (i : ℕ) : Set GDriver :=
  {b | ENNReal.ofReal (D.threshold i) ≤ M.stoppedTest z (D.start i) D.level b}

def testFailure (z : ℂ) (D : RadialTestSchedule a z.im) (n : ℕ) : Set GDriver :=
  failed (M.testSuccess z D) n

lemma testFailure_raw (z : ℂ) (hz : 0 < z.im) (D : RadialTestSchedule a z.im) (n : ℕ) :
    MeasurableSet[(radialTime_stopping a (by linarith) z hz (D.boundary n)
      (D.boundary_pos n) (D.boundary_le n)).measurableSpace] (M.testFailure z D n) := by
  induction n with
  | zero => exact MeasurableSet.univ
  | succ n ih =>
    have hs := M.stoppedTest_measurable z hz (D.start n) (D.start_pos n)
      ((D.start_le n).trans (D.boundary_le n)) D.level
    have hn : D.boundary (n+1) ≤ D.boundary n := by
      rw [D.next]
      exact (testEndpoint_le (ha := ha) _ (D.start_pos n).le _).trans (D.start_le n)
    have hmono := (radialTime_stopping a (by linarith) z hz (D.boundary n)
      (D.boundary_pos n) (D.boundary_le n)).measurableSpace_mono
      (radialTime_stopping a (by linarith) z hz (D.boundary (n+1))
        (D.boundary_pos _) (D.boundary_le _))
      (radialTime_antitone a (by linarith) z hz _ _ (D.boundary_pos _) hn (D.boundary_le n))
    apply (hmono _ ih).diff
    unfold testSuccess
    have he := measurableSet_le (f := fun _=>ENNReal.ofReal (D.threshold n)) measurable_const hs
    exact ⟨he.1,fun t=>by simpa only [D.next] using he.2 t⟩

 

theorem testFailure_product [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (z : ℂ) (hz : 0 < z.im) (D : RadialTestSchedule a z.im) (n : ℕ) :
    (radialLaw W a z (D.boundary n)).real (M.testFailure z D n) ≤
      ∏i∈Finset.range n,(1-M.law.real {x | D.threshold i ≤ sequenceLevelReal D.level x}/2) := by
  let := M.probability
  have hP (i : ℕ) : IsProbabilityMeasure (radialLaw W a z (D.boundary i)) :=
    radialLaw_probability W hW a ha z hz _ (D.boundary_pos _) (D.boundary_le _)
  induction n with
  | zero =>
    let := hP 0
    simp [testFailure,failed]
  | succ n ih =>
    let := hP (n+1)
    have hraw := M.testFailure_raw z hz D n
    obtain ⟨s,hs,hgap⟩ := D.gap n
    have hl := M.stopped_success_lower hW z hz (D.boundary n) (D.start n)
      (D.start_pos n) (D.start_le n) (D.boundary_le n) s hs hgap D.level
      (D.threshold n) (D.threshold_nonneg n) (M.testFailure z D n) hraw
    rw [←D.next] at hl
    have hlr := ENNReal.toReal_mono (measure_ne_top _ _) hl
    simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat] at hlr
    change 1/2*M.law.real {x | D.threshold n ≤ sequenceLevelReal D.level x}*
      (radialLaw W a z (D.boundary (n+1))).real (M.testFailure z D n) ≤
      (radialLaw W a z (D.boundary (n+1))).real
        (M.testFailure z D n∩M.testSuccess z D n) at hlr
    have hm : MeasurableSet (M.testSuccess z D n) := by
      have hT := radialTime_stopping a (by linarith) z hz _
        (testEndpoint_pos (a := a) _ (D.start_pos n) D.level)
        ((testEndpoint_le (ha := ha) _ (D.start_pos n).le _).trans
          ((D.start_le n).trans (D.boundary_le n)))
      exact hT.measurableSpace_le _ (measurableSet_le measurable_const
        (M.stoppedTest_measurable z hz (D.start n) (D.start_pos n)
          ((D.start_le n).trans (D.boundary_le n)) D.level))
    have hsplit := measureReal_inter_add_sdiff (μ := radialLaw W a z (D.boundary (n+1)))
      (s := M.testFailure z D n) hm
    have hn : D.boundary (n+1) ≤ D.boundary n := by
      rw [D.next]
      exact (testEndpoint_le (ha := ha) _ (D.start_pos n).le _).trans (D.start_le n)
    have he := congrArg ENNReal.toReal (radialLaw_consistent_le W hW a ha z hz
      (D.boundary n) (D.boundary (n+1)) (D.boundary_pos _) hn (D.boundary_le n)
      (M.testFailure z D n) hraw)
    change (radialLaw W a z (D.boundary (n+1))).real (M.testFailure z D n)=
      (radialLaw W a z (D.boundary n)).real (M.testFailure z D n) at he
    have hp : M.law.real {x | D.threshold n ≤ sequenceLevelReal D.level x} ≤ 1 := measureReal_le_one
    calc
      _ ≤ (1-M.law.real {x | D.threshold n ≤ sequenceLevelReal D.level x}/2)*
          (radialLaw W a z (D.boundary (n+1))).real (M.testFailure z D n) := by
        change (radialLaw W a z (D.boundary (n+1))).real (M.testFailure z D n \ M.testSuccess z D n) ≤ _
        nlinarith
      _ = (1-M.law.real {x | D.threshold n ≤ sequenceLevelReal D.level x}/2)*
          (radialLaw W a z (D.boundary n)).real (M.testFailure z D n) := by rw [he]
      _ ≤ (1-M.law.real {x | D.threshold n ≤ sequenceLevelReal D.level x}/2)*
          (∏i∈Finset.range n,(1-M.law.real {x | D.threshold i ≤ sequenceLevelReal D.level x}/2)) :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      _ = _ := by rw [Finset.prod_range_succ]; ring

lemma testFailure_exponential [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (z : ℂ) (hz : 0 < z.im) (D : RadialTestSchedule a z.im) (n : ℕ)
    (B : ℝ) (hB : B ≤ ∑i∈Finset.range n,M.law.real {x | D.threshold i ≤ sequenceLevelReal D.level x}/2) :
    radialLaw W a z (D.boundary n) (M.testFailure z D n) ≤ ENNReal.ofReal (Real.exp (-B)) := by
  let := M.probability
  have := radialLaw_probability W hW a ha z hz (D.boundary n) (D.boundary_pos _) (D.boundary_le _)
  have hp (i : ℕ) : M.law.real {x | D.threshold i ≤ sequenceLevelReal D.level x}/2 ≤ 1 := by
    have : M.law.real {x | D.threshold i ≤ sequenceLevelReal D.level x} ≤ 1 := measureReal_le_one
    linarith
  have hh := (M.testFailure_product hW z hz D n).trans
    ((product_le_exp _ hp n).trans (Real.exp_le_exp.mpr (neg_le_neg hB)))
  simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using ENNReal.ofReal_le_ofReal hh

 
theorem testFailure_chordal [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (z : ℂ) (hz : 0 < z.im) (D : RadialTestSchedule a z.im) (n : ℕ)
    (ρ : ℝ) (hρ : 0 < ρ) (hρσ : ρ ≤ D.boundary n)
    (s : ℝ) (hs : Jacobi.mixingTime (4*a) ≤ s) (hgap : ρ=D.boundary n*Real.exp (-2*a*s))
    (B : ℝ) (hB : B ≤ ∑i∈Finset.range n,M.law.real {x | D.threshold i ≤ sequenceLevelReal D.level x}/2) :
    W (M.testFailure z D n∩{b | radialTime a b.1 z ρ≠∞}) ≤
      Jacobi.visitConstant a*ENNReal.ofReal ((ρ/z.im)^(alpha a))*ENNReal.ofReal (Real.exp (-B)) := by
  have hr := M.testFailure_raw z hz D n
  have hh := radial_change_law_past_bound W hW a ha z hz (D.boundary n) ρ hρ hρσ
    (D.boundary_le n) s hs hgap (M.testFailure z D n) hr
  rw [radialLaw_consistent_le W hW a ha z hz _ ρ hρ hρσ (D.boundary_le n) _ hr] at hh
  exact hh.trans (mul_le_mul le_rfl (M.testFailure_exponential hW z hz D n B hB) zero_le zero_le)

end CenteredMomentModel
end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator LoewnerRestart

 
def batchRadius (a : ℝ) (l n i : ℕ) : ℝ :=
  Real.exp (-(n:ℝ)^2-2*a*(i:ℝ)*((l:ℝ)+(n:ℝ)))

lemma batchRadius_pos (a : ℝ) (l n i : ℕ) : 0 < batchRadius a l n i := Real.exp_pos _

lemma batchRadius_zero (a : ℝ) (l n : ℕ) : batchRadius a l n 0=Real.exp (-(n:ℝ)^2) := by
  simp [batchRadius]

lemma batchRadius_succ (a : ℝ) (l n i : ℕ) :
    batchRadius a l n (i+1)=batchRadius a l n i*Real.exp (-2*a*l)*Real.exp (-2*a*n) := by
  simp only [batchRadius,←Real.exp_add,Nat.cast_add,Nat.cast_one]
  congr 1
  ring

lemma batchRadius_antitone (a : ℝ) (ha : 0 ≤ a) (l n : ℕ) : Antitone (batchRadius a l n) := by
  intro i j hij
  apply Real.exp_le_exp.mpr
  have hj : (i:ℝ) ≤ j := by exact_mod_cast hij
  have hm : 0 ≤ 2*a*((l:ℝ)+(n:ℝ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hj hm]

lemma mixingTime_nonneg (a : ℝ) : 0 ≤ Jacobi.mixingTime (4*a) := by
  unfold Jacobi.mixingTime Jacobi.majorantBase
  positivity

def BatchReady (a : ℝ) (n : ℕ) : Prop :=
  3 ≤ n ∧ Jacobi.mixingTime (4*a) ≤ (n:ℝ)-Real.log 2/(2*a) ∧
  400*Real.exp (-(n:ℝ)^2) ≤ Real.exp (-(n:ℝ))*Real.exp (-2*a*Jacobi.mixingTime (4*a))

lemma eventually_batchReady (a : ℝ) (_ha : 0 < a) : ∀ᶠ n in atTop,BatchReady a n := by
  have hR (x : ℝ) : ∀ᶠ n : ℕ in atTop,x ≤ (n:ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop x)
  filter_upwards [eventually_ge_atTop 3,hR (Jacobi.mixingTime (4*a)+Real.log 2/(2*a)),
    hR (Real.log 400+2*a*Jacobi.mixingTime (4*a))] with n hn hmix hinit
  refine ⟨hn,by linarith,?_⟩
  have hnR : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (n:ℝ) ≤ (n:ℝ)^2-(n:ℝ) := by nlinarith
  rw [show (400:ℝ)=Real.exp (Real.log 400) by rw [Real.exp_log (by norm_num)],
    ←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

lemma BatchReady.mixing {a : ℝ} (ha : 0<a) {n : ℕ} (h : BatchReady a n) :
    Jacobi.mixingTime (4*a) ≤ (n:ℝ) := by
  have : 0 ≤ Real.log 2/(2*a) := div_nonneg (Real.log_nonneg (by norm_num)) (by positivity)
  linarith [h.2.1]

 

def batchBoundary (a y : ℝ) (l n : ℕ) : ℕ→ℝ
  | 0 => y
  | i+1 => 400*batchRadius a l n i*Real.exp (-2*a*l)

lemma batchBoundary_pos (a y : ℝ) (hy : 0<y) (l n i : ℕ) : 0<batchBoundary a y l n i := by
  cases i with
  | zero => exact hy
  | succ i => dsimp [batchBoundary]; have := batchRadius_pos a l n i; positivity

lemma batchBoundary_start (a y : ℝ) (ha : 0<a) (hy : 0<y) (l n : ℕ)
    (h : BatchReady a n) (hyn : Real.exp (-(n:ℝ)) ≤ y) (i : ℕ) :
    400*batchRadius a l n i ≤ batchBoundary a y l n i ∧
      ∃s : ℝ,Jacobi.mixingTime (4*a) ≤ s ∧
        400*batchRadius a l n i=batchBoundary a y l n i*Real.exp (-2*a*s) := by
  cases i with
  | zero =>
    apply clock_gap_of_small a ha _ (mixingTime_nonneg a) y _ hy
      (by have := batchRadius_pos a l n 0; positivity)
    rw [batchRadius_zero]
    exact h.2.2.trans (mul_le_mul_of_nonneg_right hyn (Real.exp_pos _).le)
  | succ i =>
    have hg : 400*batchRadius a l n (i+1)=batchBoundary a y l n (i+1)*Real.exp (-2*a*n) := by
      rw [batchRadius_succ,batchBoundary]; ring
    refine ⟨?_,(n:ℝ),h.mixing ha,hg⟩
    rw [hg]
    exact mul_le_of_le_one_right (batchBoundary_pos a y hy l n _).le
      (Real.exp_le_one_iff.mpr (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; nlinarith))

lemma batchBoundary_le (a y : ℝ) (ha : 0<a) (hy : 0<y) (l n : ℕ)
    (h : BatchReady a n) (hyn : Real.exp (-(n:ℝ)) ≤ y) (i : ℕ) :
    batchBoundary a y l n i ≤ y := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    change 400*batchRadius a l n i*Real.exp (-2*a*l) ≤ y
    have hstart := (batchBoundary_start a y ha hy l n h hyn i).1.trans ih
    refine (mul_le_of_le_one_right (by have := batchRadius_pos a l n i; positivity) ?_).trans hstart
    exact Real.exp_le_one_iff.mpr (by have : (0:ℝ) ≤ l := Nat.cast_nonneg l; nlinarith)

def batchSchedule (a y : ℝ) (ha : 0<a) (hy : 0<y) (l n : ℕ)
    (h : BatchReady a n) (hyn : Real.exp (-(n:ℝ)) ≤ y) (b : ℕ→ℝ) (hb : ∀i,0 ≤ b i) :
    RadialTestSchedule a y where
  start i := 400*batchRadius a l n i
  boundary := batchBoundary a y l n
  level := l
  threshold := b
  boundary_pos := batchBoundary_pos a y hy l n
  boundary_le := batchBoundary_le a y ha hy l n h hyn
  start_pos i := by have := batchRadius_pos a l n i; positivity
  start_le i := (batchBoundary_start a y ha hy l n h hyn i).1
  next _ := rfl
  threshold_nonneg := hb
  gap i := (batchBoundary_start a y ha hy l n h hyn i).2

lemma batch_final_gap (a y : ℝ) (ha : 0<a) (l n J : ℕ) (hJ : 0<J) :
    800*batchRadius a l n J=batchBoundary a y l n J*
      Real.exp (-2*a*((n:ℝ)-Real.log 2/(2*a))) := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hJ.ne'
  rw [batchRadius_succ,batchBoundary,
    show -2*a*((n:ℝ)-Real.log 2/(2*a))= -2*a*n+Real.log 2 by field_simp; ring,
    Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
  ring

lemma batch_final_le (a y : ℝ) (ha : 0<a) (hy : 0<y) (l n J : ℕ) (hJ : 0<J)
    (h : BatchReady a n) : 800*batchRadius a l n J ≤ batchBoundary a y l n J := by
  rw [batch_final_gap a y ha l n J hJ]
  apply mul_le_of_le_one_right (batchBoundary_pos a y hy l n J).le
  apply Real.exp_le_one_iff.mpr
  have ht := (mixingTime_nonneg a).trans h.2.1
  nlinarith

end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator
open LoewnerRestart CompactSequence MomentBatches

lemma sum_getD_eq_map_sum (L : List ℝ) (f : ℝ→ℝ) :
    (∑i∈Finset.range L.length,f (L.getD i 1))=(L.map f).sum := by
  rw [←Fin.sum_univ_eq_sum_range]
  simp only [List.getD_eq_getElem _ _ (Fin.isLt _)]
  rw [←List.sum_ofFn]
  change (List.ofFn (f ∘ (fun i : Fin L.length=>L[i.1]))).sum = _
  rw [←List.map_ofFn,List.ofFn_getElem]

namespace CenteredMomentModel
variable {κ a : ℝ} {ha : 1/4 < a} {W : Measure GDriver} (M : CenteredMomentModel κ a ha W)

def batchLevel (n : ℕ) : ℕ := momentLevel M.law sequenceMassReal sequenceLevelReal n

def testCount (n : ℕ) : ℕ := (noncleanup (moment M.law sequenceMassReal) n).length

def testThreshold (n i : ℕ) : ℝ := (noncleanup (moment M.law sequenceMassReal) n).getD i 1

def finalRadius (n : ℕ) : ℝ := batchRadius a (M.batchLevel n) n (M.testCount n)

lemma finalRadius_pos (n : ℕ) : 0<M.finalRadius n := batchRadius_pos ..

lemma finalRadius_le (n : ℕ) : M.finalRadius n ≤ Real.exp (-(n:ℝ)^2) := by
  rw [←batchRadius_zero a (M.batchLevel n) n]
  exact batchRadius_antitone a (by linarith) _ _ (Nat.zero_le _)

lemma testThreshold_pos (n i : ℕ) : 0 < M.testThreshold n i := by
  classical
  unfold testThreshold
  by_cases hi : i < (noncleanup (moment M.law sequenceMassReal) n).length
  · rw [List.getD_eq_getElem _ _ hi]
    have hm := List.getElem_mem hi
    obtain ⟨k,hk,h⟩ := List.mem_flatMap.mp hm
    obtain ⟨_,he⟩ := List.mem_replicate.mp h
    rw [he]
    positivity
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    norm_num

 

def testIndex (n : ℕ) (hn : 0<n) (i : ℕ) (hi : i<M.testCount n) : M.Entries :=
  ⟨⟨n,hn⟩,⟨i,by
    change i<(batch (moment M.law sequenceMassReal) n).length
    change i < (noncleanup (moment M.law sequenceMassReal) n).length at hi
    simpa only [batch,List.length_append,List.length_singleton] using Nat.lt_succ_of_lt hi⟩⟩

lemma testIndex_threshold (n : ℕ) (hn : 0<n) (i : ℕ) (hi : i<M.testCount n) :
    M.entryThreshold (M.testIndex n hn i hi)=M.testThreshold n i := by
  simp only [entryThreshold,threshold,testIndex,batch,List.getElem_append_left (by exact hi),
    testThreshold,List.getD_eq_getElem _ _ (by exact hi)]

lemma testIndex_radius (n : ℕ) (hn : 0<n) (i : ℕ) (hi : i<M.testCount n) :
    M.entryRadius (M.testIndex n hn i hi)=batchRadius a (M.batchLevel n) n i := rfl

lemma cleanup_radius (n : ℕ) (hn : 0<n) :
    M.entryRadius (cleanupIndex (moment M.law sequenceMassReal) n hn)=M.finalRadius n := rfl

lemma batch_success (n : ℕ) (hn : 3≤n) :
    (2:ℝ)^n/8 ≤ ∑i∈Finset.range (M.testCount n),
      M.law.real {x | M.testThreshold n i ≤ sequenceLevelReal (M.batchLevel n) x} := by
  let := M.probability
  have hnp : 0<n := by omega
  have hfin := finite_multiplicity_support hnp (M.moments_positive 1 le_rfl)
    (M.moments_positive n hnp) (M.moments_positive (n+1) (by omega))
    (mean_pow_le_moment M.law sequenceMassReal (Eventually.of_forall sequenceMassReal_nonneg)
      (by simpa only [pow_one] using M.integrable_moments 1) n (M.integrable_moments n))
  change _ ≤ ∑i∈Finset.range (noncleanup (moment M.law sequenceMassReal) n).length,
    (fun b=>M.law.real {x | b ≤ sequenceLevelReal (M.batchLevel n) x})
      ((noncleanup (moment M.law sequenceMassReal) n).getD i 1)
  rw [sum_getD_eq_map_sum _ (fun b=>M.law.real {x | b ≤ sequenceLevelReal (M.batchLevel n) x}),
    noncleanup_sum,sum_eq_tsum_multiplicity hfin]
  exact M.success n hn

lemma testCount_pos (n : ℕ) (hn : 3≤n) : 0<M.testCount n := by
  have hs := M.batch_success n hn
  by_contra! hh
  have he := Nat.eq_zero_of_le_zero hh
  rw [he] at hs
  simp only [Finset.range_zero,Finset.sum_empty] at hs
  have : (0:ℝ)<2^n/8 := by positivity
  linarith

lemma batch_half_success (n : ℕ) (hn : 3≤n) :
    (2:ℝ)^n/16 ≤ ∑i∈Finset.range (M.testCount n),
      M.law.real {x | M.testThreshold n i ≤ sequenceLevelReal (M.batchLevel n) x}/2 := by
  rw [←Finset.sum_div]
  linarith [M.batch_success n hn]

def batchFailures (z : ℂ) (n : ℕ) : Set GDriver :=
  {b | ∀i<M.testCount n,¬(ENNReal.ofReal (M.testThreshold n i) ≤
    M.stoppedTest z (400*batchRadius a (M.batchLevel n) n i) (M.batchLevel n) b)}

lemma batchFailures_eq_testFailure (z : ℂ) (hz : 0<z.im) (n : ℕ)
    (hr : BatchReady a n) (hy : Real.exp (-(n:ℝ)) ≤ z.im) :
    M.batchFailures z n=M.testFailure z
      (batchSchedule a z.im (by linarith) hz (M.batchLevel n) n hr hy
        (M.testThreshold n) (fun i=>(M.testThreshold_pos n i).le)) (M.testCount n) := by
  ext b
  simp only [batchFailures,mem_ofPred_eq,testFailure,AdaptedFailure.failed_iff]
  rfl

lemma batch_failures_measurable (z : ℂ) (hz : 0<z.im) (n : ℕ)
    (hr : BatchReady a n) (hy : Real.exp (-(n:ℝ)) ≤ z.im) :
    MeasurableSet (M.batchFailures z n) := by
  rw [M.batchFailures_eq_testFailure z hz n hr hy]
  exact (radialTime_stopping a (by linarith) z hz _
    (batchBoundary_pos a z.im hz _ _ _) (batchBoundary_le a z.im (by linarith) hz _ _ hr hy _)).measurableSpace_le _
    (M.testFailure_raw z hz _ _)

 

theorem batch_failure_chordal [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (z : ℂ) (hz : 0<z.im) (n : ℕ) (hr : BatchReady a n)
    (hy : Real.exp (-(n:ℝ)) ≤ z.im) :
    W (M.batchFailures z n∩{b | radialTime a b.1 z (800*M.finalRadius n)≠∞}) ≤
      Jacobi.visitConstant a*ENNReal.ofReal ((800*M.finalRadius n/z.im)^(alpha a))*
        ENNReal.ofReal (Real.exp (-((2:ℝ)^n/16))) := by
  rw [M.batchFailures_eq_testFailure z hz n hr hy]
  apply M.testFailure_chordal hW z hz _ _ _
    (by have := M.finalRadius_pos n; positivity)
    (batch_final_le a z.im (by linarith) hz _ _ _ (M.testCount_pos n hr.1) hr)
    ((n:ℝ)-Real.log 2/(2*a)) hr.2.1
    (batch_final_gap a z.im (by linarith) _ _ _ (M.testCount_pos n hr.1))
    ((2:ℝ)^n/16)
  exact M.batch_half_success n hr.1

end CenteredMomentModel
end SLEExactGauge.CenteredMoments
end
end

end OAI
