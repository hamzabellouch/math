import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterra
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedBoundedEndpointTransport
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedEndpointHistories
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedBranchingBlocks
import OAI.MathematicalPhysics.Boltzmann.Branching.ScaledBlockMass
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedDampedBalance

namespace OAI

section

/-! # Finite positive gain histories with their survival weights -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.DampedGainHistory

def step (a : ℝ) (K : Kernel KineticPhase Velocity)
    (W : KineticPhase × ℝ → ℝ≥0∞) (f : KineticPhase → ℝ≥0∞)
    (z : KineticPhase) : ℝ≥0∞ :=
  ∫⁻ s in Ioc a z.1.1, W (z,s)*∫⁻ v, f ((PositiveIteration.flight z s).1,v)
    ∂K (PositiveIteration.flight z s)

theorem step_slab_mono {a T : ℝ} (K : Kernel KineticPhase Velocity)
    (W : KineticPhase × ℝ → ℝ≥0∞) {f g : KineticPhase → ℝ≥0∞}
    (h : ∀ z, z.1.1 ∈ Icc a T → f z ≤ g z)
    {z : KineticPhase} (hz : z.1.1 ∈ Icc a T) : step a K W f z ≤ step a K W g z := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  apply mul_le_mul' le_rfl
  apply lintegral_mono
  intro v
  exact h _ ⟨hs.1.le,hs.2.trans hz.2⟩

theorem step_measurable (a : ℝ) (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {W : KineticPhase × ℝ → ℝ≥0∞} (hW : Measurable W)
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) : Measurable (step a K W f) := by
  have hflight : Measurable (fun p : KineticPhase × ℝ => PositiveIteration.flight p.1 p.2) := by
    unfold PositiveIteration.flight
    fun_prop
  let J := K.comap (fun p : KineticPhase × ℝ => PositiveIteration.flight p.1 p.2) hflight
  have hm : Measurable (fun p : (KineticPhase × ℝ) × Velocity =>
      f ((PositiveIteration.flight p.1.1 p.1.2).1,p.2)) :=
    hf.comp (((hflight.comp measurable_fst).fst).prodMk measurable_snd)
  have hi : Measurable (fun p : KineticPhase × ℝ =>
      W p*∫⁻ v, f ((PositiveIteration.flight p.1 p.2).1,v) ∂K (PositiveIteration.flight p.1 p.2)) :=
    hW.mul (hm.lintegral_kernel_prod_right' (κ := J))
  let D : Set (KineticPhase × ℝ) := {p | a < p.2 ∧ p.2 ≤ p.1.1.1}
  have hD : MeasurableSet D := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst.fst.fst)
  have h : Measurable (fun z : KineticPhase => ∫⁻ s : ℝ,
      D.indicator (fun p : KineticPhase × ℝ => W p*∫⁻ v,
        f ((PositiveIteration.flight p.1 p.2).1,v) ∂K (PositiveIteration.flight p.1 p.2)) (z,s)) :=
    (hi.indicator hD).lintegral_prod_right'
  convert h using 1
  funext z
  rw [step,← lintegral_indicator measurableSet_Ioc]
  rfl

theorem step_add (a : ℝ) (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {W : KineticPhase × ℝ → ℝ≥0∞} (hW : Measurable W)
    {f g : KineticPhase → ℝ≥0∞} (hf : Measurable f) :
    step a K W (f+g) = step a K W f+step a K W g := by
  funext z
  unfold step
  simp only [Pi.add_apply]
  have hi (s : ℝ) : Measurable (fun v => f ((PositiveIteration.flight z s).1,v)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  simp_rw [lintegral_add_left (hi _),mul_add]
  apply lintegral_add_left
  exact (hW.comp (measurable_const.prodMk measurable_id)).mul
    (PositiveIteration.step_inner_measurable K hf z)

def iterate (a : ℝ) (K : Kernel KineticPhase Velocity)
    (W : KineticPhase × ℝ → ℝ≥0∞) (f : KineticPhase → ℝ≥0∞) : ℕ → KineticPhase → ℝ≥0∞
  | 0 => f
  | n+1 => step a K W (iterate a K W f n)

theorem iterate_measurable (a : ℝ) (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {W : KineticPhase × ℝ → ℝ≥0∞} (hW : Measurable W)
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    Measurable (iterate a K W f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact step_measurable a K hW ih

def partialSum (a : ℝ) (K : Kernel KineticPhase Velocity)
    (W : KineticPhase × ℝ → ℝ≥0∞) (d : KineticPhase → ℝ≥0∞) : ℕ → KineticPhase → ℝ≥0∞
  | 0 => 0
  | n+1 => d+step a K W (partialSum a K W d n)

/-- Positive remainders imply domination of every finite collection of collision depths. -/
theorem partialSum_le {a T : ℝ} (K : Kernel KineticPhase Velocity)
    (W : KineticPhase × ℝ → ℝ≥0∞) {f d : KineticPhase → ℝ≥0∞}
    (h : ∀ z, z.1.1 ∈ Icc a T → d z+step a K W f z ≤ f z) (n : ℕ) :
    ∀ z, z.1.1 ∈ Icc a T → partialSum a K W d n z ≤ f z := by
  induction n with
  | zero => exact fun _ _ => zero_le
  | succ n ih =>
    intro z hz
    exact (add_le_add le_rfl (step_slab_mono K W ih hz)).trans (h z hz)

end BoltzmannNonuniqueness.DampedGainHistory

end

end

section

/-! # Bounded measurable tests of a damped positive source -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.WeakTime

def dampedTimeWeight (C s t : ℝ) : ℝ → ℝ :=
  (Ioc s t).indicator (fun r => Real.exp (-C*(t-r)))

theorem dampedTimeWeight_measurable (C s t : ℝ) : Measurable (dampedTimeWeight C s t) :=
  (by fun_prop : Measurable (fun r : ℝ => Real.exp (-C*(t-r)))).indicator measurableSet_Ioc

theorem dampedTimeWeight_bounds {C : ℝ} (hC : 0 ≤ C) (s t r : ℝ) :
    0 ≤ dampedTimeWeight C s t r ∧ dampedTimeWeight C s t r ≤ 1 := by
  by_cases hr : r ∈ Ioc s t
  · rw [dampedTimeWeight,indicator_of_mem hr]
    exact ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (by nlinarith [hr.2])⟩
  · simp only [dampedTimeWeight,indicator_of_notMem hr,le_refl,zero_le_one,and_self]

theorem dampedSourceIncrement_integral (μ : Measure (ℝ × Phase))
    {a b C s t : ℝ} (hs : a < s) (ht : t < b) {ψ : Phase → ℝ} (hψ : Measurable ψ) :
    (∫ p, ψ p ∂dampedSourceIncrement a b C s t μ) =
      ∫ z, dampedTimeWeight C s t z.1*ψ z.2 ∂μ := by
  have hW : AEMeasurable (fun z : ℝ × Phase => slabExponential a b C z.1) μ := by
    simpa only [Function.comp_def] using
      ((slabExponential_measurable a b C).comp measurable_fst).aemeasurable (μ := μ)
  rw [dampedSourceIncrement,integral_smul_measure,ENNReal.toReal_ofReal (Real.exp_pos _).le,
    smul_eq_mul,phaseIncrement_integral _ _ _ hψ]
  change Real.exp (-C*t)*(∫ z, (Ioc s t).indicator (fun _ => (1 : ℝ)) z.1*ψ z.2
    ∂positiveDensityMeasure μ (fun z => slabExponential a b C z.1)) = _
  rw [positiveDensityMeasure_integral hW
    (ae_of_all _ (fun z => slabExponential_nonneg a b C z.1)),← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    dsimp only
    by_cases hz : z.1 ∈ Ioc s t
    · have hab : z.1 ∈ Ioo a b := ⟨hs.trans hz.1,hz.2.trans_lt ht⟩
      rw [indicator_of_mem hz,one_mul,slabExponential,indicator_of_mem hab,
        dampedTimeWeight,indicator_of_mem hz]
      calc
        _ = (Real.exp (-C*t)*Real.exp (C*z.1))*ψ z.2 := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring
    · simp only [indicator_of_notMem hz,zero_mul,mul_zero,dampedTimeWeight])

theorem dampedSourceIncrement_weighted_integral (μ : Measure (ℝ × Phase))
    {a b C s t : ℝ} (hs : a < s) (ht : t < b) {ψ β : Phase → ℝ}
    (hψ : Measurable ψ) (hβ : Measurable β) (hβn : ∀ p, 0 ≤ β p) :
    (∫ p, ψ p ∂dampedSourceIncrement a b C s t (weightedPhaseSource μ β)) =
      ∫ z, (dampedTimeWeight C s t z.1*ψ z.2)*β z.2 ∂μ := by
  rw [dampedSourceIncrement_integral _ hs ht hψ]
  have hm : AEMeasurable (fun z : ℝ × Phase => β z.2) μ := by
    simpa only [Function.comp_def] using (hβ.comp measurable_snd).aemeasurable (μ := μ)
  exact positiveDensityMeasure_integral hm (ae_of_all _ (fun z => hβn z.2)) _

def dampedPhaseTest (C s t : ℝ) (ψ β : Phase → ℝ) (z : ℝ × Phase) : ℝ :=
  (dampedTimeWeight C s t z.1*ψ z.2)*β z.2

theorem dampedPhaseTest_measurable (C s t : ℝ) {ψ β : Phase → ℝ}
    (hψ : Measurable ψ) (hβ : Measurable β) : Measurable (dampedPhaseTest C s t ψ β) := by
  exact (((dampedTimeWeight_measurable C s t).comp measurable_fst).mul
    (hψ.comp measurable_snd)).mul (hβ.comp measurable_snd)

theorem dampedPhaseTest_bound {C : ℝ} (hC : 0 ≤ C) (s t : ℝ) {ψ β : Phase → ℝ}
    {P B : ℝ} (hψ : ∀ p, |ψ p| ≤ P) (hβ : ∀ p, |β p| ≤ B) (z : ℝ × Phase) :
    |dampedPhaseTest C s t ψ β z| ≤ P*B := by
  have hw := dampedTimeWeight_bounds hC s t z.1
  have hP : 0 ≤ P := (abs_nonneg (ψ 0)).trans (hψ 0)
  rw [dampedPhaseTest,abs_mul,abs_mul,abs_of_nonneg hw.1]
  calc
    _ ≤ (1*P)*B := mul_le_mul
      (mul_le_mul hw.2 (hψ z.2) (abs_nonneg _) zero_le_one)
      (hβ z.2) (abs_nonneg _) (by positivity)
    _ = _ := by rw [one_mul]

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Finite collision-depth sums and their positive remainder -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.DampedGainHistory

theorem partialSum_measurable (a : ℝ) (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {W : KineticPhase × ℝ → ℝ≥0∞} (hW : Measurable W)
    {d : KineticPhase → ℝ≥0∞} (hd : Measurable d) (n : ℕ) :
    Measurable (partialSum a K W d n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact hd.add (step_measurable a K hW ih)

theorem partialSum_succ (a : ℝ) (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {W : KineticPhase × ℝ → ℝ≥0∞} (hW : Measurable W)
    {d : KineticPhase → ℝ≥0∞} (hd : Measurable d) (n : ℕ) :
    partialSum a K W d (n+1) = partialSum a K W d n+iterate a K W d n := by
  induction n with
  | zero => funext z; simp [partialSum,iterate,step]
  | succ n ih =>
    change d+step a K W (partialSum a K W d (n+1)) =
      partialSum a K W d (n+1)+step a K W (iterate a K W d n)
    conv_lhs => rw [ih]
    rw [step_add a K hW (partialSum_measurable a K hW hd n)]
    funext z
    simp only [partialSum,Pi.add_apply,add_assoc]

theorem partialSum_eq (a : ℝ) (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {W : KineticPhase × ℝ → ℝ≥0∞} (hW : Measurable W)
    {d : KineticPhase → ℝ≥0∞} (hd : Measurable d) (n : ℕ) (z : KineticPhase) :
    partialSum a K W d n z = ∑ j ∈ Finset.range n, iterate a K W d j z := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih => rw [partialSum_succ a K hW hd,Finset.sum_range_succ]; exact congrArg (·+_) ih

theorem finite_histories_le {a T : ℝ} (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {W : KineticPhase × ℝ → ℝ≥0∞} (hW : Measurable W)
    {f d : KineticPhase → ℝ≥0∞} (hd : Measurable d)
    (h : ∀ z, z.1.1 ∈ Icc a T → d z+step a K W f z ≤ f z)
    (n : ℕ) {z : KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    ∑ j ∈ Finset.range n, iterate a K W d j z ≤ f z := by
  rw [← partialSum_eq a K hW hd]
  exact partialSum_le K W h n z hz

theorem all_histories_le {a T : ℝ} (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {W : KineticPhase × ℝ → ℝ≥0∞} (hW : Measurable W)
    {f d : KineticPhase → ℝ≥0∞} (hd : Measurable d)
    (h : ∀ z, z.1.1 ∈ Icc a T → d z+step a K W f z ≤ f z)
    {z : KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    ∑' j, iterate a K W d j z ≤ f z :=
  ENNReal.tsum_le_of_sum_range_le (fun n => finite_histories_le K hW hd h n hz)

end BoltzmannNonuniqueness.DampedGainHistory

end

end

section

/-! # Factorial bounds on finite collision histories in bounded-rate regions -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.DampedGainHistory

theorem iterate_factorial_bound {a T C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (K : Kernel KineticPhase Velocity) {W : KineticPhase × ℝ → ℝ≥0∞}
    (hW : ∀ z, z.1.1 ∈ Icc a T → ∀ s ∈ Ioc a z.1.1, W (z,s) ≤ 1)
    (hK : ∀ z, z.1.1 ∈ Icc a T → K z univ ≤ ENNReal.ofReal C)
    {f : KineticPhase → ℝ≥0∞} (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ ENNReal.ofReal B)
    (n : ℕ) : ∀ z, z.1.1 ∈ Icc a T →
      iterate a K W f n z ≤ ENNReal.ofReal (B*C^n*(z.1.1-a)^n/(n.factorial:ℝ)) := by
  induction n with
  | zero => simpa only [iterate,pow_zero,mul_one,Nat.factorial_zero,Nat.cast_one,div_one] using hf
  | succ n ih =>
    intro z hz
    let b : ℝ → ℝ := fun s => B*C^n*(s-a)^n/(n.factorial:ℝ)*C
    have hb (s : ℝ) (hs : a ≤ s) : 0 ≤ b s := by dsimp [b]; positivity
    have hi : IntegrableOn b (Ioc a z.1.1) := by
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.1).mp
        ((show Continuous b by dsimp [b]; fun_prop).intervalIntegrable a z.1.1)
    change step a K W (iterate a K W f n) z ≤ _
    unfold step
    calc
      _ ≤ ∫⁻ s in Ioc a z.1.1, ENNReal.ofReal (b s) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hst : s ∈ Icc a T := ⟨hs.1.le,hs.2.trans hz.2⟩
        calc
          _ ≤ 1*∫⁻ v, iterate a K W f n ((PositiveIteration.flight z s).1,v)
              ∂K (PositiveIteration.flight z s) := mul_le_mul' (hW z hz s hs) le_rfl
          _ ≤ ∫⁻ _v, ENNReal.ofReal (B*C^n*(s-a)^n/(n.factorial:ℝ))
              ∂K (PositiveIteration.flight z s) := by
                rw [one_mul]
                exact lintegral_mono (fun v => ih _ hst)
          _ = ENNReal.ofReal (B*C^n*(s-a)^n/(n.factorial:ℝ))*K (PositiveIteration.flight z s) univ := by
            rw [lintegral_const,mul_comm]
          _ ≤ ENNReal.ofReal (B*C^n*(s-a)^n/(n.factorial:ℝ))*ENNReal.ofReal C :=
            mul_le_mul' le_rfl (hK _ hst)
          _ = ENNReal.ofReal (b s) := by
            exact (ENNReal.ofReal_mul (div_nonneg
              (mul_nonneg (mul_nonneg hB (pow_nonneg hC n))
                (pow_nonneg (sub_nonneg.mpr hs.1.le) n))
              (Nat.cast_nonneg _))).symm
      _ = ENNReal.ofReal (∫ s in a..z.1.1, b s) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi]
        · rw [intervalIntegral.integral_of_le hz.1]
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact hb s hs.1.le
      _ = _ := by
        have he : b = fun s => (B*C^n*C/(n.factorial:ℝ))*(s-a)^n := by funext s; dsimp [b]; ring
        rw [he,intervalIntegral.integral_const_mul,
          intervalIntegral.integral_comp_sub_right (fun x : ℝ => x^n),integral_pow]
        simp only [sub_self,zero_pow (Nat.succ_ne_zero n),sub_zero,
          Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
        congr 1
        field_simp

end BoltzmannNonuniqueness.DampedGainHistory

end

end

section

/-! # Nonnegative remainders in the survival-weighted history expansion -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.DampedGainHistory

theorem iterate_slab_mono {a T : ℝ} (K : Kernel KineticPhase Velocity)
    (W : KineticPhase × ℝ → ℝ≥0∞) {f g : KineticPhase → ℝ≥0∞}
    (h : ∀ z, z.1.1 ∈ Icc a T → f z ≤ g z) (n : ℕ) :
    ∀ z, z.1.1 ∈ Icc a T → iterate a K W f n z ≤ iterate a K W g n z := by
  induction n with
  | zero => exact h
  | succ n ih => exact fun _ hz => step_slab_mono K W ih hz

theorem iterate_add (a : ℝ) (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {W : KineticPhase × ℝ → ℝ≥0∞} (hW : Measurable W)
    {f g : KineticPhase → ℝ≥0∞} (hf : Measurable f) (n : ℕ) :
    iterate a K W (f+g) n = iterate a K W f n+iterate a K W g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterate,ih]
    exact step_add a K hW (iterate_measurable a K hW hf n)

theorem iterate_step (a : ℝ) (K : Kernel KineticPhase Velocity)
    (W : KineticPhase × ℝ → ℝ≥0∞) (f : KineticPhase → ℝ≥0∞) (n : ℕ) :
    iterate a K W (step a K W f) n = iterate a K W f (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterate,ih]

theorem residual_expansion {a T : ℝ} (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {W : KineticPhase × ℝ → ℝ≥0∞} (hW : Measurable W)
    {f d : KineticPhase → ℝ≥0∞} (hd : Measurable d)
    (h : ∀ z, z.1.1 ∈ Icc a T → f z ≤ d z+step a K W f z) (n : ℕ) :
    ∀ z, z.1.1 ∈ Icc a T →
      f z ≤ (∑ j ∈ Finset.range n, iterate a K W d j z)+iterate a K W f n z := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,zero_add,iterate,le_refl,implies_true]
  | succ n ih =>
    intro z hz
    have hi := iterate_slab_mono K W h n z hz
    change iterate a K W f n z ≤ iterate a K W (d+step a K W f) n z at hi
    rw [iterate_add a K hW hd,iterate_step] at hi
    change iterate a K W f n z ≤ iterate a K W d n z+iterate a K W f (n+1) z at hi
    calc
      f z ≤ (∑ j ∈ Finset.range n, iterate a K W d j z)+iterate a K W f n z := ih z hz
      _ ≤ (∑ j ∈ Finset.range n, iterate a K W d j z)+
          (iterate a K W d n z+iterate a K W f (n+1) z) := add_le_add le_rfl hi
      _ = _ := by rw [Finset.sum_range_succ,add_assoc]

end BoltzmannNonuniqueness.DampedGainHistory

end

end

section

/-! # Scaled finite histories and terminal survival at the enlarged damping -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedDensityScaled_bounded_history_map (C : ℝ≥0) (b : BeamCoefficients)
    {ρ : ℝ} (hρ : 0 < ρ) (t₀ endTime : ℝ) (x₀ : V) (n : ℕ)
    (p : PhysicalFlightState) {T : ℝ} (hT : ρ*p.1 ≤ T) :
    (((dampedBoundedDensityScaledEvent C b endTime (Real.toNNReal ρ))^n) p).map
      (flightScaleEquiv ρ hρ.ne' x₀) =
      ((dampedBoundedEventKernel C (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀)) T)^n)
        (flightScaleEquiv ρ hρ.ne' x₀ p) := by
  rw [dampedBoundedDensityScaledEvent_pow_map C b hρ t₀ endTime x₀ n p,
    damped_boundedMediumEventKernel_pow_eq_physical C _ _ _ _ hT]

theorem dampedDensityScaled_endpoint_integral (C : ℝ≥0) (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ endTime : ℝ) (x₀ : V) (n : ℕ) (p : PhysicalFlightState) {T : ℝ} (hT : ρ*p.1 ≤ T)
    {F : V × V → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, clockSurvival (Real.toNNReal ρ*C) q.1 * F (finishMediumFlight q)
      ∂((dampedBoundedDensityScaledEvent C b endTime (Real.toNNReal ρ))^n) p) =
    ∫⁻ q, clockSurvival C q.1 *
      F (x₀+ρ⁻¹ • (finishMediumFlight q).1,(finishMediumFlight q).2)
      ∂((dampedBoundedEventKernel C (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀)) T)^n)
        (flightScaleEquiv ρ hρ.ne' x₀ p) := by
  let g : PhysicalFlightState → ℝ≥0∞ := fun q => clockSurvival C q.1 *
    F (x₀+ρ⁻¹ • (finishMediumFlight q).1,(finishMediumFlight q).2)
  have hg : Measurable g := by
    apply (show Measurable (fun q : PhysicalFlightState => clockSurvival C q.1) by
      unfold clockSurvival; fun_prop).mul
    exact hF.comp (by unfold finishMediumFlight; fun_prop)
  have H := congrArg (fun μ : Measure PhysicalFlightState => ∫⁻ q, g q ∂μ)
    (dampedDensityScaled_bounded_history_map C b hρ t₀ endTime x₀ n p hT)
  rw [lintegral_map hg (flightScaleEquiv ρ hρ.ne' x₀).measurable] at H
  calc
    _ = ∫⁻ q, g (flightScaleEquiv ρ hρ.ne' x₀ q)
        ∂((dampedBoundedDensityScaledEvent C b endTime (Real.toNNReal ρ))^n) p := by
      apply lintegral_congr
      intro q
      dsimp only [g]
      rw [finishFlight_scale_inverse]
      change _ = clockSurvival C (ρ*q.1)*F (finishMediumFlight q)
      rw [clockSurvival_scaled C hρ]
    _ = _ := H

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exact physical-time mass of each finite normalized branching block -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedDensityScaledBlockMass (C : ℝ≥0) (b : BeamCoefficients) (endTime ρ : ℝ)
    (x : V) (Δ : ℝ) (v : RetainedState) (κ d : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, ∫⁻ q,
    clockSurvival (Real.toNNReal ρ*C) q.1 *
      (physicalBlockTarget x Δ κ d).indicator 1 (finishMediumFlight q)
    ∂((dampedBoundedDensityScaledEvent C b endTime (Real.toNNReal ρ))^n) (Δ,(x,(v : V)))

theorem dampedDensityScaledBlockMass_eq (C : ℝ≥0) (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ : ℝ) (x : V) (Δ : ℝ) (v : RetainedState) (κ d : ℝ) (N : ℕ) {T : ℝ}
    (hT : ρ*Δ ≤ T) :
    dampedDensityScaledBlockMass C b (t₀+Δ) ρ x Δ v κ d N =
      dampedBoundedBlockMass C (b.normalized ρ t₀ x) (ρ*Δ) T (ρ*Δ,(0,v)) κ d N := by
  unfold dampedDensityScaledBlockMass dampedBoundedBlockMass
  apply Finset.sum_congr rfl
  intro n _hn
  have H := dampedDensityScaled_endpoint_integral C b hρ t₀ (t₀+Δ) x n
    (Δ,(x,(v : V))) hT
    (F := (physicalBlockTarget x Δ κ d).indicator (1 : V × V → ℝ≥0∞))
    (measurable_const.indicator (physicalBlockTarget_measurable _ _ _ _))
  rw [H]
  have ht : ρ*(t₀+Δ-t₀) = ρ*Δ := by ring
  have hp : flightScaleEquiv ρ hρ.ne' x (Δ,(x,(v : V))) = (ρ*Δ,(0,(v : V))) := by
    simp [flightScaleEquiv]
  rw [ht,hp]
  simp_rw [scaled_block_indicator hρ x Δ κ d]
  exact (dampedBoundedWord_integral C (b.normalized ρ t₀ x) (ρ*Δ) T
    (dampedMediumFlightSeed_measurable C (measurable_const.indicator
      (physicalBlockTarget_measurable 0 (ρ*Δ) κ d))) n
        (embedFlightState (ρ*Δ,(0,v)))).symm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Convergence and exhaustion of bounded-rate collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open BoltzmannNonuniqueness.Published
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.DampedGainHistory

theorem sum_iterate_le_exp {a T C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (K : Kernel KineticPhase Velocity) {W : KineticPhase × ℝ → ℝ≥0∞}
    (hW : ∀ z, z.1.1 ∈ Icc a T → ∀ s ∈ Ioc a z.1.1, W (z,s) ≤ 1)
    (hK : ∀ z, z.1.1 ∈ Icc a T → K z univ ≤ ENNReal.ofReal C)
    {d : KineticPhase → ℝ≥0∞} (hd : ∀ z, z.1.1 ∈ Icc a T → d z ≤ ENNReal.ofReal B)
    (n : ℕ) (z : KineticPhase) (hz : z.1.1 ∈ Icc a T) :
    (∑ j ∈ Finset.range n, iterate a K W d j z) ≤
      ENNReal.ofReal (B*Real.exp (C*(z.1.1-a))) := by
  calc
    _ ≤ ∑ j ∈ Finset.range n, ENNReal.ofReal (B*((C*(z.1.1-a))^j/(j.factorial:ℝ))) := by
      apply Finset.sum_le_sum
      intro j _
      convert iterate_factorial_bound hC hB K hW hK hd j z hz using 1
      simp only [mul_pow]
      congr 1
      ring
    _ = ENNReal.ofReal (B*∑ j ∈ Finset.range n, (C*(z.1.1-a))^j/(j.factorial:ℝ)) := by
      rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
      intro j _
      exact mul_nonneg hB (div_nonneg (pow_nonneg (mul_nonneg hC (sub_nonneg.mpr hz.1)) j)
        (Nat.cast_nonneg _))
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (Real.sum_le_exp_of_nonneg (mul_nonneg hC (sub_nonneg.mpr hz.1)) n) hB)

theorem all_histories_le_exp {a T C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (K : Kernel KineticPhase Velocity) {W : KineticPhase × ℝ → ℝ≥0∞}
    (hW : ∀ z, z.1.1 ∈ Icc a T → ∀ s ∈ Ioc a z.1.1, W (z,s) ≤ 1)
    (hK : ∀ z, z.1.1 ∈ Icc a T → K z univ ≤ ENNReal.ofReal C)
    {d : KineticPhase → ℝ≥0∞} (hd : ∀ z, z.1.1 ∈ Icc a T → d z ≤ ENNReal.ofReal B)
    (z : KineticPhase) (hz : z.1.1 ∈ Icc a T) :
    (∑' j, iterate a K W d j z) ≤ ENNReal.ofReal (B*Real.exp (C*(z.1.1-a))) :=
  ENNReal.tsum_le_of_sum_range_le (fun n => sum_iterate_le_exp hC hB K hW hK hd n z hz)

theorem remainder_tendsto_zero {a T C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (K : Kernel KineticPhase Velocity) {W : KineticPhase × ℝ → ℝ≥0∞}
    (hW : ∀ z, z.1.1 ∈ Icc a T → ∀ s ∈ Ioc a z.1.1, W (z,s) ≤ 1)
    (hK : ∀ z, z.1.1 ∈ Icc a T → K z univ ≤ ENNReal.ofReal C)
    {f : KineticPhase → ℝ≥0∞} (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ ENNReal.ofReal B)
    (z : KineticPhase) (hz : z.1.1 ∈ Icc a T) :
    Tendsto (fun n => iterate a K W f n z) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (B*((C*(z.1.1-a))^n/(n.factorial:ℝ))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((FloorSemiring.tendsto_pow_div_factorial_atTop (C*(z.1.1-a))).const_mul B)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  convert iterate_factorial_bound hC hB K hW hK hf n z hz using 1
  simp only [mul_pow]
  congr 1
  ring

/-- The bounded solution is exhausted by its finite positive collision histories. -/
theorem eq_history_sum {a T C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {W : KineticPhase × ℝ → ℝ≥0∞} (hWm : Measurable W)
    (hW : ∀ z, z.1.1 ∈ Icc a T → ∀ s ∈ Ioc a z.1.1, W (z,s) ≤ 1)
    (hK : ∀ z, z.1.1 ∈ Icc a T → K z univ ≤ ENNReal.ofReal C)
    {f d : KineticPhase → ℝ≥0∞} (hd : Measurable d)
    (hf : ∀ z, z.1.1 ∈ Icc a T → f z ≤ ENNReal.ofReal B)
    (heq : ∀ z, z.1.1 ∈ Icc a T → f z = d z+step a K W f z)
    (z : KineticPhase) (hz : z.1.1 ∈ Icc a T) :
    f z = ∑' j, iterate a K W d j z := by
  apply le_antisymm
  · have hsum : Tendsto (fun n => ∑ j ∈ Finset.range n, iterate a K W d j z) atTop
        (𝓝 (∑' j, iterate a K W d j z)) := ENNReal.tendsto_nat_tsum _
    have hr := remainder_tendsto_zero hC hB K hW hK hf z hz
    have hlim := hsum.add hr
    simp only [add_zero] at hlim
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
      (fun n => residual_expansion K hWm hd (fun z hz => (heq z hz).le) n z hz)
  · exact all_histories_le K hWm hd (fun z hz => (heq z hz).ge) hz

end BoltzmannNonuniqueness.DampedGainHistory

end

end

section

/-! # Uniform late-box branching growth in physical time -/

noncomputable section

open Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lateBox_damped_physical_block_growth {d κ : ℝ}
    (hd : 0 < d) (hdsmall : d ≤ 1/2) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ Dmax : ℝ≥0, ∃ N : ℕ, ∃ ε γ₀ : ℝ,
      0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ D : ℝ≥0, referenceClock ≤ D → D ≤ Dmax →
      ∀ {θ η α γ K t : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*(4*A₀) ≤ ε*K → 0 < t →
      ∀ (x : V) (v : RetainedState), (x,(v : V)) ∈ lateBox κ d t →
      let Δ := (8*κ*A₀/K)*t
      (6 : ℝ≥0∞) < dampedDensityScaledBlockMass D
        (GeometricBackground.beamCoefficients hθ hα hγ η ‖transverse x‖)
        (t+Δ) (K/(4*‖transverse x‖)) x Δ v κ d N := by
  obtain ⟨A₀,hA₀,hblock⟩ := uniform_damped_lateBox_geometric_block hd hdsmall hκ hκsmall hg
  refine ⟨A₀,hA₀,?_⟩
  intro Dmax
  obtain ⟨N,ε,γ₀,hε,hεsmall,hγ₀,hgrowth⟩ := hblock Dmax
  refine ⟨N,ε,γ₀,hε,hεsmall,hγ₀,?_⟩
  intro D hD hDmax θ η α γ K t hθ hη hηsmall hα hαsmall hγ hγsmall hK hKlarge ht x v hp
  have hr : 0 < ‖transverse x‖ :=
    (lateBox_geometric_scale hκ hκsmall.le hdsmall ht hp).1
  have hρ : 0 < K/(4*‖transverse x‖) := by positivity
  have hT := (lateBox_block_duration hκ ht hdsmall hK hA₀ hp).2
  dsimp only
  rw [dampedDensityScaledBlockMass_eq D _ hρ t x _ v κ d N hT]
  exact hgrowth D hD hDmax hθ hη hηsmall hα hαsmall hγ hγsmall hK hKlarge ht x v hp

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
