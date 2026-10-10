import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
open Matrix
open scoped InnerProductSpace
variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]

@[simp] theorem timeLaw_eq_volume : timeLaw = (volume : Measure Time) := rfl

instance : IsProbabilityMeasure timeLaw := by
  rw [timeLaw_eq_volume]
  infer_instance

instance : NullSingletonClass timeLaw := by
  rw [timeLaw_eq_volume]
  infer_instance

theorem progressive_zero (P : Measure BrownianPath) :
    Progressive P (fun _ _ => 0) := by
  intro t
  exact measurable_const

@[simp] theorem controlCost_zero (P : Measure BrownianPath) (m : Trial) :
    controlCost P m (fun _ _ => 0) = 0 := by
  simp [controlCost]

@[simp] theorem controlPayoff_zero (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (m : Trial) :
    controlPayoff P f m (fun _ _ => 0) = ∫ ω, f (brownianEval 1 ω) ∂P := by
  simp [controlPayoff]

theorem abs_integral_reward_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (X : BrownianPath → ℝ) :
    |∫ ω, f (X ω) ∂P| ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const
    (μ := P) (f := fun ω => f (X ω)) (C := ‖f‖)
    (Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm (X ω))
  simpa using h

theorem controlPayoff_le_norm (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (v : Time → BrownianPath → ℝ) :
    controlPayoff P f m v ≤ ‖f‖ := by
  unfold controlPayoff
  have h := (abs_integral_reward_le P f
    (fun ω => brownianEval 1 ω + ∫ t, m t * v t ω ∂timeLaw))
  have h := (le_abs_self _).trans h
  exact (sub_le_self _ (div_nonneg ENNReal.toReal_nonneg (by norm_num))).trans h

theorem controlPayoffs_nonempty (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ) (m : Trial) :
    {a | ∃ v : Time → BrownianPath → ℝ,
      Progressive P v ∧ controlCost P m v < ∞ ∧ a = controlPayoff P f m v}.Nonempty := by
  exact ⟨_, fun _ _ => 0, progressive_zero P, by simp, rfl⟩

theorem controlPayoffs_bddAbove (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) :
    BddAbove {a | ∃ v : Time → BrownianPath → ℝ,
      Progressive P v ∧ controlCost P m v < ∞ ∧ a = controlPayoff P f m v} := by
  refine ⟨‖f‖, ?_⟩
  rintro a ⟨v, _, _, rfl⟩
  exact controlPayoff_le_norm P f m v

theorem controlValue_le_norm (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) : controlValue P f m ≤ ‖f‖ := by
  apply csSup_le (controlPayoffs_nonempty P f m)
  rintro a ⟨v, _, _, rfl⟩
  exact controlPayoff_le_norm P f m v

theorem zero_payoff_le_controlValue (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) :
    (∫ ω, f (brownianEval 1 ω) ∂P) ≤ controlValue P f m := by
  apply le_csSup (controlPayoffs_bddAbove P f m)
  exact ⟨fun _ _ => 0, progressive_zero P, by simp, by simp⟩

theorem neg_norm_le_controlValue (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) : -‖f‖ ≤ controlValue P f m := by
  exact (abs_le.mp (abs_integral_reward_le P f (brownianEval 1))).1.trans
    (zero_payoff_le_controlValue P f m)

theorem abs_controlValue_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) : |controlValue P f m| ≤ ‖f‖ := by
  exact abs_le.mpr ⟨neg_norm_le_controlValue P f m, controlValue_le_norm P f m⟩

def oneTrial : Trial where
  toFun := fun _ => 1
  monotone := monotone_const
  measurable := measurable_const
  nonneg := fun _ => zero_le_one
  le_one := fun _ => le_rfl

@[simp] theorem oneTrial_apply (t : Time) : oneTrial t = 1 := rfl

@[simp] theorem tailIntegral_oneTrial (t : Time) :
    tailIntegral oneTrial t = 1 - (t : ℝ) := by
  simp [tailIntegral, Measure.real, ENNReal.toReal_ofReal, sub_nonneg.mpr t.2.2]

@[simp] theorem entropy_oneTrial : entropy oneTrial = 0 := by
  simp [entropy]

instance (N : ℕ) : IsProbabilityMeasure (unitSphereLaw (N + 1)) := by
  have : NeZero ((volume : Measure (Spin (N + 1))).toSphere) :=
    ⟨Measure.toSphere_ne_zero volume⟩
  unfold unitSphereLaw
  infer_instance

instance (N : ℕ) : IsProbabilityMeasure (sphereLaw (N + 1)) := by
  unfold sphereLaw
  infer_instance

lemma continuous_patternField {α : ℝ} {N : ℕ} (a : Fin (patternCount α N)) :
    Continuous (fun p : Patterns α N × Spin N => patternField p.1 a p.2) := by
  unfold patternField
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp ((continuous_apply a).comp
    (continuous_fst : Continuous (fun p : Patterns α N × Spin N => p.1)))).mul
    ((EuclideanSpace.proj i).continuous.comp
      (continuous_snd : Continuous (fun p : Patterns α N × Spin N => p.2)))

lemma continuous_hamiltonian (α : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    Continuous (fun p : Patterns α N × Spin N => hamiltonian α φ N p.1 p.2) := by
  unfold hamiltonian
  apply continuous_finsetSum
  intro a _
  exact φ.continuous.comp (continuous_patternField a)

lemma abs_hamiltonian_le (α : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α N) (x : Spin N) :
    |hamiltonian α φ N g x| ≤ (patternCount α N : ℝ) * ‖φ‖ := by
  unfold hamiltonian
  calc
    |∑ a, φ (patternField g a x)| ≤ ∑ a, |φ (patternField g a x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin (patternCount α N), ‖φ‖ :=
      Finset.sum_le_sum fun a _ => φ.norm_coe_le_norm _
    _ = _ := by simp

lemma log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F G : Ω → ℝ} {c : ℝ}
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (pF : 0 < ∫ x, Real.exp (F x) ∂μ) (pG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (h : ∀ x, F x ≤ G x + c) :
    Real.log (∫ x, Real.exp (F x) ∂μ) - Real.log (∫ x, Real.exp (G x) ∂μ) ≤ c := by
  have hi : (∫ x, Real.exp (F x) ∂μ) ≤
      Real.exp c * ∫ x, Real.exp (G x) ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono hF (hG.const_mul _)
    intro x
    calc
      Real.exp (F x) ≤ Real.exp (G x + c) := Real.exp_le_exp.mpr (h x)
      _ = Real.exp c * Real.exp (G x) := by rw [Real.exp_add, mul_comm]
  have hl := Real.log_le_log pF hi
  rw [Real.log_mul (Real.exp_ne_zero _) (ne_of_gt pG), Real.log_exp] at hl
  linarith

lemma abs_log_integral_exp_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F G : Ω → ℝ} {c : ℝ}
    (hF : Integrable (fun x => Real.exp (F x)) μ)
    (hG : Integrable (fun x => Real.exp (G x)) μ)
    (pF : 0 < ∫ x, Real.exp (F x) ∂μ) (pG : 0 < ∫ x, Real.exp (G x) ∂μ)
    (h : ∀ x, |F x - G x| ≤ c) :
    |Real.log (∫ x, Real.exp (F x) ∂μ) - Real.log (∫ x, Real.exp (G x) ∂μ)| ≤ c := by
  apply abs_le.mpr
  constructor
  · have hh := log_integral_exp_sub_le μ hG hF pG pF (fun x => by
      have := (abs_le.mp (h x)).1
      linarith)
    linarith
  · exact log_integral_exp_sub_le μ hF hG pF pG (fun x => by
      have := (abs_le.mp (h x)).2
      linarith)

lemma abs_energy_le (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α N) (x : Spin N) :
    |β * hamiltonian α φ N g x| ≤ |β| * (patternCount α N : ℝ) * ‖φ‖ := by
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_hamiltonian_le α φ N g x) (abs_nonneg β)

lemma integrable_partition (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α (N + 1)) :
    Integrable (fun x => Real.exp (β * hamiltonian α φ (N + 1) g x))
      (sphereLaw (N + 1)) := by
  apply (integrable_const (Real.exp (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖))).mono'
  · exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_hamiltonian α φ (N + 1)).comp
        (continuous_const.prodMk continuous_id)))).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_exp.mpr ((abs_le.mp (abs_energy_le α β φ (N + 1) g x)).2)

lemma partition_bounds (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α (N + 1)) :
    Real.exp (- (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖)) ≤
      (∫ x, Real.exp (β * hamiltonian α φ (N + 1) g x) ∂sphereLaw (N + 1)) ∧
    (∫ x, Real.exp (β * hamiltonian α φ (N + 1) g x) ∂sphereLaw (N + 1)) ≤
      Real.exp (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖) := by
  constructor
  · calc
      _ = ∫ _ : Spin (N + 1), Real.exp (- (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖))
          ∂sphereLaw (N + 1) := by simp
      _ ≤ _ := integral_mono (integrable_const _) (integrable_partition α β φ N g)
        (fun x => Real.exp_le_exp.mpr ((abs_le.mp (abs_energy_le α β φ (N + 1) g x)).1))
  · calc
      _ ≤ ∫ _ : Spin (N + 1), Real.exp (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖)
          ∂sphereLaw (N + 1) := integral_mono (integrable_partition α β φ N g)
        (integrable_const _)
        (fun x => Real.exp_le_exp.mpr ((abs_le.mp (abs_energy_le α β φ (N + 1) g x)).2))
      _ = _ := by simp

lemma partition_pos (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α (N + 1)) :
    0 < ∫ x, Real.exp (β * hamiltonian α φ (N + 1) g x) ∂sphereLaw (N + 1) :=
  (Real.exp_pos _).trans_le (partition_bounds α β φ N g).1

lemma continuous_partition (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    Continuous (fun g : Patterns α (N + 1) =>
      ∫ x, Real.exp (β * hamiltonian α φ (N + 1) g x) ∂sphereLaw (N + 1)) := by
  apply continuous_of_dominated (bound := fun _ =>
    Real.exp (|β| * (patternCount α (N + 1) : ℝ) * ‖φ‖))
  · intro g
    exact (integrable_partition α β φ N g).aestronglyMeasurable
  · intro g
    apply Filter.Eventually.of_forall
    intro x
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_exp.mpr ((abs_le.mp (abs_energy_le α β φ (N + 1) g x)).2)
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro x
    exact Real.continuous_exp.comp (continuous_const.mul
      ((continuous_hamiltonian α φ (N + 1)).comp
        (continuous_id.prodMk continuous_const)))

lemma continuous_pressure (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    Continuous (pressure α β φ (N + 1)) := by
  unfold pressure
  apply Continuous.div_const
  exact (continuous_partition α β φ N).log (fun g => ne_of_gt (partition_pos α β φ N g))

lemma abs_pressure_le (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α (N + 1)) :
    |pressure α β φ (N + 1) g| ≤
      |β| * (patternCount α (N + 1) : ℝ) * ‖φ‖ / (N + 1 : ℝ) := by
  have hp := partition_pos α β φ N g
  have hb := partition_bounds α β φ N g
  have hlo := Real.log_le_log (Real.exp_pos _) hb.1
  have hhi := Real.log_le_log hp hb.2
  rw [Real.log_exp] at hlo hhi
  have hd : 0 ≤ (N + 1 : ℝ) := by positivity
  unfold pressure
  rw [abs_div, abs_of_nonneg (show 0 ≤ ((N + 1 : ℕ) : ℝ) by positivity)]
  simpa only [Nat.cast_add, Nat.cast_one] using div_le_div_of_nonneg_right
    (abs_le.mpr ⟨hlo, hhi⟩) hd

lemma integrable_pressure (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    Integrable (pressure α β φ (N + 1)) (patternLaw α (N + 1)) := by
  have : IsProbabilityMeasure (patternLaw α (N + 1)) := by
    unfold patternLaw
    infer_instance
  exact (integrable_const _).mono' (continuous_pressure α β φ N).aestronglyMeasurable
    (Filter.Eventually.of_forall (abs_pressure_le α β φ N))
section ProductVariance
variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology Y] in
lemma continuous_integral_of_bounded {F : X × Y → ℝ} (hF : Continuous F)
    {K : ℝ} (hK : ∀ p, |F p| ≤ K) :
    Continuous (fun x => ∫ y, F (x, y) ∂ν) := by
  apply continuous_of_dominated (bound := fun _ => K)
  · intro x
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall (fun y => hK (x, y))
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun y =>
      hF.comp (continuous_id.prodMk continuous_const)

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [BorelSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y] in
lemma abs_integral_of_bounded {F : X × Y → ℝ} {K : ℝ} (hK : ∀ p, |F p| ≤ K)
    (x : X) : |∫ y, F (x, y) ∂ν| ≤ K := by
  simpa using norm_integral_le_of_norm_le_const
    (μ := ν) (f := fun y => F (x, y))
    (Filter.Eventually.of_forall fun y => hK (x, y))

lemma variance_prod_le {F : X × Y → ℝ} (hF : Continuous F)
    {K A B : ℝ} (hK : ∀ p, |F p| ≤ K)
    (hA : ∀ x, variance (fun y => F (x, y)) ν ≤ A)
    (hB : variance (fun x => ∫ y, F (x, y) ∂ν) μ ≤ B) :
    variance F (μ.prod ν) ≤ A + B := by
  have hp : MemLp F 2 (μ.prod ν) :=
    MemLp.of_bound hF.aestronglyMeasurable K (Filter.Eventually.of_forall hK)
  have hs (x : X) : MemLp (fun y => F (x, y)) 2 ν :=
    MemLp.of_bound (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      K (Filter.Eventually.of_forall fun y => hK (x, y))
  have hh : MemLp (fun x => ∫ y, F (x, y) ∂ν) 2 μ :=
    MemLp.of_bound (continuous_integral_of_bounded ν hF hK).aestronglyMeasurable K
      (Filter.Eventually.of_forall (abs_integral_of_bounded ν hK))
  have hi : (∫ x, ∫ y, F (x, y) ^ 2 ∂ν ∂μ) ≤
      A + ∫ x, (∫ y, F (x, y) ∂ν) ^ 2 ∂μ := by
    calc
      _ ≤ ∫ x, (A + (∫ y, F (x, y) ∂ν) ^ 2) ∂μ := by
        apply integral_mono hp.integrable_sq.integral_prod_left
          ((integrable_const A).add hh.integrable_sq)
        intro x
        have hv := hA x
        rw [variance_eq_sub (hs x)] at hv
        simpa only [Pi.pow_apply, Pi.add_apply] using (sub_le_iff_le_add.mp hv)
      _ = _ := by rw [integral_add (integrable_const _) hh.integrable_sq]; simp
  rw [variance_eq_sub hh] at hB
  rw [variance_eq_sub hp]
  simp only [Pi.pow_apply] at hB ⊢
  rw [integral_prod _ hp.integrable_sq,
    integral_prod _ (hp.integrable (by norm_num))]
  simpa only [Pi.pow_apply] using sub_le_iff_le_add.mpr (by linarith :
    (∫ x, ∫ y, F (x, y) ^ 2 ∂ν ∂μ) ≤
      A + B + (∫ x, ∫ y, F (x, y) ∂ν ∂μ) ^ 2)

end ProductVariance

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [Nonempty X]
  (μ : Measure X) [IsProbabilityMeasure μ]

omit [SecondCountableTopology X] in
lemma variance_le_of_oscillation {F : X → ℝ} (hF : Continuous F) {c : ℝ}
    (hosc : ∀ x y, |F x - F y| ≤ c) : variance F μ ≤ c ^ 2 := by
  let x₀ : X := Classical.choice ‹Nonempty X›
  have hbound : ∀ᵐ x ∂μ, F x ∈ Icc (F x₀ - c) (F x₀ + c) := by
    apply Filter.Eventually.of_forall
    intro x
    have hh := abs_le.mp (hosc x x₀)
    constructor <;> linarith
  have hv := variance_le_sq_of_bounded hbound hF.measurable.aemeasurable
  convert hv using 1
  ring

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [Nonempty X] in
lemma continuous_fin_cons {n : ℕ} :
    Continuous (fun p : X × (Fin n → X) => Fin.cons (α := fun _ => X) p.1 p.2) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (continuous_fst : Continuous (fun p : X × (Fin n → X) => p.1))
  · simpa only [Fin.cons_succ, Function.comp_def] using (continuous_apply j).comp
      (continuous_snd : Continuous (fun p : X × (Fin n → X) => p.2))

omit [BorelSpace X] [Nonempty X] in
lemma measurePreserving_fin_cons (n : ℕ) :
    MeasurePreserving (fun p : X × (Fin n → X) => Fin.cons (α := fun _ => X) p.1 p.2)
      (μ.prod (Measure.pi fun _ : Fin n => μ)) (Measure.pi fun _ : Fin (n+1) => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero,
    Fin.consEquiv] using h

omit [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X] [Nonempty X] in
lemma measurableEmbedding_fin_cons (n : ℕ) :
    MeasurableEmbedding (fun p : X × (Fin n → X) => Fin.cons (α := fun _ => X) p.1 p.2) := by
  have h := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) 0).symm.measurableEmbedding
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero,
    Fin.consEquiv] using h

theorem variance_pi_le_of_bounded_differences (n : ℕ) {F : (Fin n → X) → ℝ}
    (hF : Continuous F) {K c : ℝ} (hK : ∀ x, |F x| ≤ K)
    (hdiff : ∀ x i y, |F (Function.update x i y) - F x| ≤ c) :
    variance F (Measure.pi fun _ : Fin n => μ) ≤ (n : ℝ) * c ^ 2 := by
  classical
  induction n with
  | zero =>
      rw [Measure.pi_of_empty]
      simp
  | succ n ih =>
      let ν := Measure.pi fun _ : Fin n => μ
      let G : X × (Fin n → X) → ℝ := fun p => F (Fin.cons (α := fun _ => X) p.1 p.2)
      have hG : Continuous G := hF.comp continuous_fin_cons
      have hGK (p) : |G p| ≤ K := hK _
      have hA (x : X) : variance (fun y => G (x, y)) ν ≤ (n : ℝ) * c ^ 2 := by
        apply ih (hG.comp (continuous_const.prodMk continuous_id)) (fun y => hGK (x,y))
        intro y i z
        simpa only [G, Function.comp_apply, id_eq, Fin.cons_update] using hdiff (Fin.cons x y) i.succ z
      have hHc : Continuous (fun x => ∫ y, G (x, y) ∂ν) :=
        continuous_integral_of_bounded ν hG hGK
      have hHosc (x x' : X) :
          |(∫ y, G (x, y) ∂ν) - ∫ y, G (x', y) ∂ν| ≤ c := by
        have hi (x : X) : Integrable (fun y => G (x, y)) ν :=
          (integrable_const K).mono'
            (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
            (Filter.Eventually.of_forall fun y => hGK (x, y))
        rw [← integral_sub (hi x) (hi x')]
        have hh : ∀ y, |G (x, y) - G (x', y)| ≤ c := by
          intro y
          have hu : Function.update (Fin.cons x' y) 0 x = Fin.cons (α := fun _ => X) x y := by
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          simpa only [G, hu] using hdiff (Fin.cons x' y) 0 x
        simpa using norm_integral_le_of_norm_le_const
          (μ := ν) (f := fun y => G (x,y) - G (x',y))
          (Filter.Eventually.of_forall hh)
      have hv := variance_prod_le μ ν hG hGK hA
        (variance_le_of_oscillation μ hHc hHosc)
      have hpF : MemLp F 2 (Measure.pi fun _ : Fin (n+1) => μ) :=
        MemLp.of_bound hF.aestronglyMeasurable K (Filter.Eventually.of_forall hK)
      have hpG : MemLp G 2 (μ.prod ν) :=
        MemLp.of_bound hG.aestronglyMeasurable K (Filter.Eventually.of_forall hGK)
      rw [variance_eq_sub hpG] at hv
      rw [variance_eq_sub hpF]
      have hmean := (measurePreserving_fin_cons μ n).integral_comp
        (measurableEmbedding_fin_cons (X := X) n) F
      have hsquare := (measurePreserving_fin_cons μ n).integral_comp
        (measurableEmbedding_fin_cons (X := X) n) (fun x => F x ^ 2)
      change (∫ x, G x ∂μ.prod ν) = _ at hmean
      change (∫ x, G x ^ 2 ∂μ.prod ν) = _ at hsquare
      simp only [Pi.pow_apply] at hv ⊢
      rw [hsquare, hmean] at hv
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using hv

end SphericalPerceptronFreeEnergy
end

end OAI
