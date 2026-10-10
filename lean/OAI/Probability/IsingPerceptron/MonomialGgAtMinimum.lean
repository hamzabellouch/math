import Mathlib
import OAI.Probability.IsingPerceptron.ReplicaEnergyCovarianceBound

namespace OAI

/-! Monomial Gg At Minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

theorem monomial_gg_at_minimum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {N n : ℕ} (hN : 0 < N)
    {ν : Ω → Measure (Spin N × LabeledLeaf n)}
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)] (p d : ℕ)
    {v c a s δ K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hmin : ∀ t ∈ Icc (v-s) (v+s),
      -(∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (monomialCoefficients n p d x) z.2) (ν z.1) v
        ∂P.prod gaussianCoordinates)+c*(v-a)^2 ≤
      -(∫ z : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (monomialCoefficients n p d x) z.2) (ν z.1) t
        ∂P.prod gaussianCoordinates)+c*(t-a)^2)
    (hconc : ∀ t ∈ ({v-s,v,v+s} : Set ℝ),
      (∫ z : Ω × (ℕ → ℝ), |cgf (fun x => cylinderField (monomialCoefficients n p d x) z.2) (ν z.1) t -
        (∫ z' : Ω × (ℕ → ℝ), cgf (fun x => cylinderField (monomialCoefficients n p d x) z'.2) (ν z'.1) t
          ∂P.prod gaussianCoordinates)| ∂P.prod gaussianCoordinates) ≤ δ)
    {r : ℕ} (D : (Fin (r+1) → Spin N × LabeledLeaf n) → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hD : ∀ σ, |D σ| ≤ C) :
    let A := monomialCoefficients (N := N) n p d
    let κ := fun x y : Spin N × LabeledLeaf n => spinOverlap x.1 y.1 ^ p * treeOverlap n x.2 y.2 ^ d
    |v| * |(r+1 : ℕ)*randomReplicaAverage P ν A v
        (fun τ : Fin (r+1+1) → Spin N × LabeledLeaf n => D (Fin.tail τ)*κ ((Fin.tail τ) 0) (τ 0)) -
      randomReplicaAverage P ν A v D * randomReplicaAverage P ν A v
        (fun τ : Fin 2 → Spin N × LabeledLeaf n => κ (τ 1) (τ 0)) -
      randomReplicaAverage P ν A v
        (fun σ => D σ*(∑ l : Fin r, κ (σ 0) (σ l.succ)))| ≤
      2*C*((2*c+K^2)/(2*K)+c*s+4*δ/s) := by
  dsimp only
  obtain ⟨hE,hEb⟩ := random_gaussian_energy_at_minimum hν
    (monomialCoefficients n p d) (monomialCoefficients_variance_le hN n p d) hs hK hmin hconc
  have hg := countable_gaussian_gg_bound hν (monomialCoefficients n p d)
    (monomialCoefficients_variance_le hN n p d)
    (fun x => by rw [cylinderCross_self,monomialCoefficients_variance hN])
    v (2*c*(v-a)) D hC hD hE
  simp only [monomialCoefficients_cross] at hg
  exact hg.trans (mul_le_mul_of_nonneg_left hEb (by positivity))

variable {A : Type*} [MeasurableSpace A]

def logMean (b : ℝ) (μ : Measure A) (F : A → ℝ) : ℝ :=
  Real.log (∫ a, Real.exp (b*F a) ∂μ) / b

lemma integral_exp_pos (μ : Measure A) [IsProbabilityMeasure μ] (F : A → ℝ)
    {b : ℝ} (hi : Integrable (fun a => Real.exp (b*F a)) μ) :
    0 < ∫ a, Real.exp (b*F a) ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun a => (Real.exp_pos _).le) hi).mpr
  simpa only [Function.support, ne_eq, Real.exp_ne_zero, not_false_eq_true, ofPred_true,
    measure_univ] using (zero_lt_one : (0 : ℝ≥0∞) < 1)

theorem logMean_normalized_moment (μ : Measure A) [IsProbabilityMeasure μ]
    (F : A → ℝ) {b : ℝ} (hb : b ≠ 0)
    (hi : Integrable (fun a => Real.exp (b*F a)) μ) :
    (∫⁻ a, ENNReal.ofReal ((Real.exp (F a-logMean b μ F))^b) ∂μ) = 1 := by
  let M := ∫ a, Real.exp (b*F a) ∂μ
  have hM : 0 < M := integral_exp_pos μ F hi
  have he a : (Real.exp (F a-logMean b μ F))^b = M⁻¹ * Real.exp (b*F a) := by
    rw [← Real.exp_mul]
    have he' : (F a-logMean b μ F)*b = -Real.log M+b*F a := by
      dsimp only [logMean, M]
      field_simp
      ring
    rw [he', Real.exp_add, Real.exp_neg, Real.exp_log hM]
  simp_rw [he, ENNReal.ofReal_mul (inv_nonneg.mpr hM.le)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun a => (Real.exp_pos _).le)]
  change ENNReal.ofReal M⁻¹ * ENNReal.ofReal M = 1
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hM.le), inv_mul_cancel₀ hM.ne', ENNReal.ofReal_one]

lemma logMean_bounds (μ : Measure A) [IsProbabilityMeasure μ]
    {F : A → ℝ} (hF : Measurable F) {b K : ℝ} (hb : 0 < b)
    (hbound : ∀ a, |F a| ≤ K) : |logMean b μ F| ≤ K := by
  have hi : Integrable (fun a => Real.exp (b*F a)) μ := by
    apply Integrable.of_bound ((measurable_const.mul hF).exp).aestronglyMeasurable (Real.exp (b*K))
    apply ae_of_all
    intro a
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hbound a)) hb.le)
  have hlow : Real.exp (-b*K) ≤ ∫ a, Real.exp (b*F a) ∂μ := by
    calc
      _ = ∫ _, Real.exp (-b*K) ∂μ := by simp
      _ ≤ _ := by
        apply integral_mono (integrable_const _) hi
        intro a
        apply Real.exp_le_exp.mpr
        have := (abs_le.mp (hbound a)).1
        nlinarith
  have hhigh : (∫ a, Real.exp (b*F a) ∂μ) ≤ Real.exp (b*K) := by
    calc
      _ ≤ ∫ _, Real.exp (b*K) ∂μ := integral_mono hi (integrable_const _) (fun a =>
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hbound a)) hb.le))
      _ = _ := by simp
  have hM := integral_exp_pos μ F hi
  rw [abs_le, logMean]
  constructor
  · apply (le_div_iff₀ hb).mpr
    have := Real.log_le_log (Real.exp_pos _) hlow
    rw [Real.log_exp] at this
    nlinarith
  · apply (div_le_iff₀ hb).mpr
    have := Real.log_le_log hM hhigh
    rw [Real.log_exp] at this
    nlinarith

end IsingPerceptron

namespace IsingPerceptron
variable {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]

def cascadeRecursion : ℕ → (ℕ → ℝ) → (ℕ → ProbabilityMeasure A) →
    (ℕ → S × A → S) → (S → ℝ) → S → ℝ
  | 0, _, _, _, F => F
  | n+1, b, μ, u, F => fun s => logMean (b 0) (μ 0 : Measure A)
      (fun a => cascadeRecursion n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => u (j+1)) F (u 0 (s,a)))

lemma measurable_cascadeRecursion (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {u : ℕ → S × A → S} {F : S → ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) :
    Measurable (cascadeRecursion n b μ u F) := by
  induction n generalizing b μ u with
  | zero => exact hF
  | succ n ih =>
    have hm : Measurable (fun p : S × A => Real.exp (b 0 *
        cascadeRecursion n (fun j => b (j+1)) (fun j => μ (j+1))
          (fun j => u (j+1)) F (u 0 p))) :=
      (measurable_const.mul ((ih _ _ (fun j => hu (j+1))).comp (hu 0))).exp
    exact hm.stronglyMeasurable.integral_prod_right.measurable.log.div_const _

lemma cascadeRecursion_bound (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {u : ℕ → S × A → S} {F : S → ℝ} {K : ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F)
    (hb : ∀ i < n, 0 < b i) (hbound : ∀ s, |F s| ≤ K) :
    ∀ s, |cascadeRecursion n b μ u F s| ≤ K := by
  induction n generalizing b μ u with
  | zero => exact hbound
  | succ n ih =>
    intro s
    apply logMean_bounds (μ 0 : Measure A)
      ((measurable_cascadeRecursion n _ _ (fun j => hu (j+1)) hF).comp
        ((hu 0).comp (measurable_const.prodMk measurable_id))) (hb 0 (by omega))
    intro a
    exact ih _ _ (fun j => hu (j+1)) (fun i hi => hb (i+1) (by omega)) (u 0 (s,a))

def stoppedUpdate (n : ℕ) (u : ℕ → S × A → S) (i : ℕ) (p : S × A) : S :=
  if i < n then u i p else p.1

lemma measurable_stoppedUpdate (n : ℕ) {u : ℕ → S × A → S}
    (hu : ∀ i, Measurable (u i)) (i : ℕ) : Measurable (stoppedUpdate n u i) := by
  unfold stoppedUpdate
  split_ifs
  · exact hu i
  · exact measurable_fst

def backwardValue (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (u : ℕ → S × A → S) (F : S → ℝ) (i : ℕ) : S → ℝ :=
  cascadeRecursion (n-i) (fun j => b (i+j)) (fun j => μ (i+j))
    (fun j => u (i+j)) F

lemma measurable_backwardValue (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {u : ℕ → S × A → S} {F : S → ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) (i : ℕ) :
    Measurable (backwardValue n b μ u F i) :=
  measurable_cascadeRecursion _ _ _ (fun j => hu (i+j)) hF

omit [MeasurableSpace S] in
lemma backwardValue_step (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (u : ℕ → S × A → S) (F : S → ℝ) {i : ℕ} (hi : i < n) (s : S) :
    backwardValue n b μ u F i s = logMean (b i) (μ i : Measure A)
      (fun a => backwardValue n b μ u F (i+1) (u i (s,a))) := by
  unfold backwardValue
  rw [show n-i = (n-(i+1))+1 by omega, cascadeRecursion]
  simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]

omit [MeasurableSpace S] in
lemma backwardValue_terminal (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (u : ℕ → S × A → S) (F : S → ℝ) {i : ℕ} (hi : n ≤ i) :
    backwardValue n b μ u F i = F := by
  simp [backwardValue, Nat.sub_eq_zero_of_le hi, cascadeRecursion]

theorem backwardValue_multiplier_moment (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    {u : ℕ → S × A → S} {F : S → ℝ} {K : ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F)
    (hb : ∀ i < n, 0 < b i) (hbound : ∀ s, |F s| ≤ K) (i : ℕ) (s : S) :
    (∫⁻ a, ENNReal.ofReal ((Real.exp
      (backwardValue n b μ u F (i+1) (stoppedUpdate n u i (s,a)) -
        backwardValue n b μ u F i s)) ^ b i) ∂(μ i : Measure A)) = 1 := by
  by_cases hi : i < n
  · simp only [stoppedUpdate, ite_eq_left hi, backwardValue_step n b μ u F hi]
    apply logMean_normalized_moment _ _ (hb i hi).ne'
    apply Integrable.of_bound
      ((measurable_const.mul ((measurable_backwardValue n b μ hu hF (i+1)).comp
        ((hu i).comp (measurable_const.prodMk measurable_id)))).exp).aestronglyMeasurable
      (Real.exp (b i*K))
    apply ae_of_all
    intro a
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (hb i hi).le
    apply le_trans (le_abs_self _)
    exact cascadeRecursion_bound _ _ _ (fun j => hu (i+1+j)) hF
      (fun j hj => hb (i+1+j) (by omega)) hbound _
  · have hni : n ≤ i := by omega
    simp only [stoppedUpdate, ite_eq_right hi,
      backwardValue_terminal n b μ u F hni,
      backwardValue_terminal n b μ u F (show n ≤ i+1 by omega), sub_self,
      Real.exp_zero, Real.one_rpow, ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]

end IsingPerceptron

namespace IsingPerceptron
variable {A S : Type} [MeasurableSpace A] [MeasurableSpace S] [Nonempty A]

def terminalTreeFactor : (n : ℕ) → (ℕ → ℝ) → (ℕ → ProbabilityMeasure A) →
    (ℕ → S × A → S) → (S → ℝ) → S → NoiseTree A n → ℝ≥0∞
  | 0, _, _, _, F, s, _ => ENNReal.ofReal (Real.exp (F s))
  | n+1, b, μ, u, F, s, ν => ∫⁻ p, ENNReal.ofReal (max p.1 0) *
      terminalTreeFactor n (fun j => b (j+1)) (fun j => μ (j+1))
        (fun j => u (j+1)) F (u 0 (s,p.2.1)) p.2.2
        ∂sigmaPart ((powerIntensity (b 0)).prod ((μ 0 : Measure A).prod
          (noiseCascadeLaw A n (fun j => b (j+1)) (fun j => μ (j+1)) : Measure (NoiseTree A n)))) ν

omit [MeasurableSpace S] in
lemma noiseTreeFactor_terminal (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (X : ℕ → S → ℝ) (u : ℕ → S × A → S) (s : S) (ν : NoiseTree A n) :
    noiseTreeFactor n b μ X u s ν = terminalTreeFactor n b μ u (X n) s ν := by
  induction n generalizing b μ X u s with
  | zero => rfl
  | succ n ih =>
    unfold noiseTreeFactor terminalTreeFactor
    apply lintegral_congr
    intro p
    congr 1
    exact ih _ _ _ _ _ _

omit [MeasurableSpace S] in
lemma terminalTreeFactor_update_congr (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (F : S → ℝ) {u v : ℕ → S × A → S} (huv : ∀ i < n, u i = v i)
    (s : S) (ν : NoiseTree A n) :
    terminalTreeFactor n b μ u F s ν = terminalTreeFactor n b μ v F s ν := by
  induction n generalizing b μ u v s with
  | zero => rfl
  | succ n ih =>
    unfold terminalTreeFactor
    rw [huv 0 (by omega)]
    apply lintegral_congr
    intro p
    congr 1
    exact ih _ _ (fun i hi => huv (i+1) (by omega)) _ _

omit [MeasurableSpace S] in
lemma backwardValue_treeFactor (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A)
    (F : S → ℝ) (u : ℕ → S × A → S) (s : S) (ν : NoiseTree A n) :
    noiseTreeFactor n b μ (backwardValue n b μ u F) (stoppedUpdate n u) s ν =
      terminalTreeFactor n b μ u F s ν := by
  rw [noiseTreeFactor_terminal, backwardValue_terminal n b μ u F (le_refl n)]
  apply terminalTreeFactor_update_congr
  intro i hi
  funext p
  exact ite_eq_left hi

theorem bounded_noiseCascade_recursion (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {u : ℕ → S × A → S} {F : S → ℝ} {K : ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) (hbound : ∀ s, |F s| ≤ K) (s : S) :
    let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    let L := fun ν => Real.log
      ((terminalTreeFactor n b μ u F s ν).toReal / (noiseTreeTotal A n ν).toReal)
    (∀ᵐ ν ∂P, 0 < terminalTreeFactor n b μ u F s ν ∧ terminalTreeFactor n b μ u F s ν < ∞) ∧
    Integrable L P ∧ (∫ ν, L ν ∂P) = cascadeRecursion n b μ u F s ∧
    Integrable (fun ν => (L ν-cascadeRecursion n b μ u F s)^2) P ∧
    (∫ ν, (L ν-cascadeRecursion n b μ u F s)^2 ∂P) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  let X := backwardValue n b μ u F
  let v := stoppedUpdate n u
  let c : ℕ → S × A → ℝ := fun i p => Real.exp (X (i+1) (v i p)-X i p.1)
  have hX : ∀ i, Measurable (X i) := measurable_backwardValue n b μ hu hF
  have hv : ∀ i, Measurable (v i) := measurable_stoppedUpdate n hu
  have hc : ∀ i, Measurable (c i) := fun i =>
    (((hX (i+1)).comp (hv i)).sub ((hX i).comp measurable_fst)).exp
  have hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a)^b i) ∂(μ i : Measure A)) = 1 :=
    backwardValue_multiplier_moment n b μ hu hF (fun i hi => (hb.1 i hi).1) hbound
  have h := noiseCascade_log_integral n b hb μ hc hv (X := X) (fun _ _ _ => rfl) hm s
  have hX0 : X 0 s = cascadeRecursion n b μ u F s := by simp [X, backwardValue]
  simpa only [X, v, backwardValue_treeFactor, hX0] using h

omit [MeasurableSpace S] [Nonempty A] in
lemma backwardValue_multiplier_moment_admissible (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure A) (u : ℕ → S × A → S) (F : S → ℝ)
    (hb : ∀ i < n, 0 < b i)
    (hadm : ∀ i < n, ∀ s, Integrable (fun a => Real.exp
      (b i * backwardValue n b μ u F (i+1) (u i (s,a)))) (μ i : Measure A))
    (i : ℕ) (s : S) :
    (∫⁻ a, ENNReal.ofReal ((Real.exp
      (backwardValue n b μ u F (i+1) (stoppedUpdate n u i (s,a)) -
        backwardValue n b μ u F i s)) ^ b i) ∂(μ i : Measure A)) = 1 := by
  by_cases hi : i < n
  · simp only [stoppedUpdate, ite_eq_left hi, backwardValue_step n b μ u F hi]
    exact logMean_normalized_moment _ _ (hb i hi).ne' (hadm i hi s)
  · have hni : n ≤ i := by omega
    simp only [stoppedUpdate, ite_eq_right hi,
      backwardValue_terminal n b μ u F hni,
      backwardValue_terminal n b μ u F (show n ≤ i+1 by omega), sub_self,
      Real.exp_zero, Real.one_rpow, ENNReal.ofReal_one, lintegral_const, measure_univ, mul_one]

theorem admissible_noiseCascade_recursion (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure A) {u : ℕ → S × A → S} {F : S → ℝ}
    (hu : ∀ i, Measurable (u i)) (hF : Measurable F) (hadm : ∀ i < n, ∀ s, Integrable (fun a => Real.exp
      (b i * backwardValue n b μ u F (i+1) (u i (s,a)))) (μ i : Measure A)) (s : S) :
    let P := (noiseCascadeLaw A n b μ : Measure (NoiseTree A n))
    let L := fun ν => Real.log
      ((terminalTreeFactor n b μ u F s ν).toReal / (noiseTreeTotal A n ν).toReal)
    (∀ᵐ ν ∂P, 0 < terminalTreeFactor n b μ u F s ν ∧ terminalTreeFactor n b μ u F s ν < ∞) ∧
    Integrable L P ∧ (∫ ν, L ν ∂P) = cascadeRecursion n b μ u F s ∧
    Integrable (fun ν => (L ν-cascadeRecursion n b μ u F s)^2) P ∧
    (∫ ν, (L ν-cascadeRecursion n b μ u F s)^2 ∂P) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  let X := backwardValue n b μ u F
  let v := stoppedUpdate n u
  let c : ℕ → S × A → ℝ := fun i p => Real.exp (X (i+1) (v i p)-X i p.1)
  have hX : ∀ i, Measurable (X i) := measurable_backwardValue n b μ hu hF
  have hv : ∀ i, Measurable (v i) := measurable_stoppedUpdate n hu
  have hc : ∀ i, Measurable (c i) := fun i =>
    (((hX (i+1)).comp (hv i)).sub ((hX i).comp measurable_fst)).exp
  have hm : ∀ i s, (∫⁻ a, ENNReal.ofReal (c i (s,a)^b i) ∂(μ i : Measure A)) = 1 :=
    backwardValue_multiplier_moment_admissible n b μ u F (fun i hi => (hb.1 i hi).1) hadm
  have h := noiseCascade_log_integral n b hb μ hc hv (X := X) (fun _ _ _ => rfl) hm s
  have hX0 : X 0 s = cascadeRecursion n b μ u F s := by simp [X, backwardValue]
  simpa only [X, v, backwardValue_treeFactor, hX0] using h

end IsingPerceptron

namespace IsingPerceptron
variable {A : Type*} [MeasurableSpace A]

lemma logMean_mono (μ : Measure A) [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b)
    {F G : A → ℝ} (hF : Integrable (fun a => Real.exp (b*F a)) μ)
    (hG : Integrable (fun a => Real.exp (b*G a)) μ) (hFG : ∀ a, F a ≤ G a) :
    logMean b μ F ≤ logMean b μ G := by
  apply div_le_div_of_nonneg_right _ hb.le
  apply Real.log_le_log (integral_exp_pos μ F hF)
  apply integral_mono hF hG
  intro a
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hFG a) hb.le)

lemma logMean_const_add (μ : Measure A) [IsProbabilityMeasure μ] {b : ℝ} (hb : b ≠ 0)
    {F : A → ℝ} (hF : Integrable (fun a => Real.exp (b*F a)) μ) (c : ℝ) :
    logMean b μ (fun a => c+F a) = c+logMean b μ F := by
  have he a : Real.exp (b*(c+F a)) = Real.exp (b*c)*Real.exp (b*F a) := by
    rw [mul_add, Real.exp_add]
  simp_rw [logMean, he, integral_const_mul]
  rw [Real.log_mul (Real.exp_ne_zero _) (integral_exp_pos μ F hF).ne', Real.log_exp]
  field_simp

end IsingPerceptron

namespace IsingPerceptron
variable {S : Type*} [SeminormedAddCommGroup S] [MeasurableSpace S] [MeasurableAdd₂ S]

def ExponentialNormMoments (μ : Measure S) : Prop :=
  ∀ a : ℝ, Integrable (fun s => Real.exp (a*‖s‖)) μ

def HasLinearGrowth (F : S → ℝ) : Prop :=
  ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ ∀ s, |F s| ≤ C+L*‖s‖

omit [MeasurableAdd₂ S] in
lemma integrable_exp_of_linearGrowth (μ : Measure S) (hμ : ExponentialNormMoments μ)
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F) (b : ℝ) :
    Integrable (fun s => Real.exp (b*F s)) μ := by
  obtain ⟨C,L,_,_,hbound⟩ := hG
  apply ((hμ (|b| *L)).const_mul (Real.exp (|b| *C))).mono'
    ((hF.const_mul b).exp).aestronglyMeasurable
  apply ae_of_all
  intro s
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    b*F s ≤ |b*F s| := le_abs_self _
    _ = |b| *|F s| := abs_mul _ _
    _ ≤ |b| *(C+L*‖s‖) := mul_le_mul_of_nonneg_left (hbound s) (abs_nonneg _)
    _ = |b| *C+(|b| *L)*‖s‖ := by ring

omit [MeasurableSpace S] [MeasurableAdd₂ S] in
lemma HasLinearGrowth.add_left {F : S → ℝ} (h : HasLinearGrowth F) (x : S) :
    HasLinearGrowth (fun a => F (x+a)) := by
  obtain ⟨C,L,hC,hL,h⟩ := h
  refine ⟨C+L*‖x‖, L, by positivity, hL, fun a => ?_⟩
  calc
    _ ≤ C+L*‖x+a‖ := h _
    _ ≤ C+L*(‖x‖+‖a‖) := add_le_add_right (mul_le_mul_of_nonneg_left (norm_add_le _ _) hL) C
    _ = C+L*‖x‖+L*‖a‖ := by ring

omit [MeasurableSpace S] [MeasurableAdd₂ S] in
lemma linearGrowth_norm_mul (L : ℝ) : HasLinearGrowth (fun s : S => L*‖s‖) := by
  refine ⟨0, |L|, le_rfl, abs_nonneg _, fun s => ?_⟩
  simp [abs_mul, abs_of_nonneg (norm_nonneg s)]

lemma logMean_hasLinearGrowth (μ : Measure S) [IsProbabilityMeasure μ]
    (hμ : ExponentialNormMoments μ) {F : S → ℝ} (hF : Measurable F)
    (hG : HasLinearGrowth F) {b : ℝ} (hb : 0 < b) :
    HasLinearGrowth (fun x => logMean b μ (fun a => F (x+a))) := by
  obtain ⟨C,L,hC,hL,hbound⟩ := hG
  have hG : HasLinearGrowth F := ⟨C,L,hC,hL,hbound⟩
  let U := logMean b μ (fun a : S => L*‖a‖)
  let D := logMean b μ (fun a : S => -L*‖a‖)
  have hiU : Integrable (fun a : S => Real.exp (b*(L*‖a‖))) μ := by
    simpa only [mul_assoc] using hμ (b*L)
  have hiD : Integrable (fun a : S => Real.exp (b*(-L*‖a‖))) μ := by
    simpa only [mul_assoc] using hμ (b*(-L))
  have hi (x : S) : Integrable (fun a => Real.exp (b*F (x+a))) μ :=
    integrable_exp_of_linearGrowth μ hμ (hF.comp (measurable_const.add measurable_id))
      (hG.add_left x) b
  refine ⟨C+|U|+|D|, L, by positivity, hL, fun x => ?_⟩
  have hup : logMean b μ (fun a => F (x+a)) ≤ (C+L*‖x‖)+U := by
    rw [← logMean_const_add μ hb.ne' hiU]
    apply logMean_mono μ hb (hi x)
    · convert hiU.const_mul (Real.exp (b*(C+L*‖x‖))) using 1
      ext a
      rw [mul_add, Real.exp_add]
    · intro a
      calc
        F (x+a) ≤ |F (x+a)| := le_abs_self _
        _ ≤ C+L*‖x+a‖ := hbound _
        _ ≤ C+L*(‖x‖+‖a‖) := by gcongr; exact norm_add_le _ _
        _ = (C+L*‖x‖)+L*‖a‖ := by ring
  have hlo : (-C-L*‖x‖)+D ≤ logMean b μ (fun a => F (x+a)) := by
    rw [← logMean_const_add μ hb.ne' hiD]
    refine logMean_mono μ hb ?_ (hi x) ?_
    · convert hiD.const_mul (Real.exp (b*(-C-L*‖x‖))) using 1
      ext a
      rw [mul_add, Real.exp_add]
    · intro a
      have hh := (abs_le.mp (hbound (x+a))).1
      have hn := mul_le_mul_of_nonneg_left (norm_add_le x a) hL
      linarith
  rw [abs_le]
  constructor
  · have := neg_abs_le D
    linarith [abs_nonneg U]
  · have := le_abs_self U
    linarith [abs_nonneg D]

lemma cascadeRecursion_linearGrowth (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure S)
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure S))
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hb : ∀ i < n, 0 < b i) :
    HasLinearGrowth (cascadeRecursion n b μ (fun _ p => p.1+p.2) F) := by
  induction n generalizing b μ with
  | zero => exact hG
  | succ n ih =>
    exact logMean_hasLinearGrowth _ (hμ 0 (by omega))
      (measurable_cascadeRecursion n (fun i => b (i+1)) (fun i => μ (i+1))
        (fun _ => measurable_fst.add measurable_snd) hF)
      (ih _ _ (fun i hi => hμ (i+1) (by omega)) (fun i hi => hb (i+1) (by omega)))
      (hb 0 (by omega))

lemma backwardValue_linearGrowth_moments (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure S)
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure S))
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hb : ∀ i < n, 0 < b i) :
    ∀ i < n, ∀ s, Integrable (fun a => Real.exp
      (b i * backwardValue n b μ (fun _ p => p.1+p.2) F (i+1) (s+a))) (μ i : Measure S) := by
  intro i hi s
  apply integrable_exp_of_linearGrowth _ (hμ i hi)
    ((measurable_backwardValue n b μ (fun _ => measurable_fst.add measurable_snd) hF (i+1)).comp
      (measurable_const.add measurable_id))
  apply HasLinearGrowth.add_left
  unfold backwardValue
  exact cascadeRecursion_linearGrowth _ _ _ (fun j hj => hμ (i+1+j) (by omega)) hF hG
    (fun j hj => hb (i+1+j) (by omega))

end IsingPerceptron

namespace IsingPerceptron
lemma gaussianReal_exponentialNormMoments (m : ℝ) (v : ℝ≥0) :
    ExponentialNormMoments (gaussianReal m v) := by
  intro a
  simpa only [Real.norm_eq_abs] using integrable_exp_mul_abs
    (integrable_exp_mul_gaussianReal (μ := m) (v := v) a)
    (integrable_exp_mul_gaussianReal (μ := m) (v := v) (-a))

variable {S : Type} [SeminormedAddCommGroup S] [MeasurableSpace S] [MeasurableAdd₂ S]

theorem linearGrowth_noiseCascade_recursion (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure S) (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure S))
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F) (s : S) :
    let u : ℕ → S × S → S := fun _ p => p.1+p.2
    let P := (noiseCascadeLaw S n b μ : Measure (NoiseTree S n))
    let L := fun ν => Real.log
      ((terminalTreeFactor n b μ u F s ν).toReal / (noiseTreeTotal S n ν).toReal)
    (∀ᵐ ν ∂P, 0 < terminalTreeFactor n b μ u F s ν ∧ terminalTreeFactor n b μ u F s ν < ∞) ∧
    Integrable L P ∧ (∫ ν, L ν ∂P) = cascadeRecursion n b μ u F s ∧
    Integrable (fun ν => (L ν-cascadeRecursion n b μ u F s)^2) P ∧
    (∫ ν, (L ν-cascadeRecursion n b μ u F s)^2 ∂P) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  exact admissible_noiseCascade_recursion n b hb μ (fun _ => measurable_fst.add measurable_snd) hF
    (backwardValue_linearGrowth_moments n b μ hμ hF hG (fun i hi => (hb.1 i hi).1)) s

end IsingPerceptron

namespace IsingPerceptron

lemma abs_log_cosh_le (x : ℝ) : |Real.log (Real.cosh x)| ≤ |x| := by
  have hp := Real.cosh_pos x
  rw [abs_of_nonneg (Real.log_nonneg (Real.one_le_cosh x))]
  calc
    _ ≤ Real.log (Real.exp |x|) := by
      apply Real.log_le_log hp
      rw [Real.cosh_eq]
      have h₁ := Real.exp_le_exp.mpr (le_abs_self x)
      have h₂ := Real.exp_le_exp.mpr (neg_le_abs x)
      linarith
    _ = |x| := Real.log_exp _

lemma logCosh_linearGrowth : HasLinearGrowth (fun x : ℝ => Real.log (Real.cosh x)) := by
  refine ⟨0, 1, le_rfl, zero_le_one, fun x => ?_⟩
  simpa only [zero_add, one_mul, Real.norm_eq_abs] using abs_log_cosh_le x

lemma measurable_logCosh : Measurable (fun x : ℝ => Real.log (Real.cosh x)) :=
  Real.measurable_log.comp Real.continuous_cosh.measurable

theorem gaussian_logCosh_cascade (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (m : ℕ → ℝ) (v : ℕ → ℝ≥0) (s : ℝ) :
    let μ : ℕ → ProbabilityMeasure ℝ := fun i => ⟨gaussianReal (m i) (v i), inferInstance⟩
    let u : ℕ → ℝ × ℝ → ℝ := fun _ p => p.1+p.2
    let F : ℝ → ℝ := fun x => Real.log (Real.cosh x)
    let P := (noiseCascadeLaw ℝ n b μ : Measure (NoiseTree ℝ n))
    let L := fun ν => Real.log
      ((terminalTreeFactor n b μ u F s ν).toReal / (noiseTreeTotal ℝ n ν).toReal)
    Integrable L P ∧ (∫ ν, L ν ∂P) = cascadeRecursion n b μ u F s ∧
    Integrable (fun ν => (L ν-cascadeRecursion n b μ u F s)^2) P ∧
    (∫ ν, (L ν-cascadeRecursion n b μ u F s)^2 ∂P) ≤
      4 * ∫ T, (Real.log (rawTreeTotal n T).toReal)^2 ∂(rawCascadeLaw n b : Measure (RawTree n)) := by
  exact (linearGrowth_noiseCascade_recursion n b hb
    (fun i => ⟨gaussianReal (m i) (v i), inferInstance⟩)
    (fun i _ => gaussianReal_exponentialNormMoments (m i) (v i))
    measurable_logCosh logCosh_linearGrowth s).2

lemma logMean_const_add_integrable {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {b : ℝ} {F : A → ℝ}
    (hF : Integrable (fun a => Real.exp (b*F a)) μ) (c : ℝ) :
    Integrable (fun a => Real.exp (b*(c+F a))) μ := by
  simpa only [mul_add,Real.exp_add] using hF.const_mul (Real.exp (b*c))

lemma logMean_abs_sub_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b)
    {F G : A → ℝ} (hF : Integrable (fun a => Real.exp (b*F a)) μ)
    (hG : Integrable (fun a => Real.exp (b*G a)) μ) {C : ℝ}
    (h : ∀ a, |F a-G a| ≤ C) : |logMean b μ F-logMean b μ G| ≤ C := by
  apply abs_le.mpr
  have hu : logMean b μ F ≤ C+logMean b μ G := by
    rw [← logMean_const_add μ hb.ne' hG C]
    exact logMean_mono μ hb hF (logMean_const_add_integrable hG C)
      (fun a => by linarith [(abs_le.mp (h a)).2])
  have hl : logMean b μ G ≤ C+logMean b μ F := by
    rw [← logMean_const_add μ hb.ne' hF C]
    exact logMean_mono μ hb hG (logMean_const_add_integrable hF C)
      (fun a => by linarith [(abs_le.mp (h a)).1])
  constructor <;> linarith

theorem cascadeRecursion_lipschitz {S : Type*} [SeminormedAddCommGroup S]
    [MeasurableSpace S] [MeasurableAdd₂ S]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure S)
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure S))
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    {L : ℝ} (hLip : ∀ x y, |F x-F y| ≤ L*‖x-y‖)
    (hb : ∀ i < n, 0 < b i) :
    ∀ x y, |cascadeRecursion n b μ (fun _ p => p.1+p.2) F x-
      cascadeRecursion n b μ (fun _ p => p.1+p.2) F y| ≤ L*‖x-y‖ := by
  induction n generalizing b μ with
  | zero => exact hLip
  | succ n ih =>
    let G := cascadeRecursion n (fun i => b (i+1)) (fun i => μ (i+1)) (fun _ p => p.1+p.2) F
    have hGm : Measurable G := measurable_cascadeRecursion n _ _
      (fun _ => measurable_fst.add measurable_snd) hF
    have hGG : HasLinearGrowth G := cascadeRecursion_linearGrowth n _ _
      (fun i hi => hμ (i+1) (by omega)) hF hG (fun i hi => hb (i+1) (by omega))
    have hGi (x : S) : Integrable (fun a => Real.exp (b 0*G (x+a))) (μ 0 : Measure S) :=
      integrable_exp_of_linearGrowth _ (hμ 0 (by omega))
        (hGm.comp (measurable_const.add measurable_id)) (hGG.add_left x) _
    intro x y
    apply logMean_abs_sub_le _ (hb 0 (by omega)) (hGi x) (hGi y)
    intro a
    simpa only [add_sub_add_right_eq_sub] using ih (fun i => b (i+1)) (fun i => μ (i+1))
      (fun i hi => hμ (i+1) (by omega)) (fun i hi => hb (i+1) (by omega)) (x+a) (y+a)

end IsingPerceptron

end

end OAI
