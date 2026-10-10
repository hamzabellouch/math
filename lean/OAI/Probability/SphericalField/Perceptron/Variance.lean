import Mathlib
import OAI.Probability.SphericalField.Perceptron.Partition

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
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

section BoundedDifferences
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

end BoundedDifferences

lemma abs_hamiltonian_update_sub_le (α : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α N) (a : Fin (patternCount α N)) (y : Fin N → ℝ) (x : Spin N) :
    |hamiltonian α φ N (Function.update g a y) x - hamiltonian α φ N g x| ≤ 2 * ‖φ‖ := by
  classical
  have heq : hamiltonian α φ N (Function.update g a y) x - hamiltonian α φ N g x =
      φ (patternField (Function.update g a y) a x) - φ (patternField g a x) := by
    unfold hamiltonian
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_single a
    · intro b _ hba
      simp [patternField, Function.update_of_ne hba]
    · simp
  rw [heq]
  calc
    _ ≤ |φ (patternField (Function.update g a y) a x)| + |φ (patternField g a x)| :=
      abs_sub _ _
    _ ≤ ‖φ‖ + ‖φ‖ := add_le_add (φ.norm_coe_le_norm _) (φ.norm_coe_le_norm _)
    _ = _ := by ring

lemma abs_pressure_update_sub_le (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ)
    (g : Patterns α (N + 1)) (a : Fin (patternCount α (N + 1))) (y : Fin (N + 1) → ℝ) :
    |pressure α β φ (N + 1) (Function.update g a y) - pressure α β φ (N + 1) g| ≤
      (2 * |β| * ‖φ‖) / (N + 1 : ℝ) := by
  have hh := abs_log_integral_exp_sub_le (sphereLaw (N + 1))
    (integrable_partition α β φ N (Function.update g a y)) (integrable_partition α β φ N g)
    (partition_pos α β φ N (Function.update g a y)) (partition_pos α β φ N g)
    (c := 2 * |β| * ‖φ‖) (fun x => by
      rw [← mul_sub, abs_mul]
      calc
        _ ≤ |β| * (2 * ‖φ‖) := mul_le_mul_of_nonneg_left
          (abs_hamiltonian_update_sub_le α φ (N + 1) g a y x) (abs_nonneg β)
        _ = _ := by ring)
  unfold pressure
  rw [← sub_div, abs_div, abs_of_nonneg (show 0 ≤ ((N + 1 : ℕ) : ℝ) by positivity)]
  simpa only [Nat.cast_add, Nat.cast_one] using div_le_div_of_nonneg_right hh
    (show 0 ≤ (N + 1 : ℝ) by positivity)

lemma variance_pressure_le (α β : ℝ) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    variance (pressure α β φ (N + 1)) (patternLaw α (N + 1)) ≤
      (patternCount α (N + 1) : ℝ) * ((2 * |β| * ‖φ‖) / (N + 1 : ℝ)) ^ 2 := by
  exact variance_pi_le_of_bounded_differences (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
    (patternCount α (N + 1)) (continuous_pressure α β φ N)
    (abs_pressure_le α β φ N) (abs_pressure_update_sub_le α β φ N)

lemma variance_pressure_le_rate (α β : ℝ) (hα : 0 ≤ α) (φ : ℝ →ᵇ ℝ) (N : ℕ) :
    variance (pressure α β φ (N + 1)) (patternLaw α (N + 1)) ≤
      α * (2 * |β| * ‖φ‖) ^ 2 / (N + 1 : ℝ) := by
  have hM : (patternCount α (N + 1) : ℝ) ≤ α * (N + 1 : ℝ) := by
    simpa [patternCount] using Nat.floor_le
      (mul_nonneg hα (show 0 ≤ ((N + 1 : ℕ) : ℝ) by positivity))
  calc
    _ ≤ (patternCount α (N + 1) : ℝ) * ((2 * |β| * ‖φ‖) / (N + 1 : ℝ)) ^ 2 :=
      variance_pressure_le α β φ N
    _ ≤ (α * (N + 1 : ℝ)) * ((2 * |β| * ‖φ‖) / (N + 1 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hM (sq_nonneg _)
    _ = _ := by
      have hn : (N + 1 : ℝ) ≠ 0 := by positivity
      field_simp

lemma pressure_deviation_le (α β : ℝ) (hα : 0 ≤ α) (φ : ℝ →ᵇ ℝ)
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    patternLaw α (N + 1)
      {g | ε < |pressure α β φ (N + 1) g - expectedPressure α β φ (N + 1)|} ≤
    ENNReal.ofReal ((α * (2 * |β| * ‖φ‖) ^ 2 / (N + 1 : ℝ)) / ε ^ 2) := by
  have hp : MemLp (pressure α β φ (N + 1)) 2 (patternLaw α (N + 1)) :=
    MemLp.of_bound (continuous_pressure α β φ N).aestronglyMeasurable _
      (Filter.Eventually.of_forall (abs_pressure_le α β φ N))
  calc
    _ ≤ patternLaw α (N + 1)
        {g | ε ≤ |pressure α β φ (N + 1) g - expectedPressure α β φ (N + 1)|} :=
      by
        apply measure_mono
        intro g hg
        change ε < |pressure α β φ (N + 1) g - expectedPressure α β φ (N + 1)| at hg
        change ε ≤ |pressure α β φ (N + 1) g - expectedPressure α β φ (N + 1)|
        exact le_of_lt hg
    _ ≤ ENNReal.ofReal (variance (pressure α β φ (N + 1)) (patternLaw α (N + 1)) / ε ^ 2) :=
      meas_ge_le_variance_div_sq hp hε
    _ ≤ _ := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (variance_pressure_le_rate α β hα φ N) (sq_nonneg _))

end SphericalPerceptron
end
end

end OAI
