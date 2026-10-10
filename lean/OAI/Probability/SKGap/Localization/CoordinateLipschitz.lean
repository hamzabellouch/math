import Mathlib
import OAI.Probability.SKGap.Terminal.FiniteSpinCalculus
import OAI.Probability.SKGap.Brownian.ContinuousEnergy
import OAI.Probability.SKGap.Localization.UpperCoefficient

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
namespace SKGapCutoff

def CoordinateLipschitz {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ x y, |f x - f y| ≤ ∑ i, |x i - y i|

lemma CoordinateLipschitz.lipschitz {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} (hf : CoordinateLipschitz f) :
    LipschitzWith (Fintype.card ι) f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (f x) (f y) = |f x - f y| := Real.dist_eq _ _
    _ ≤ ∑ i, |x i - y i| := hf x y
    _ ≤ ∑ _ : ι, dist x y := Finset.sum_le_sum fun i _ => by
      simpa only [Real.dist_eq] using dist_le_pi_dist x y i
    _ = _ := by simp

lemma memLp_gaussian_pi_id {ι : Type*} [Fintype ι] (v : ℝ≥0) :
    MemLp (id : (ι → ℝ) → (ι → ℝ)) 2 (Measure.pi (fun _ => gaussianReal 0 v)) := by
  apply memLp_pi_iff.2
  intro i
  exact (memLp_id_gaussianReal (μ := 0) (v := v) 2).comp_measurePreserving
    (measurePreserving_eval _ i)

lemma memLp_gaussian_pi_of_lipschitz {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (v : ℝ≥0) :
    MemLp f 2 (Measure.pi (fun _ => gaussianReal 0 v)) := by
  have hsub : LipschitzWith K (fun x => f x - f 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using hf.dist_le_mul x y
  have h := hsub.comp_memLp (by simp) (memLp_gaussian_pi_id (ι := ι) v)
  convert h.add (memLp_const (f 0)) using 1
  · ext x; simp

lemma memLp_gaussian_real_of_lipschitz {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (v : ℝ≥0) : MemLp f 2 (gaussianReal 0 v) := by
  have hsub : LipschitzWith K (fun x => f x - f 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using hf.dist_le_mul x y
  have h := hsub.comp_memLp (by simp)
    (memLp_id_gaussianReal (μ := 0) (v := v) 2)
  convert h.add (memLp_const (f 0)) using 1 <;> try norm_num
  ext x
  simp

lemma gaussian_lipschitz_variance {f : ℝ → ℝ} (hf : LipschitzWith 1 f) (v : ℝ≥0) :
    variance f (gaussianReal 0 v) ≤ v := by
  have hm := memLp_gaussian_real_of_lipschitz hf v
  have hs : MemLp (fun z => f z - f 0) 2 (gaussianReal 0 v) := hm.sub (memLp_const (f 0))
  have hv : variance f (gaussianReal 0 v) =
      (∫ z, (f z - f 0)^2 ∂gaussianReal 0 v) -
        (∫ z, f z - f 0 ∂gaussianReal 0 v)^2 := by
    rw [← variance_sub_const hm.aestronglyMeasurable (f 0)]
    simpa only [Pi.pow_apply] using variance_eq_sub hs
  rw [hv]
  have hi : (∫ z, (f z - f 0)^2 ∂gaussianReal 0 v) ≤
      ∫ z, z^2 ∂gaussianReal 0 v := by
    apply integral_mono hs.integrable_sq
      (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
    intro z
    have h := hf.dist_le_mul z 0
    simp only [Real.dist_eq, NNReal.coe_one, one_mul, sub_zero] at h
    exact sq_le_sq.mpr h
  have hid : (∫ z : ℝ, z^2 ∂gaussianReal 0 v) = v := by
    have hh := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := v) 2)
    simpa only [variance_id_gaussianReal, integral_id_gaussianReal, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero,
      id_eq, Pi.pow_apply] using hh.symm
  rw [hid] at hi
  linarith [sq_nonneg (∫ z, f z - f 0 ∂gaussianReal 0 v)]

lemma coordinateLipschitz_cons_real {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : CoordinateLipschitz f) (x : Fin n → ℝ) :
    LipschitzWith 1 (fun z => f (Fin.cons z x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa [Real.dist_eq, Fin.sum_univ_succ] using hf (Fin.cons z x) (Fin.cons w x)

lemma coordinateLipschitz_integral_cons {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : CoordinateLipschitz f) (v : ℝ≥0) :
    CoordinateLipschitz (fun x : Fin n → ℝ =>
      ∫ z, f (Fin.cons z x) ∂gaussianReal 0 v) := by
  intro x y
  rw [← integral_sub
    ((memLp_gaussian_real_of_lipschitz (coordinateLipschitz_cons_real hf x) v).integrable one_le_two)
    ((memLp_gaussian_real_of_lipschitz (coordinateLipschitz_cons_real hf y) v).integrable one_le_two)]
  calc
    _ ≤ ∫ z, |f (Fin.cons z x) - f (Fin.cons z y)| ∂gaussianReal 0 v :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _ : ℝ, (∑ i, |x i - y i|) ∂gaussianReal 0 v := by
      apply integral_mono
        (((memLp_gaussian_real_of_lipschitz (coordinateLipschitz_cons_real hf x) v).integrable one_le_two).sub
          ((memLp_gaussian_real_of_lipschitz (coordinateLipschitz_cons_real hf y) v).integrable one_le_two)).abs
        (integrable_const _)
      intro z
      simpa [Fin.sum_univ_succ] using hf (Fin.cons z x) (Fin.cons z y)
    _ = _ := by simp

lemma integral_gaussian_fin_succ {n : ℕ} (v : ℝ≥0)
    (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : Integrable f (Measure.pi (fun _ => gaussianReal 0 v))) :
    (∫ x, f x ∂Measure.pi (fun _ => gaussianReal 0 v)) =
      ∫ x : Fin n → ℝ, ∫ z : ℝ, f (Fin.cons z x) ∂gaussianReal 0 v
        ∂Measure.pi (fun _ => gaussianReal 0 v) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 v) 0).symm
  have he (p : ℝ × (Fin n → ℝ)) : e p = Fin.cons p.1 p.2 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  rw [← hm.integral_comp']
  change (∫ p : ℝ × (Fin n → ℝ), f (e p) ∂(gaussianReal 0 v).prod
    (Measure.pi (fun _ => gaussianReal 0 v))) = _
  simp_rw [he]
  apply integral_prod_symm
  have hi := (hm.integrable_comp hf.aestronglyMeasurable).mpr hf
  change Integrable (fun p : ℝ × (Fin n → ℝ) => f (e p)) _ at hi
  simpa only [he] using hi

lemma gaussian_coordinate_variance_fin (v : ℝ≥0) (n : ℕ)
    {f : (Fin n → ℝ) → ℝ} (hf : CoordinateLipschitz f) :
    variance f (Measure.pi (fun _ => gaussianReal 0 v)) ≤ (n : ℝ) * v := by
  induction n with
  | zero =>
    have he : f = fun _ => f 0 := funext fun x => congrArg f (Subsingleton.elim x 0)
    rw [he, variance_eq_sub (memLp_const _)]
    simp
  | succ n ih =>
    let g : (Fin n → ℝ) → ℝ := fun x => ∫ z, f (Fin.cons z x) ∂gaussianReal 0 v
    have hg := coordinateLipschitz_integral_cons hf v
    have hfm := memLp_gaussian_pi_of_lipschitz hf.lipschitz v
    have hgm := memLp_gaussian_pi_of_lipschitz hg.lipschitz v
    change MemLp g 2 _ at hgm
    have hpoint (x : Fin n → ℝ) :
        (∫ z, f (Fin.cons z x)^2 ∂gaussianReal 0 v) ≤ v + g x ^ 2 := by
      have hv := gaussian_lipschitz_variance (coordinateLipschitz_cons_real hf x) v
      rw [variance_eq_sub (memLp_gaussian_real_of_lipschitz
        (coordinateLipschitz_cons_real hf x) v)] at hv
      change (∫ z, f (Fin.cons z x)^2 ∂gaussianReal 0 v) - g x ^ 2 ≤ v at hv
      linarith
    have hsq := integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun x => integral_nonneg (fun z => sq_nonneg _)))
      ((integrable_const (v : ℝ)).add hgm.integrable_sq) (Filter.Eventually.of_forall hpoint)
    simp only [Pi.add_apply] at hsq
    rw [integral_add (f := fun _ => (v : ℝ)) (g := fun x => g x ^ 2)
      (integrable_const _) hgm.integrable_sq, integral_const] at hsq
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hsq
    rw [← integral_gaussian_fin_succ v (fun x => f x^2) hfm.integrable_sq] at hsq
    have hih := ih hg
    rw [variance_eq_sub hgm] at hih
    rw [variance_eq_sub hfm, integral_gaussian_fin_succ v f (hfm.integrable one_le_two)]
    change (∫ x, f x^2 ∂Measure.pi (fun _ => gaussianReal 0 v)) -
      (∫ x, g x ∂Measure.pi (fun _ => gaussianReal 0 v))^2 ≤ ((n+1 : ℕ) : ℝ) * v
    push_cast
    change (∫ x, g x^2 ∂Measure.pi (fun _ => gaussianReal 0 v)) -
      (∫ x, g x ∂Measure.pi (fun _ => gaussianReal 0 v))^2 ≤ (n : ℝ)*v at hih
    linarith

lemma gaussian_coordinate_variance {ι : Type*} [Fintype ι] (v : ℝ≥0)
    {f : (ι → ℝ) → ℝ} (hf : CoordinateLipschitz f) :
    variance f (Measure.pi (fun _ => gaussianReal 0 v)) ≤ (Fintype.card ι : ℝ) * v := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let T := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  have hm := measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 v) e
  have hg : CoordinateLipschitz (fun x => f (T x)) := by
    intro x y
    calc
      _ ≤ ∑ i : ι, |T x i - T y i| := hf _ _
      _ = ∑ i : Fin (Fintype.card ι), |x i - y i| := by
        rw [← e.sum_comp]
        simp [T, MeasurableEquiv.piCongrLeft_apply_apply]
  rw [← hm.variance_fun_comp hf.lipschitz.continuous.measurable.aemeasurable]
  exact gaussian_coordinate_variance_fin v _ hg

lemma abs_upperCoefficient_le_one {n : ℕ} (x : Spin n) (p : Fin n × Fin n) :
    |upperCoefficient x p| ≤ 1 := by
  unfold upperCoefficient
  split_ifs
  · rw [abs_mul]; cases h₁ : x p.1 <;> cases h₂ : x p.2 <;> simp [spin, h₁, h₂]
  · simp

lemma energy_sampled_diff_le {n : ℕ} (x : Spin n) (g h : GaussianCoordinates n) :
    |energy (sampledInteraction g) x - energy (sampledInteraction h) x| ≤
      ∑ p, |g p - h p| := by
  simp only [energy_sampled, ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ p, |upperCoefficient x p * (g p - h p)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun p _ => by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_upperCoefficient_le_one x p)

lemma log_partition_sampled_le {n : ℕ} (g h : GaussianCoordinates n) :
    Real.log (partition (sampledInteraction g)) ≤
      (∑ p, |g p - h p|) + Real.log (partition (sampledInteraction h)) := by
  have hp : partition (sampledInteraction g) ≤
      Real.exp (∑ p, |g p - h p|) * partition (sampledInteraction h) := by
    unfold partition
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := (le_abs_self _).trans (energy_sampled_diff_le x g h)
    linarith
  have hh := Real.log_le_log (partition_pos _) hp
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (partition_pos _)),
    Real.log_exp] at hh
  exact hh

lemma coordinateLipschitz_log_partition (n : ℕ) :
    CoordinateLipschitz (fun g : GaussianCoordinates n =>
      Real.log (partition (sampledInteraction g))) := by
  intro g h
  apply abs_le.mpr
  have hg := log_partition_sampled_le g h
  have hh := log_partition_sampled_le h g
  simp_rw [abs_sub_comm (h _) (g _)] at hh
  constructor <;> linarith

lemma memLp_log_partition (β : ℝ) (n : ℕ) :
    MemLp (fun g => Real.log (partition (sampledInteraction g))) 2 (disorderLaw β n) :=
  memLp_gaussian_pi_of_lipschitz (coordinateLipschitz_log_partition n).lipschitz _

lemma variance_log_partition_le (β : ℝ) {n : ℕ} (hn : 0 < n) :
    variance (fun g => Real.log (partition (sampledInteraction g))) (disorderLaw β n) ≤
      β ^ 2 * n := by
  have h := gaussian_coordinate_variance (Real.toNNReal (β ^ 2 / n))
    (coordinateLipschitz_log_partition n)
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    Real.coe_toNNReal _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))] at h
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have he : (n : ℝ) * n * (β ^ 2 / n) = β ^ 2 * n := by field_simp
  rw [he] at h
  exact h

lemma integral_sq_cauchy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ x, f x ^ 2 ∂μ := by
  by_cases hμ : μ = 0
  · simp [hμ]
  have hM : 0 < μ.real Set.univ := by
    rw [measureReal_def, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr (Measure.measure_univ_ne_zero.mpr hμ), measure_lt_top _ _⟩
  let M := μ.real Set.univ
  let I := ∫ x, f x ∂μ
  have hp (x : Ω) : (M * f x - I) ^ 2 =
      M ^ 2 * f x ^ 2 - (2 * M * I) * f x + I ^ 2 := by ring
  have h := integral_nonneg (μ := μ) (f := fun x => (M * f x - I) ^ 2)
    (fun x => sq_nonneg _)
  simp_rw [hp] at h
  rw [integral_add (f := fun x => M ^ 2 * f x ^ 2 - (2 * M * I) * f x)
    (g := fun _ => I ^ 2) ((hf2.const_mul _).sub (hf.const_mul _)) (integrable_const _),
    integral_sub (f := fun x => M ^ 2 * f x ^ 2) (g := fun x => (2 * M * I) * f x)
      (hf2.const_mul _) (hf.const_mul _), integral_const_mul,
    integral_const_mul, integral_const] at h
  simp only [smul_eq_mul] at h
  change 0 ≤ M ^ 2 * (∫ x, f x ^ 2 ∂μ) - 2 * M * I * I + M * I ^ 2 at h
  change I ^ 2 ≤ M * ∫ x, f x ^ 2 ∂μ
  have h' : 0 ≤ M * (M * (∫ x, f x ^ 2 ∂μ) - I ^ 2) := by nlinarith
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hM).mp h')

lemma second_moment_lower_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hm : Measurable f) (hfp : ∀ x, 0 ≤ f x) {a : ℝ}
    (ha : 0 ≤ a) (ham : a ≤ ∫ x, f x ∂μ) :
    ((∫ x, f x ∂μ) - a) ^ 2 ≤ μ.real {x | a ≤ f x} * ∫ x, f x ^ 2 ∂μ := by
  let A := {x | a ≤ f x}
  have hA : MeasurableSet A := measurableSet_le measurable_const hm
  have hIc : (∫ x in Aᶜ, f x ∂μ) ≤ a := by
    calc
      _ ≤ ∫ _ in Aᶜ, a ∂μ := by
        apply setIntegral_mono_on hf.integrableOn (integrable_const _).integrableOn hA.compl
        intro x hx
        exact le_of_lt (lt_of_not_ge hx)
      _ = μ.real Aᶜ * a := by rw [setIntegral_const]; rfl
      _ ≤ a := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (measureReal_le_one (μ := μ) (s := Aᶜ)) ha
  have hdecomp := integral_add_compl hA hf
  have hI : (∫ x, f x ∂μ) - a ≤ ∫ x in A, f x ∂μ := by linarith
  have hI0 : 0 ≤ ∫ x in A, f x ∂μ := integral_nonneg hfp
  have hsq := integral_sq_cauchy (μ.restrict A) hf.integrableOn hf2.integrableOn
  simp only [measureReal_restrict_apply_univ] at hsq
  have hQ : (∫ x in A, f x ^ 2 ∂μ) ≤ ∫ x, f x ^ 2 ∂μ :=
    setIntegral_le_integral hf2 (Filter.Eventually.of_forall (fun x => sq_nonneg (f x)))
  have hQ' := mul_le_mul_of_nonneg_left hQ (measureReal_nonneg (μ := μ) (s := A))
  have hab : 0 ≤ (∫ x, f x ∂μ) - a := sub_nonneg.mpr ham
  nlinarith

open ProbabilityTheory
lemma partition_half_mean_probability (β : ℝ) (hβ : β ^ 2 < 1)
    {n : ℕ} (hn : 0 < n) :
    Real.sqrt (1 - β ^ 2) / 4 ≤ (disorderLaw β n).real
      {g | (∫ h, partition (sampledInteraction h) ∂disorderLaw β n) / 2 ≤
        partition (sampledInteraction g)} := by
  let : IsProbabilityMeasure (disorderLaw β n) := by unfold disorderLaw; infer_instance
  let m := ∫ g, partition (sampledInteraction g) ∂disorderLaw β n
  let q := ∫ g, partition (sampledInteraction g) ^ 2 ∂disorderLaw β n
  let p := (disorderLaw β n).real {g | m / 2 ≤ partition (sampledInteraction g)}
  have hm : 0 < m := by
    dsimp [m]
    rw [integral_partition_sampled β hn]
    positivity
  have hs : 0 < Real.sqrt (1 - β ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hz := second_moment_lower_probability (disorderLaw β n)
    (integrable_partition_sampled β n) (integrable_partition_sq_sampled β n)
    (((continuous_partition n).comp (continuous_sampledInteraction n)).measurable)
    (fun g => le_of_lt (partition_pos _)) (a := m / 2) (by positivity) (by dsimp [m]; linarith)
  change (m - m / 2) ^ 2 ≤ p * q at hz
  have hu := partition_second_moment_bound β hβ hn
  change q / m ^ 2 ≤ (Real.sqrt (1 - β ^ 2))⁻¹ at hu
  have hu' : q * Real.sqrt (1 - β ^ 2) ≤ m ^ 2 := by
    rw [div_le_iff₀ (sq_pos_of_pos hm)] at hu
    have := mul_le_mul_of_nonneg_left hu (le_of_lt hs)
    field_simp at this
    nlinarith
  have hp : 0 ≤ p := measureReal_nonneg
  have hh := mul_le_mul_of_nonneg_right hz (le_of_lt hs)
  have hh' := mul_le_mul_of_nonneg_left hu' hp
  change Real.sqrt (1 - β ^ 2) / 4 ≤ p
  nlinarith [sq_pos_of_pos hm]

lemma mean_ge_of_upper_event {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ)
    {a p : ℝ} (hp : 0 < p) (hprob : p ≤ μ.real {x | a ≤ f x}) :
    a - Real.sqrt (variance f μ / p) ≤ ∫ x, f x ∂μ := by
  by_cases ha : a ≤ ∫ x, f x ∂μ
  · linarith [Real.sqrt_nonneg (variance f μ / p)]
  have hc : 0 < a - ∫ x, f x ∂μ := sub_pos.mpr (lt_of_not_ge ha)
  have hsub : {x | a ≤ f x} ⊆
      {x | a - (∫ x, f x ∂μ) ≤ |f x - (∫ x, f x ∂μ)|} := by
    intro x hx
    change a ≤ f x at hx
    exact (sub_le_sub_right hx _).trans (le_abs_self _)
  have hm := meas_ge_le_variance_div_sq hf hc
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at hr
  have hreal : p ≤ variance f μ / (a - (∫ x, f x ∂μ)) ^ 2 :=
    hprob.trans ((measureReal_mono hsub).trans hr)
  rw [le_div_iff₀ (sq_pos_of_pos hc)] at hreal
  have hs := Real.sq_sqrt (div_nonneg (variance_nonneg f μ) (le_of_lt hp))
  have he : p * Real.sqrt (variance f μ / p)^2 = variance f μ := by
    rw [hs]; field_simp
  have hle : a - (∫ x, f x ∂μ) ≤ Real.sqrt (variance f μ / p) := by
    have hz := Real.sqrt_nonneg (variance f μ / p)
    have hc2 := (mul_le_mul_iff_of_pos_left hp).mp (hreal.trans_eq he.symm)
    nlinarith
  linarith

lemma integral_log_partition_le_log_mean (β : ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ g, Real.log (partition (sampledInteraction g)) ∂disorderLaw β n) ≤
      Real.log (∫ g, partition (sampledInteraction g) ∂disorderLaw β n) := by
  let μ := disorderLaw β n
  let : IsProbabilityMeasure μ := by dsimp [μ, disorderLaw]; infer_instance
  let m := ∫ g, partition (sampledInteraction g) ∂μ
  have hm : 0 < m := by dsimp [m, μ]; rw [integral_partition_sampled β hn]; positivity
  have hi := integral_mono (memLp_log_partition β n |>.integrable one_le_two)
    ((integrable_const (Real.log m)).add
      ((integrable_partition_sampled β n).div_const m) |>.sub (integrable_const 1))
    (fun g => show Real.log (partition (sampledInteraction g)) ≤
        Real.log m + partition (sampledInteraction g) / m - 1 from by
      have hl := Real.log_le_sub_one_of_pos (div_pos (partition_pos (sampledInteraction g)) hm)
      rw [Real.log_div (ne_of_gt (partition_pos _)) (ne_of_gt hm)] at hl
      linarith)
  simp only [Pi.sub_apply, Pi.add_apply] at hi
  rw [integral_sub (f := fun g => Real.log m + partition (sampledInteraction g) / m)
    (g := fun _ => 1) ((integrable_const _).add ((integrable_partition_sampled β n).div_const _))
      (integrable_const _), integral_add (integrable_const _)
      ((integrable_partition_sampled β n).div_const _), integral_const, integral_const,
    integral_div] at hi
  change (∫ g, Real.log (partition (sampledInteraction g)) ∂μ) ≤
    μ.real Set.univ • Real.log m + m / m - μ.real Set.univ • 1 at hi
  simpa [ne_of_gt hm] using hi

lemma integral_log_partition_ge_log_mean (β : ℝ) (hβ : β ^ 2 < 1)
    {n : ℕ} (hn : 0 < n) :
    Real.log (∫ g, partition (sampledInteraction g) ∂disorderLaw β n) - Real.log 2 -
      Real.sqrt (β ^ 2 * n / (Real.sqrt (1 - β ^ 2) / 4)) ≤
        ∫ g, Real.log (partition (sampledInteraction g)) ∂disorderLaw β n := by
  let μ := disorderLaw β n
  let : IsProbabilityMeasure μ := by dsimp [μ, disorderLaw]; infer_instance
  let m := ∫ g, partition (sampledInteraction g) ∂μ
  have hm : 0 < m := by dsimp [m, μ]; rw [integral_partition_sampled β hn]; positivity
  have hp : 0 < Real.sqrt (1 - β ^ 2) / 4 := by
    exact div_pos (Real.sqrt_pos.2 (by linarith)) (by norm_num)
  have hprob := partition_half_mean_probability β hβ hn
  have he : {g : GaussianCoordinates n | m / 2 ≤ partition (sampledInteraction g)} =
      {g : GaussianCoordinates n | Real.log m - Real.log 2 ≤ Real.log (partition (sampledInteraction g))} := by
    ext g
    rw [← Real.log_div (ne_of_gt hm) (by norm_num)]
    exact (Real.log_le_log_iff (by positivity) (partition_pos _)).symm
  change Real.sqrt (1 - β ^ 2) / 4 ≤ μ.real {g | m / 2 ≤ partition (sampledInteraction g)} at hprob
  rw [he] at hprob
  have hv := variance_log_partition_le β hn
  have hs := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hv (le_of_lt hp))
  have hl := mean_ge_of_upper_event μ (memLp_log_partition β n) hp hprob
  dsimp [m, μ] at hl hs ⊢
  linarith

lemma square_integral_shift {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) (a : ℝ) :
    (∫ x, (f x - a)^2 ∂μ) = variance f μ + ((∫ x, f x ∂μ) - a)^2 := by
  have hs : MemLp (fun x => f x - a) 2 μ := hf.sub (memLp_const a)
  have hv := variance_eq_sub hs
  rw [variance_sub_const hf.aestronglyMeasurable] at hv
  simp only [Pi.pow_apply] at hv
  rw [integral_sub (hf.integrable one_le_two) (integrable_const _), integral_const] at hv
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hv
  linarith

lemma second_moment_log_partition_centered_le (β : ℝ) (hβ : β ^ 2 < 1)
    {n : ℕ} (hn : 0 < n) :
    (∫ g, (Real.log (partition (sampledInteraction g)) -
      Real.log (∫ h, partition (sampledInteraction h) ∂disorderLaw β n)) ^ 2
        ∂disorderLaw β n) ≤
      (β ^ 2 + 2 * β ^ 2 / (Real.sqrt (1 - β ^ 2) / 4)) * n + 2 * (Real.log 2)^2 := by
  let μ := disorderLaw β n
  let : IsProbabilityMeasure μ := by dsimp [μ, disorderLaw]; infer_instance
  let c := Real.log (∫ g, partition (sampledInteraction g) ∂μ)
  let m := ∫ g, Real.log (partition (sampledInteraction g)) ∂μ
  let p := Real.sqrt (1 - β ^ 2) / 4
  have hp : 0 < p := by dsimp [p]; positivity
  have hs : Real.sqrt (β ^ 2 * n / p)^2 = β ^ 2 * n / p :=
    Real.sq_sqrt (by positivity)
  have hmUpper := integral_log_partition_le_log_mean β hn
  have hmLower := integral_log_partition_ge_log_mean β hβ hn
  change m ≤ c at hmUpper
  change c - Real.log 2 - Real.sqrt (β ^ 2 * n / p) ≤ m at hmLower
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsq : (m-c)^2 ≤ 2 * (Real.log 2)^2 + 2 * β ^ 2 * n / p := by
    have hm0 : 0 ≤ c-m := sub_nonneg.mpr hmUpper
    have hms : c-m ≤ Real.log 2 + Real.sqrt (β ^ 2 * n / p) := by linarith
    have hmsq := sq_le_sq₀ hm0 (by positivity : 0 ≤ Real.log 2 + Real.sqrt (β^2*n/p)) |>.mpr hms
    have hh : 2 * β ^ 2 * (n : ℝ) / p = 2 * (β ^ 2 * n / p) := by ring
    rw [hh]
    nlinarith [sq_nonneg (Real.log 2 - Real.sqrt (β^2*n/p))]
  rw [square_integral_shift μ (memLp_log_partition β n) c]
  have hv := variance_log_partition_le β hn
  change variance (fun g => Real.log (partition (sampledInteraction g))) μ ≤ β^2*n at hv
  change variance (fun g => Real.log (partition (sampledInteraction g))) μ + (m-c)^2 ≤ _
  calc
    _ ≤ β^2*n + (2 * (Real.log 2)^2 + 2 * β^2*n/p) := add_le_add hv hsq
    _ = _ := by dsimp [p]; ring

end SKGapCutoff
end

end OAI
