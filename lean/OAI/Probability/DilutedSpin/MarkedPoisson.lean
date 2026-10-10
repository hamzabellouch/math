import OAI.Probability.DilutedSpin.PoissonMoments

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

/-- The archival Mathlib Poisson weights, not a replacement count model. -/
noncomputable def poissonWeight (r : ℝ≥0) (n : ℕ) : ℝ :=
  Real.exp (-(r : ℝ)) * (r : ℝ)^n / (n.factorial : ℝ)

@[simp] theorem poissonWeight_nonneg (r : ℝ≥0) (n : ℕ) : 0 ≤ poissonWeight r n := by
  unfold poissonWeight
  positivity

theorem poissonWeight_succ_mul (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1 : ℕ) = (r : ℝ) * poissonWeight r n := by
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Poisson add-one (the count part of pert:palm), including zero rate. -/
theorem poisson_add_one (r : ℝ≥0) (f : ℕ → ℝ)
    (hf : Integrable (fun n => f (n+1)) (poissonMeasure r)) :
    (∫ n : ℕ, (n : ℝ) * f n ∂poissonMeasure r) =
      (r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r := by
  have hs := (hasSum_integral_poissonMeasure hf).mul_left (r : ℝ)
  simp only [smul_eq_mul] at hs
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ) * f (n+1))
      ((r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r) := by
    simp_rw [poissonWeight_succ_mul]
    simpa only [poissonWeight, mul_assoc] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ) * f n) ht
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add] at ht'
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul, ← mul_assoc, poissonWeight] using ht'.tsum_eq

/-- Integrability of the count is proved from the same add-one recurrence. -/
theorem poisson_integrable_count (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)) r := by
    simp_rw [poissonWeight_succ_mul]
    unfold poissonWeight
    simpa only [mul_one] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ)) ht
  simp only [Nat.cast_zero, mul_zero, zero_add] at ht'
  simpa only [Real.norm_natCast, poissonWeight] using ht'.summable

@[simp] theorem poisson_mean (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  simpa using poisson_add_one r (fun _ => 1) (integrable_const 1)

theorem poisson_integrable_linear (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A + B*n) : Integrable f (poissonMeasure r) := by
  apply ((integrable_const A).add ((poisson_integrable_count r).const_mul B)).mono
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)
  exact ae_of_all _ (fun n => (h n).trans (le_abs_self _))

theorem poisson_integrable_count_sq (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)^2) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hnext : Integrable (fun n : ℕ => ((n+1 : ℕ) : ℝ)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 1) (B := 1)
    intro n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ))]
    simp only [Nat.cast_add, Nat.cast_one, one_mul]
    exact le_of_eq (add_comm _ _)
  have hs := (hasSum_integral_poissonMeasure hnext).mul_left (r : ℝ)
  simp only [smul_eq_mul] at hs
  have ht : Summable (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)^2) := by
    simp_rw [pow_two, ← mul_assoc, poissonWeight_succ_mul]
    simpa only [poissonWeight, mul_assoc] using hs.summable
  have ht' := Summable.comp_nat_add (f := fun n => poissonWeight r n * (n : ℝ)^2) (k := 1) ht
  simpa only [Real.norm_eq_abs, abs_sq, poissonWeight] using ht'

@[simp] theorem poisson_second_moment (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ)^2 ∂poissonMeasure r) = (r : ℝ)^2 + r := by
  have hi : Integrable (fun n : ℕ => ((n+1 : ℕ) : ℝ)) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 1) (B := 1)
    intro n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n+1 : ℕ) : ℝ))]
    simp only [Nat.cast_add, Nat.cast_one, one_mul]
    exact le_of_eq (add_comm _ _)
  have h := poisson_add_one r (fun n => (n : ℝ)) hi
  simp only [← pow_two, Nat.cast_add, Nat.cast_one] at h
  rw [integral_add (poisson_integrable_count r) (integrable_const 1), poisson_mean,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  nlinarith

theorem poisson_variance (r : ℝ≥0) :
    (∫ n : ℕ, ((n : ℝ) - r)^2 ∂poissonMeasure r) = r := by
  have heq : (fun n : ℕ => ((n : ℝ)-r)^2) =
      (fun n : ℕ => (n : ℝ)^2 - 2*(r : ℝ)*(n : ℝ) + (r : ℝ)^2) := by
    funext n
    ring
  rw [heq]
  have hi : Integrable (fun n : ℕ => (n : ℝ)^2 - 2*(r : ℝ)*n) (poissonMeasure r) :=
    (poisson_integrable_count_sq r).sub ((poisson_integrable_count r).const_mul (2*(r : ℝ)))
  rw [integral_add hi (integrable_const ((r : ℝ)^2)),
    integral_sub (poisson_integrable_count_sq r) ((poisson_integrable_count r).const_mul (2*r)),
    integral_const_mul, poisson_second_moment, poisson_mean, integral_const,
    probReal_univ, smul_eq_mul, one_mul]
  ring

end DilutedSpinGlass

namespace DilutedSpinGlass

/-- A quadratic envelope suffices; no exponential moment is used. -/
theorem poisson_integrable_quadratic (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A + B*(n : ℝ)^2) : Integrable f (poissonMeasure r) := by
  apply ((integrable_const A).add ((poisson_integrable_count_sq r).const_mul B)).mono
    (StronglyMeasurable.of_discrete.aestronglyMeasurable)
  exact ae_of_all _ (fun n => (h n).trans (le_abs_self _))

/-- Lipschitz sequences have a square-integrable Poisson law. -/
theorem poisson_memLp_lipschitz (r : ℝ≥0) {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ n m, |f n-f m| ≤ C*|(n : ℝ)-(m : ℝ)|) :
    MemLp f 2 (poissonMeasure r) := by
  apply (memLp_two_iff_integrable_sq StronglyMeasurable.of_discrete.aestronglyMeasurable).mpr
  apply poisson_integrable_quadratic r (A := 2*(f 0)^2) (B := 2*C^2)
  intro n
  have h := hL n 0
  simp only [Nat.cast_zero, sub_zero, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at h
  have hh : |f n| ≤ C*(n : ℝ)+|f 0| := by
    calc |f n| = |(f n-f 0)+f 0| := by rw [sub_add_cancel]
         _ ≤ |f n-f 0| + |f 0| := abs_add_le _ _
         _ ≤ C*(n : ℝ)+|f 0| := by linarith
  have hb : 0 ≤ C*(n : ℝ)+|f 0| := by positivity
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (f n), sq_abs (f 0),
    sq_nonneg (C*(n : ℝ)-|f 0|), mul_nonneg (sub_nonneg.mpr hh) (add_nonneg hb (abs_nonneg (f n)))]

/-- Poisson random-coordinate count variance: a count-Lipschitz logarithm
has fluctuations of order sqrt(rate), not order rate. -/
theorem poisson_variance_lipschitz (r : ℝ≥0) {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ n m, |f n-f m| ≤ C*|(n : ℝ)-(m : ℝ)|) :
    variance f (poissonMeasure r) ≤ C^2 * (r : ℝ) := by
  have hf := poisson_memLp_lipschitz r hC hL
  have hn : MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) :=
    (memLp_two_iff_integrable_sq StronglyMeasurable.of_discrete.aestronglyMeasurable).mpr
      (poisson_integrable_count_sq r)
  have hp : ∀ n m : ℕ, (f n-f m)^2 ≤ C^2*((n : ℝ)-(m : ℝ))^2 := by
    intro n m
    have h := hL n m
    have hnon : 0 ≤ C*|(n : ℝ)-(m : ℝ)| := mul_nonneg hC (abs_nonneg _)
    nlinarith [sq_abs (f n-f m), sq_abs ((n : ℝ)-(m : ℝ)),
      mul_nonneg (sub_nonneg.mpr h) (add_nonneg hnon (abs_nonneg (f n-f m)))]
  let μ := poissonMeasure r
  have hint (n : ℕ) := integral_mono
    ((memLp_const (f n)).sub hf).integrable_sq
    (((memLp_const (n : ℝ)).sub hn).integrable_sq.const_mul (C^2)) (hp n)
  have hfprod : MemLp (fun z : ℕ × ℕ => f z.1-f z.2) 2 (μ.prod μ) :=
    (hf.comp_fst μ).sub (hf.comp_snd μ)
  have hnprod : MemLp (fun z : ℕ × ℕ => (z.1 : ℝ)-(z.2 : ℝ)) 2 (μ.prod μ) :=
    (hn.comp_fst μ).sub (hn.comp_snd μ)
  have h := integral_mono hfprod.integrable_sq.integral_prod_left
    (hnprod.integrable_sq.const_mul (C^2)).integral_prod_left hint
  simp_rw [integral_const_mul] at h
  rw [variance_two_copies hf, variance_two_copies hn,
    variance_eq_integral (Measurable.of_discrete (f := fun n : ℕ => (n : ℝ))).aemeasurable, poisson_mean, poisson_variance] at h
  nlinarith

end DilutedSpinGlass

namespace DilutedSpinGlass

/-- Adding one root coordinate gives the full Lipschitz bound in the count. -/
theorem nat_lipschitz_of_step {f : ℕ → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (h : ∀ n, |f (n+1)-f n| ≤ C) : ∀ n m, |f n-f m| ≤ C*|(n : ℝ)-(m : ℝ)| := by
  have hle : ∀ n m, n ≤ m → |f m-f n| ≤ C*((m : ℝ)-(n : ℝ)) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m hnm ih =>
      have ha : |f (m+1)-f n| ≤ |f (m+1)-f m|+|f m-f n| := by
        calc
          |f (m+1)-f n| = |(f (m+1)-f m)+(f m-f n)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      push_cast
      nlinarith [h m]
  intro n m
  rcases le_total n m with hnm | hmn
  · rw [abs_sub_comm (f n), abs_sub_comm (n : ℝ), abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hnm : (n : ℝ) ≤ m))]
    exact hle n m hnm
  · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmn : (m : ℝ) ≤ n))]
    exact hle m n hmn

/-- Centering at an arbitrary constant separates conditional variance and
squared conditional-mean displacement. -/
theorem integral_sq_sub_center {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) (a : ℝ) :
    (∫ x, (f x-a)^2 ∂μ) = variance f μ + ((∫ x, f x ∂μ)-a)^2 := by
  have hi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have heq : (fun x => (f x-a)^2) = (fun x => f x^2-2*a*f x+a^2) := by funext x; ring
  rw [heq]
  have hs : Integrable (fun x => f x^2-2*a*f x) μ := hf.integrable_sq.sub (hi.const_mul (2*a))
  rw [integral_add hs (integrable_const _), integral_sub hf.integrable_sq (hi.const_mul (2*a)),
    integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul, variance_eq_sub hf]
  simp only [Pi.pow_apply]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def rootAverage (F : (n : ℕ) → RootPath Ω n → ℝ) (n : ℕ) : ℝ :=
  ∫ x, F n x ∂rootLaw n (fun _ => μ)

/-- Actual random-count root means inherit the addition/deletion constant. -/
theorem rootAverage_step {F : (n : ℕ) → RootPath Ω n → ℝ} {B : ℕ → ℝ} {D : ℝ}
    (hF : ∀ n, Measurable (F n)) (hB : ∀ n x, |F n x| ≤ B n)
    (hadd : ∀ n x y, |F (n+1) (x,y) - F n y| ≤ D) (n : ℕ) :
    |rootAverage μ F (n+1)-rootAverage μ F n| ≤ D := by
  let ν := rootLaw n (fun _ : Fin n => μ)
  have hp : Integrable (F (n+1)) (μ.prod ν) :=
    (bounded_memLp (hF (n+1)) (hB (n+1)) 1).integrable le_rfl
  have hi : Integrable (F n) ν := (bounded_memLp (hF n) (hB n) 1).integrable le_rfl
  have hs (x : Ω) : Integrable (fun y => F (n+1) (x,y)) ν :=
    (bounded_memLp ((hF (n+1)).comp (measurable_const.prodMk measurable_id))
      (fun y => hB (n+1) (x,y)) 1).integrable le_rfl
  change |(∫ z, F (n+1) z ∂μ.prod ν) - ∫ y, F n y ∂ν| ≤ D
  rw [integral_prod _ hp]
  have hc : (∫ _ : Ω, (∫ y, F n y ∂ν) ∂μ) = ∫ y, F n y ∂ν := by simp
  rw [← hc, ← integral_sub hp.integral_prod_left (integrable_const _)]
  apply abs_integral_le_bound
  intro x
  rw [← integral_sub (hs x) hi]
  exact abs_integral_le_bound (hadd n x)

 
theorem poisson_random_root_variance (r : ℝ≥0)
    {F : (n : ℕ) → RootPath Ω n → ℝ} {B : ℕ → ℝ} {C D : ℝ}
    (hF : ∀ n, Measurable (F n)) (hB : ∀ n x, |F n x| ≤ B n)
    (hD : 0 ≤ D)
    (hrep : ∀ n (i : Fin n) x y, |F n x-F n (replaceRoot n x i y)| ≤ C)
    (hadd : ∀ n x y, |F (n+1) (x,y)-F n y| ≤ D) :
    (∫ n : ℕ, ∫ x, (F n x-(∫ k, rootAverage μ F k ∂poissonMeasure r))^2
        ∂rootLaw n (fun _ => μ) ∂poissonMeasure r) ≤
      (C^2/2+D^2)*(r : ℝ) := by
  have hvar (n : ℕ) : variance (F n) (rootLaw n (fun _ => μ)) ≤ C^2/2*(n : ℝ) := by
    have h := root_variance_bound n (fun _ => μ) (hF n) (hB n) (fun _ => C) (hrep n)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using h
  have hvint : Integrable (fun n => variance (F n) (rootLaw n (fun _ => μ))) (poissonMeasure r) := by
    apply poisson_integrable_linear r (A := 0) (B := C^2/2)
    intro n
    rw [abs_of_nonneg (variance_nonneg _ _), zero_add]
    exact hvar n
  have hcount := poisson_variance_lipschitz r hD
    (nat_lipschitz_of_step hD (rootAverage_step μ hF hB hadd))
  have hmeanLp := poisson_memLp_lipschitz r hD
    (nat_lipschitz_of_step hD (rootAverage_step μ hF hB hadd))
  have hmb : Integrable (fun n => (rootAverage μ F n-(∫ k, rootAverage μ F k ∂poissonMeasure r))^2)
      (poissonMeasure r) := (hmeanLp.sub (memLp_const _)).integrable_sq
  simp_rw [integral_sq_sub_center (bounded_memLp (hF _) (hB _) 2)]
  change (∫ n, variance (F n) (rootLaw n (fun _ => μ)) +
    (rootAverage μ F n-(∫ k, rootAverage μ F k ∂poissonMeasure r))^2 ∂poissonMeasure r) ≤ _
  rw [integral_add hvint hmb, ← variance_eq_integral (Measurable.of_discrete (f := rootAverage μ F)).aemeasurable]
  have hi := integral_mono hvint ((poisson_integrable_count r).const_mul (C^2/2)) hvar
  rw [integral_const_mul, poisson_mean] at hi
  nlinarith

end DilutedSpinGlass

end

end OAI
