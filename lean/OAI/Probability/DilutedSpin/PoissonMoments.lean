import OAI.Probability.DilutedSpin.TreeDerivatives

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

/-- A bounded measurable score belongs to every finite Lp space. -/
theorem bounded_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hB : ∀ x, |f x| ≤ B) (p : ℝ≥0∞) : MemLp f p μ := by
  apply MemLp.of_bound hf.aestronglyMeasurable B
  exact ae_of_all _ (fun point => by simpa only [Real.norm_eq_abs] using hB point)

/-- The exact two-independent-copy identity for variance. -/
theorem variance_two_copies {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, ∫ y, (f x-f y)^2 ∂μ ∂μ) = 2 * variance f μ := by
  have hi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hs := hf.integrable_sq
  have hin (x : Ω) : (∫ y, (f x-f y)^2 ∂μ) =
      (f x)^2 - 2*f x*(∫ y, f y ∂μ) + ∫ y, (f y)^2 ∂μ := by
    have heq : (fun y => (f x-f y)^2) =
        (fun y => (f x)^2 - 2*f x*f y + (f y)^2) := by
      funext y; ring
    rw [heq]
    have hsub : Integrable (fun y => (f x)^2 - 2*f x*f y) μ :=
      (integrable_const _).sub (hi.const_mul (2*f x))
    rw [integral_add hsub hs,
      integral_sub (integrable_const ((f x)^2)) (hi.const_mul (2*f x)),
      integral_const_mul]
    simp
  simp_rw [hin]
  have hmul : Integrable (fun x => 2*f x*(∫ y, f y ∂μ)) μ :=
    (hi.const_mul 2).mul_const _
  have hsub : Integrable (fun x => (f x)^2 - 2*f x*(∫ y, f y ∂μ)) μ := hs.sub hmul
  rw [integral_add hsub (integrable_const (∫ y, (f y)^2 ∂μ))]
  rw [integral_sub hs hmul, variance_eq_sub hf]
  simp only [Pi.pow_apply]
  rw [show (fun x => 2*f x*(∫ y, f y ∂μ)) =
    (fun x => f x*(2*(∫ y, f y ∂μ))) by funext x; ring]
  rw [integral_mul_const]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- Pairwise oscillation controls root variance without choosing a center. -/
theorem variance_le_oscillation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {C : ℝ} (hf : MemLp f 2 μ)
    (hC : ∀ x y, |f x-f y| ≤ C) : variance f μ ≤ C^2/2 := by
  have hp : ∀ x y, (f x-f y)^2 ≤ C^2 := by
    intro x y
    have h := hC x y
    nlinarith [sq_nonneg (C - |f x-f y|), sq_abs (f x-f y), abs_nonneg (f x-f y)]
  have hb : ∀ x, (∫ y, (f x-f y)^2 ∂μ) ≤ C^2 := by
    intro x
    have hsub : MemLp (fun y => f x - f y) 2 μ := (memLp_const (f x)).sub hf
    simpa using integral_mono hsub.integrable_sq (integrable_const (C^2)) (hp x)
  have hint : Integrable (fun x => ∫ y, (f x-f y)^2 ∂μ) μ := by
    have hprod : MemLp (fun z : Ω × Ω => f z.1 - f z.2) 2 (μ.prod μ) :=
      (hf.comp_fst μ).sub (hf.comp_snd μ)
    exact hprod.integrable_sq.integral_prod_left
  have h := integral_mono hint (integrable_const (C^2)) hb
  rw [variance_two_copies hf] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  linarith

end DilutedSpinGlass

namespace DilutedSpinGlass

variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Uniform bounds survive averaging a physical root coordinate. -/
theorem abs_integral_le_bound {f : Ω → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂μ| ≤ B := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const
    (μ := μ) (f := f) (C := B) (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hB x))

/-- Total variance for a bounded measurable function of two independent root blocks. -/
theorem variance_prod_decomposition {f : Ω × Λ → ℝ} {B : ℝ}
    (hf : Measurable f) (hB : ∀ x, |f x| ≤ B) :
    variance f (μ.prod ν) =
      (∫ x, variance (fun y => f (x,y)) ν ∂μ) +
        variance (fun x => ∫ y, f (x,y) ∂ν) μ := by
  have hLp := bounded_memLp (μ := μ.prod ν) hf hB 2
  have hLp' (x : Ω) : MemLp (fun y => f (x,y)) 2 ν :=
    bounded_memLp (hf.comp (measurable_const.prodMk measurable_id)) (fun y => hB (x,y)) 2
  have hm : Measurable (fun x => ∫ y, f (x,y) ∂ν) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hmLp : MemLp (fun x => ∫ y, f (x,y) ∂ν) 2 μ :=
    bounded_memLp hm (fun x => abs_integral_le_bound (fun y => hB (x,y))) 2
  have hint : Integrable f (μ.prod ν) := hLp.integrable (by norm_num)
  rw [variance_eq_sub hLp, variance_eq_sub hmLp]
  simp_rw [variance_eq_sub (hLp' _)]
  simp only [Pi.pow_apply]
  rw [integral_sub hLp.integrable_sq.integral_prod_left hmLp.integrable_sq,
    integral_prod _ hint, integral_prod _ hLp.integrable_sq]
  ring

/-- An independent block average preserves each bounded-difference constant. -/
theorem integral_oscillation {f : Ω × Λ → ℝ} {B C : ℝ}
    (hf : Measurable f) (hB : ∀ z, |f z| ≤ B)
    (hC : ∀ x x' y, |f (x,y)-f (x',y)| ≤ C) :
    ∀ x x', |(∫ y, f (x,y) ∂ν) - (∫ y, f (x',y) ∂ν)| ≤ C := by
  intro x x'
  have hi (z : Ω) : Integrable (fun y => f (z,y)) ν :=
    (bounded_memLp (hf.comp (measurable_const.prodMk measurable_id))
      (fun y => hB (z,y)) 1).integrable le_rfl
  rw [← integral_sub (hi x) (hi x')]
  exact abs_integral_le_bound (hC x x')

end DilutedSpinGlass

namespace DilutedSpinGlass

universe u

/-- A finite independent block sequence, with no finiteness assumption on a block. -/
abbrev RootPath (Ω : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => Ω × RootPath Ω n

@[reducible] instance rootPathMeasurable (Ω : Type*) [MeasurableSpace Ω] :
    (n : ℕ) → MeasurableSpace (RootPath Ω n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n+1 => by
    letI := rootPathMeasurable Ω n
    exact inferInstanceAs (MeasurableSpace (Ω × RootPath Ω n))

noncomputable def rootLaw {Ω : Type*} [MeasurableSpace Ω] :
    (n : ℕ) → (Fin n → Measure Ω) → Measure (RootPath Ω n)
  | 0, _ => Measure.dirac PUnit.unit
  | n+1, μ => (μ 0).prod (rootLaw n (fun i => μ i.succ))

instance rootLawProbability {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (μ : Fin n → Measure Ω) [hμ : ∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (rootLaw n μ) := by
  induction n with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ n ih =>
    have : ∀ i : Fin n, IsProbabilityMeasure (μ i.succ) := fun i => hμ i.succ
    have := ih (fun i => μ i.succ)
    change IsProbabilityMeasure ((μ 0).prod (rootLaw n (fun i => μ i.succ)))
    infer_instance

def replaceRoot {Ω : Type*} : (n : ℕ) → RootPath Ω n → Fin n → Ω → RootPath Ω n
  | 0, x, _, _ => x
  | n+1, x, i, y => Fin.cases (y,x.2) (fun j => (x.1,replaceRoot n x.2 j y)) i

/-- Bounded coordinate replacements give a variance bound additive in the
number of independent root coordinates, not quadratic in that number. -/
theorem root_variance_bound {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (μ : Fin n → Measure Ω) [hμ : ∀ i, IsProbabilityMeasure (μ i)]
    {F : RootPath Ω n → ℝ} {B : ℝ} (hF : Measurable F) (hB : ∀ x, |F x| ≤ B)
    (C : Fin n → ℝ)
    (hC : ∀ (i : Fin n) x y, |F x-F (replaceRoot n x i y)| ≤ C i) :
    variance F (rootLaw n μ) ≤ ∑ i, (C i)^2/2 := by
  induction n with
  | zero =>
    rw [variance_eq_integral hF.aemeasurable]
    simp [rootLaw]
  | succ n ih =>
    let ν := rootLaw n (fun i => μ i.succ)
    have : ∀ i : Fin n, IsProbabilityMeasure (μ i.succ) := fun i => hμ i.succ
    have ht (x : Ω) : variance (fun y => F (x,y)) ν ≤ ∑ i : Fin n, (C i.succ)^2/2 := by
      apply ih (fun i => μ i.succ)
        (hF.comp (measurable_const.prodMk measurable_id)) (fun y => hB (x,y))
        (fun i => C i.succ)
      intro i y z
      simpa [replaceRoot, Function.comp_def] using hC i.succ (x,y) z
    have hm : Measurable (fun x => ∫ y, F (x,y) ∂ν) :=
      hF.stronglyMeasurable.integral_prod_right'.measurable
    have hmLp : MemLp (fun x => ∫ y, F (x,y) ∂ν) 2 (μ 0) :=
      bounded_memLp hm (fun x => abs_integral_le_bound (fun y => hB (x,y))) 2
    have hosc : ∀ x x', |(∫ y, F (x,y) ∂ν)-(∫ y, F (x',y) ∂ν)| ≤ C 0 := by
      apply integral_oscillation hF hB
      intro x x' y
      simpa [replaceRoot] using hC 0 (x,y) x'
    have hroot := variance_le_oscillation hmLp hosc
    have hLp := bounded_memLp (μ := (μ 0).prod ν) hF hB 2
    have hs (x : Ω) : MemLp (fun y => F (x,y)) 2 ν :=
      bounded_memLp (hF.comp (measurable_const.prodMk measurable_id)) (fun y => hB (x,y)) 2
    have hint : Integrable (fun x => variance (fun y => F (x,y)) ν) (μ 0) := by
      simp_rw [variance_eq_sub (hs _)]
      exact hLp.integrable_sq.integral_prod_left.sub hmLp.integrable_sq
    have hintBound := integral_mono hint (integrable_const (∑ i : Fin n, (C i.succ)^2/2)) ht
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hintBound
    change variance F ((μ 0).prod ν) ≤ _
    rw [variance_prod_decomposition hF hB, Fin.sum_univ_succ]
    linarith

end DilutedSpinGlass

end

end OAI
