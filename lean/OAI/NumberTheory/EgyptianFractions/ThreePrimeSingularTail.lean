import OAI.NumberTheory.EgyptianFractions.ThreePrimeEulerTail
import OAI.NumberTheory.EgyptianFractions.ThreePrimeSingularSeries

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

private lemma shifted_reciprocal_square_tail (P : Finset ℕ) (N : ℕ)
    (hP : ∀ n ∈ P, N ≤ n) :
    (∑ n ∈ P, 1 / ((n : ℝ) + 2) ^ 2) ≤ 1 / ((N : ℝ) + 1) := by
  have htail := ThreePrimeEulerTail.reciprocal_square_tail
    (P.image (fun n => n + 3)) (N + 2) (by omega) (by
      intro p hp
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
      have := hP n hn
      omega)
  rw [Finset.sum_image (by intro a ha b hb hab; dsimp at hab; omega)] at htail
  convert htail using 1
  · apply Finset.sum_congr rfl
    intro n hn
    push_cast
    ring
  · push_cast
    ring

/-- Every finite tail of the canonical ternary singular series has relative
error at most `2 / (N + 1)`, uniformly in the integer being represented. -/
theorem threePrimeOddFactors_tail_abs_sub_one (u N : ℕ) (P : Finset ℕ)
    (hP : ∀ n ∈ P, N ≤ n) :
    |(∏ n ∈ P, (1 + threePrimeOddPerturbation u n)) - 1| ≤
      2 / ((N : ℝ) + 1) := by
  have hsum : (∑ n ∈ P, ‖threePrimeOddPerturbation u n‖) ≤
      1 / ((N : ℝ) + 1) :=
    (Finset.sum_le_sum (fun n _ => threePrimeOddPerturbation_norm_le u n)).trans
      (shifted_reciprocal_square_tail P N hP)
  have hsmall : |1 / ((N : ℝ) + 1)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hprod := P.norm_prod_one_add_sub_one_le (threePrimeOddPerturbation u)
  rw [Real.norm_eq_abs] at hprod
  calc
    _ ≤ Real.exp (∑ n ∈ P, ‖threePrimeOddPerturbation u n‖) - 1 := hprod
    _ ≤ Real.exp (1 / ((N : ℝ) + 1)) - 1 :=
      sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1
    _ ≤ |Real.exp (1 / ((N : ℝ) + 1)) - 1| := le_abs_self _
    _ ≤ 2 * |1 / ((N : ℝ) + 1)| := Real.abs_exp_sub_one_le hsmall
    _ = 2 / ((N : ℝ) + 1) := by rw [abs_of_nonneg (by positivity)]; ring

/-- Uniform boundedness of the finite odd-prime factors. -/
theorem threePrimeOddFactors_partial_abs_le (u N : ℕ) :
    |∏ n ∈ Finset.range N, (1 + threePrimeOddPerturbation u n)| ≤ 3 := by
  have htail := threePrimeOddFactors_tail_abs_sub_one u 0 (Finset.range N)
    (by intros; omega)
  norm_num only [Nat.cast_zero, zero_add, div_one] at htail
  calc
    _ = |((∏ n ∈ Finset.range N, (1 + threePrimeOddPerturbation u n)) - 1) + 1| := by ring_nf
    _ ≤ |(∏ n ∈ Finset.range N, (1 + threePrimeOddPerturbation u n)) - 1| + |(1 : ℝ)| :=
      abs_add_le _ _
    _ ≤ 3 := by norm_num at htail ⊢; linarith

/-- The canonical infinite odd-prime product is uniformly approximated by its
first `N` factors at the explicit rate `6 / (N + 1)`. -/
theorem threePrimeOddFactors_tprod_sub_partial (u N : ℕ) :
    |(∏' n : ℕ, (1 + threePrimeOddPerturbation u n)) -
      ∏ n ∈ Finset.range N, (1 + threePrimeOddPerturbation u n)| ≤
      6 / ((N : ℝ) + 1) := by
  apply le_of_tendsto (((threePrimeOddFactors_multipliable u).hasProd.tendsto_prod_nat.sub_const
    (∏ n ∈ Finset.range N, (1 + threePrimeOddPerturbation u n))).abs)
  filter_upwards [eventually_ge_atTop N] with M hNM
  rw [← Finset.prod_range_mul_prod_Ico (fun n => 1 + threePrimeOddPerturbation u n) hNM]
  have heq : (∏ n ∈ Finset.range N, (1 + threePrimeOddPerturbation u n)) *
      (∏ n ∈ Finset.Ico N M, (1 + threePrimeOddPerturbation u n)) -
      (∏ n ∈ Finset.range N, (1 + threePrimeOddPerturbation u n)) =
      (∏ n ∈ Finset.range N, (1 + threePrimeOddPerturbation u n)) *
        ((∏ n ∈ Finset.Ico N M, (1 + threePrimeOddPerturbation u n)) - 1) := by ring
  rw [heq, abs_mul]
  calc
    _ ≤ 3 * (2 / ((N : ℝ) + 1)) := by
      apply mul_le_mul (threePrimeOddFactors_partial_abs_le u N)
        (threePrimeOddFactors_tail_abs_sub_one u N (Finset.Ico N M)
          (by intro n hn; exact (Finset.mem_Ico.mp hn).1)) (abs_nonneg _) (by norm_num)
    _ = 6 / ((N : ℝ) + 1) := by ring

/-- The finite canonical singular product, including the factor at two. -/
def threePrimeSingularPartial (u N : ℕ) : ℝ :=
  (if Odd u then 2 else 0) *
    ∏ n ∈ Finset.range N, (1 + threePrimeOddPerturbation u n)

/-- Uniform quantitative truncation of the actual defined singular series. -/
theorem threePrimeSingularSeries_sub_partial (u N : ℕ) :
    |threePrimeSingularSeries u - threePrimeSingularPartial u N| ≤
      12 / ((N : ℝ) + 1) := by
  unfold threePrimeSingularSeries threePrimeSingularPartial
  rw [← mul_sub, abs_mul]
  have hfactor : |(if Odd u then 2 else 0 : ℝ)| ≤ 2 := by split_ifs <;> norm_num
  calc
    _ ≤ 2 * (6 / ((N : ℝ) + 1)) :=
      mul_le_mul hfactor (threePrimeOddFactors_tprod_sub_partial u N) (abs_nonneg _) (by norm_num)
    _ = 12 / ((N : ℝ) + 1) := by ring

/-- Uniform convergence in the represented integer: the onset is independent
of `u`, including even inputs where the singular series vanishes. -/
theorem threePrimeSingularPartial_tendstoUniformly :
    TendstoUniformly (fun N u => threePrimeSingularPartial u N)
      threePrimeSingularSeries atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (12 / ε)
  filter_upwards [eventually_ge_atTop N₀] with N hN
  intro u
  rw [Real.dist_eq]
  apply (threePrimeSingularSeries_sub_partial u N).trans_lt
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < N + 1)).mpr
  have hNreal : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
  have hbound := (div_lt_iff₀ hε).mp hN₀
  nlinarith

/-- A simultaneous absolute bound for all singular series, useful when
converting an additive asymptotic error into a relative error. -/
theorem threePrimeSingularSeries_abs_le_six (u : ℕ) :
    |threePrimeSingularSeries u| ≤ 6 := by
  have hodd : |∏' n : ℕ, (1 + threePrimeOddPerturbation u n)| ≤ 3 :=
    le_of_tendsto' (threePrimeOddFactors_multipliable u).hasProd.tendsto_prod_nat.abs
      (threePrimeOddFactors_partial_abs_le u)
  unfold threePrimeSingularSeries
  rw [abs_mul]
  have hfactor : |(if Odd u then 2 else 0 : ℝ)| ≤ 2 := by split_ifs <;> norm_num
  nlinarith [abs_nonneg (∏' n : ℕ, (1 + threePrimeOddPerturbation u n))]

/-- A cutoff tending to infinity may depend on the represented integer or on
any other parameter; uniform truncation still makes the error tend to zero. -/
theorem threePrimeSingularPartial_sub_tendsto_zero {α : Type*} {l : Filter α}
    (u Q : α → ℕ) (hQ : Tendsto Q l atTop) :
    Tendsto (fun x => threePrimeSingularSeries (u x) -
      threePrimeSingularPartial (u x) (Q x)) l (nhds 0) := by
  apply squeeze_zero_norm (fun x => by
    simpa only [Real.norm_eq_abs] using threePrimeSingularSeries_sub_partial (u x) (Q x))
  apply tendsto_const_nhds.div_atTop
  apply tendsto_atTop_mono (fun x => ?_) (tendsto_natCast_atTop_atTop.comp hQ)
  exact le_add_of_nonneg_right zero_le_one

/-- Truncating the singular series changes any weighted main term by little-o
of that same weight. No positivity or nonvanishing of the weight is needed. -/
theorem threePrimeSingularPartial_weighted_isLittleO {α : Type*} {l : Filter α}
    (u Q : α → ℕ) (hQ : Tendsto Q l atTop) (w : α → ℝ) :
    (fun x => (threePrimeSingularSeries (u x) -
      threePrimeSingularPartial (u x) (Q x)) * w x) =o[l] w := by
  have hsmall : (fun x => threePrimeSingularSeries (u x) -
      threePrimeSingularPartial (u x) (Q x)) =o[l] (fun _ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr (threePrimeSingularPartial_sub_tendsto_zero u Q hQ)
  simpa only [one_mul] using hsmall.mul_isBigO (Asymptotics.isBigO_refl w l)

/-- An asymptotic formula with a growing finite singular product is equivalent
to the formula with the canonical infinite series. This supplies the uniform
Euler-tail transfer in a major-arc computation without asserting that formula. -/
theorem threePrimeSingularPartial_asymptotic_iff {α : Type*} {l : Filter α}
    (u Q : α → ℕ) (hQ : Tendsto Q l atTop) (a w : α → ℝ) :
    ((fun x => a x - threePrimeSingularSeries (u x) * w x) =o[l] w) ↔
      ((fun x => a x - threePrimeSingularPartial (u x) (Q x) * w x) =o[l] w) := by
  have htail := threePrimeSingularPartial_weighted_isLittleO u Q hQ w
  constructor
  · intro h
    exact (h.add htail).congr_left (fun x => by ring)
  · intro h
    exact (h.sub htail).congr_left (fun x => by ring)

end Problem337

end

end OAI
