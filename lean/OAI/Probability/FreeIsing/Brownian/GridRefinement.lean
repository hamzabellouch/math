import OAI.Probability.FreeIsing.Brownian.SimpleIntegral

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.BrownianGrid

def integralSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0)
    (H : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, H i ω * (B (t (i + 1)) ω - B (t i) ω)

lemma sum_range_blocks {E : Type*} [AddCommMonoid E] (f : ℕ → E) (n k : ℕ) :
    ∑ i ∈ Finset.range (n * k), f i =
      ∑ j ∈ Finset.range n, ∑ l ∈ Finset.range k, f (j * k + l) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma weighted_sum_refinement (x H : ℕ → ℝ) (n : ℕ) {k : ℕ} (hk : 0 < k) :
    (∑ j ∈ Finset.range n, H j * (x ((j + 1) * k) - x (j * k))) =
      ∑ i ∈ Finset.range (n * k), H (i / k) * (x (i + 1) - x i) := by
  rw [sum_range_blocks]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    H j * (x ((j + 1) * k) - x (j * k)) =
        H j * (∑ l ∈ Finset.range k, (x (j * k + (l + 1)) - x (j * k + l))) := by
      rw [Finset.sum_range_sub (fun l => x (j * k + l)) k]
      simp [Nat.add_mul]
    _ = ∑ l ∈ Finset.range k, H j * (x (j * k + (l + 1)) - x (j * k + l)) :=
      Finset.mul_sum _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      have hdiv : (j * k + l) / k = j := by
        rw [Nat.mul_comm j k, Nat.mul_add_div hk, Nat.div_eq_of_lt (Finset.mem_range.mp hl)]
        omega
      rw [hdiv]
      congr 3

theorem integralSum_refinement {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ) (n : ℕ) {k : ℕ} (hk : 0 < k) :
    integralSum B (fun j => t (j * k)) H n =
      integralSum B t (fun i => H (i / k)) (n * k) := by
  funext ω
  exact weighted_sum_refinement (fun i => B (t i) ω) (fun i => H i ω) n hk

lemma integralSum_sub {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0)
    (H K : ℕ → Ω → ℝ) (n : ℕ) :
    integralSum B t (fun i ω => H i ω - K i ω) n =
      fun ω => integralSum B t H n ω - integralSum B t K n ω := by
  funext ω
  simp only [integralSum, sub_mul, Finset.sum_sub_distrib]

theorem stronglyMeasurable_refined {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hm : ∀ t, StronglyMeasurable (B t))
    {t : ℕ → ℝ≥0} (ht : Monotone t) {H : ℕ → Ω → ℝ} {k : ℕ}
    (hH : ∀ j, StronglyMeasurable[Filtration.natural B hm (t (j * k))] (H j))
    (i : ℕ) : StronglyMeasurable[Filtration.natural B hm (t i)] (H (i / k)) :=
  (hH (i / k)).mono ((Filtration.natural B hm).mono (ht (Nat.div_mul_le_self i k)))

theorem preBrownian_difference_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H K : ℕ → Ω → ℝ)
    {k : ℕ} (hk : 0 < k)
    (hH : ∀ j, StronglyMeasurable[Filtration.natural B hm (t (j * k))] (H j))
    (hK : ∀ i, StronglyMeasurable[Filtration.natural B hm (t i)] (K i))
    (hH2 : ∀ j, MemLp (H j) 2 P) (hK2 : ∀ i, MemLp (K i) 2 P) (n : ℕ) :
    (∫ ω, (integralSum B (fun j => t (j * k)) H n ω -
      integralSum B t K (n * k) ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range (n * k), ((t (i + 1) : ℝ) - (t i : ℝ)) *
        ∫ ω, (H (i / k) ω - K i ω) ^ 2 ∂P := by
  rw [integralSum_refinement B t H n hk]
  simpa only [integralSum, sub_mul, Finset.sum_sub_distrib] using
    preBrownian_predictable_sum_isometry hB hm t ht
    (fun i ω => H (i / k) ω - K i ω)
    (fun i => (stronglyMeasurable_refined hm ht hH i).sub (hK i))
    (fun i => (hH2 (i / k)).sub (hK2 i)) (Finset.range (n * k))

theorem preBrownian_difference_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H K : ℕ → Ω → ℝ)
    {k : ℕ} (hk : 0 < k)
    (hH : ∀ j, StronglyMeasurable[Filtration.natural B hm (t (j * k))] (H j))
    (hK : ∀ i, StronglyMeasurable[Filtration.natural B hm (t i)] (K i))
    (hH2 : ∀ j, MemLp (H j) 2 P) (hK2 : ∀ i, MemLp (K i) 2 P)
    (n : ℕ) {ε : ℝ}
    (happrox : ∀ i < n * k, (∫ ω, (H (i / k) ω - K i ω) ^ 2 ∂P) ≤ ε) :
    (∫ ω, (integralSum B (fun j => t (j * k)) H n ω -
      integralSum B t K (n * k) ω) ^ 2 ∂P) ≤
      ((t (n * k) : ℝ) - (t 0 : ℝ)) * ε := by
  rw [preBrownian_difference_isometry hB hm t ht H K hk hH hK hH2 hK2 n]
  calc
    _ ≤ ∑ i ∈ Finset.range (n * k), ((t (i + 1) : ℝ) - (t i : ℝ)) * ε := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left (happrox i (Finset.mem_range.mp hi))
      exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr (ht (Nat.le_succ i)))
    _ = _ := by rw [← Finset.sum_mul, Finset.sum_range_sub (fun i => (t i : ℝ)) (n * k)]

end Problem367.BrownianGrid

end

end OAI
