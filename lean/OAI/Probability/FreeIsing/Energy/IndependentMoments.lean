import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem integrable_prod_comp_of_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : iIndepFun X μ)
    (hmX : ∀ i, Measurable (X i))
    (f : ι → ℝ → ℝ) (hmf : ∀ i, Measurable (f i))
    (hf : ∀ i, Integrable (fun ω => f i (X i ω)) μ) :
    Integrable (fun ω => ∏ i, f i (X i ω)) μ := by
  have hfi : ∀ i, Integrable (f i) (μ.map (X i)) := by
    intro i
    exact (integrable_map_measure (hmf i).aestronglyMeasurable (hmX i).aemeasurable).mpr (hf i)
  have hi := Integrable.fintype_prod hfi
  have hmap := hX.map_fun_eq_pi_map (fun i => (hmX i).aemeasurable)
  have hm : Measurable (fun x : ι → ℝ => ∏ i, f i (x i)) := by
    exact Finset.measurable_prod _ (fun i _ => (hmf i).comp (measurable_pi_apply i))
  have hmarray : Measurable (fun ω i => X i ω) := Measurable.of_eval hmX
  have hi' : Integrable (fun x : ι → ℝ => ∏ i, f i (x i))
      (μ.map (fun ω i => X i ω)) := by rw [hmap]; exact hi
  exact (integrable_map_measure hm.aestronglyMeasurable hmarray.aemeasurable).mp hi'

theorem integrable_sum_pow_of_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : iIndepFun X μ)
    (hmX : ∀ i, Measurable (X i)) (p : ℕ)
    (hMom : ∀ i k, k ≤ p → Integrable (fun ω => X i ω ^ k) μ) :
    Integrable (fun ω => (∑ i, X i ω) ^ p) μ := by
  classical
  simp_rw [Finset.sum_pow_eq_sum_piAntidiag]
  apply integrable_finsetSum
  intro r hr
  apply Integrable.const_mul
  apply integrable_prod_comp_of_iIndepFun hX hmX (fun i x => x ^ r i)
    (fun i => measurable_id.pow_const (r i))
  intro i
  apply hMom
  have hrsum := (Finset.mem_piAntidiag.mp hr).1
  have hri := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => Nat.zero_le (r j))
    (Finset.mem_univ i)
  simpa [hrsum] using hri

theorem integral_sum_pow_of_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : iIndepFun X μ)
    (hmX : ∀ i, Measurable (X i)) (p : ℕ)
    (hMom : ∀ i k, k ≤ p → Integrable (fun ω => X i ω ^ k) μ) :
    (∫ ω, (∑ i, X i ω) ^ p ∂μ) =
      ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) p,
        (Nat.multinomial Finset.univ r : ℝ) * ∏ i, ∫ ω, X i ω ^ r i ∂μ := by
  classical
  have hprod : ∀ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) p,
      Integrable (fun ω => ∏ i, X i ω ^ r i) μ := by
    intro r hr
    apply integrable_prod_comp_of_iIndepFun hX hmX (fun i x => x ^ r i)
      (fun i => measurable_id.pow_const (r i))
    intro i
    apply hMom
    have hrsum := (Finset.mem_piAntidiag.mp hr).1
    have hri := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => Nat.zero_le (r j))
      (Finset.mem_univ i)
    simpa [hrsum] using hri
  simp_rw [Finset.sum_pow_eq_sum_piAntidiag]
  rw [integral_finsetSum _ (fun r hr => (hprod r hr).const_mul _)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [integral_const_mul]
  congr 1
  exact hX.integral_fun_prod_comp (fun i => (hmX i).aemeasurable)
    (fun i => (measurable_id.pow_const (r i)).aestronglyMeasurable)

theorem integral_abs_sum_pow_le_of_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : iIndepFun X μ)
    (hmX : ∀ i, Measurable (X i)) (p : ℕ)
    (hMom : ∀ i k, k ≤ p → Integrable (fun ω => |X i ω| ^ k) μ) :
    (∫ ω, |∑ i, X i ω| ^ p ∂μ) ≤
      ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) p,
        (Nat.multinomial Finset.univ r : ℝ) * ∏ i, ∫ ω, |X i ω| ^ r i ∂μ := by
  have hAbs : iIndepFun (fun i ω => |X i ω|) μ :=
    hX.comp (fun _ x => |x|) (fun _ => measurable_abs)
  have hi := integrable_sum_pow_of_iIndepFun hAbs (fun i => (hmX i).abs) p hMom
  calc
    (∫ ω, |∑ i, X i ω| ^ p ∂μ) ≤ (∫ ω, (∑ i, |X i ω|) ^ p ∂μ) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg _) _)) hi
      exact Filter.Eventually.of_forall fun ω =>
        pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) p
    _ = _ := integral_sum_pow_of_iIndepFun hAbs (fun i => (hmX i).abs) p hMom

theorem piAntidiag_pure_filter_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} :
    (Finset.piAntidiag (Finset.univ : Finset ι) p).filter
        (fun r => ∃ i, r i = p) =
      Finset.univ.image (fun i : ι => Pi.single i p) := by
  classical
  ext r
  constructor
  · intro hr
    obtain ⟨hr, i, hi⟩ := Finset.mem_filter.mp hr
    have hsum := (Finset.mem_piAntidiag.mp hr).1
    have hrest : ∑ j ∈ Finset.univ.erase i, r j = 0 := by
      have hh := Finset.sum_erase_add Finset.univ r (Finset.mem_univ i)
      rw [hi, hsum] at hh
      omega
    have heq : r = Pi.single i p := by
      funext j
      by_cases hji : j = i
      · subst j; simpa only [Pi.single_eq_same] using hi
      · have hj := Finset.sum_eq_zero_iff.mp hrest j
          (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
        simpa [Pi.single_apply, hji] using hj
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩
  · intro hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_piAntidiag.mpr
      constructor
      · simp [Finset.sum_pi_single']
      · intro j _; exact Finset.mem_univ j
    · exact ⟨i, by simp⟩

theorem multinomial_sum_eq_pure_add_mixed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ℕ → ℝ) (hzero : ∀ i, M i 0 = 1)
    {p : ℕ} (hp : 0 < p) :
    (∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) p,
      (Nat.multinomial Finset.univ r : ℝ) * ∏ i, M i (r i)) =
      (∑ i, M i p) +
        ∑ r ∈ (Finset.piAntidiag (Finset.univ : Finset ι) p).filter
          (fun r => ¬ ∃ i, r i = p),
          (Nat.multinomial Finset.univ r : ℝ) * ∏ i, M i (r i) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun r : ι → ℕ => ∃ i, r i = p)]
  congr 1
  rw [piAntidiag_pure_filter_eq]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Nat.multinomial_single]
    simp only [Nat.cast_one, one_mul]
    rw [Finset.prod_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j _ hji
      simpa [Pi.single_apply, hji] using hzero j
    · simp
  · intro i _ j _ hij
    by_contra hne
    have hh := congrFun hij i
    simp only [Pi.single_eq_same, Pi.single_apply, ite_eq_right hne] at hh
    omega

end Problem367

end OAI
