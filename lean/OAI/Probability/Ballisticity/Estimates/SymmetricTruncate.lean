import Mathlib
import OAI.Probability.Ballisticity.Estimates.CommonWordIncrement

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma abs_supporting (t x : ℝ) : absSlope t*x ≤ |t+x|-|t| := by
  by_cases ht : 0 ≤ t
  · rw [absSlope,ite_eq_left ht,one_mul,abs_of_nonneg ht]
    linarith [le_abs_self (t+x)]
  · rw [absSlope,ite_eq_right ht,neg_one_mul,abs_of_neg (lt_of_not_ge ht)]
    linarith [neg_le_abs (t+x)]

lemma max_square_increment {m a : ℝ} : (max m |a|)^2-m^2 ≤ 2*|a| * (max m |a|-m) := by
  by_cases h : |a| ≤ m
  · rw [max_eq_left h]; ring_nf; rfl
  · rw [max_eq_right (le_of_not_ge h)]
    nlinarith [sq_nonneg (|a|-m)]

lemma partialSumMax_pathwise (X : ℕ → ℝ) (n : ℕ) :
    (partialSumMax X n)^2 ≤ 2*partialSumMax X n*|realPartialSum X n|-
      2*∑ k ∈ Finset.range n, partialSumMax X k*absSlope (realPartialSum X k)*X k := by
  induction n with
  | zero => simp [partialSumMax]
  | succ n ih =>
    have hincr := max_square_increment (m := partialSumMax X n) (a := realPartialSum X (n+1))
    have hs := mul_le_mul_of_nonneg_left (abs_supporting (realPartialSum X n) (X n))
      (partialSumMax_nonneg X n)
    rw [← realPartialSum_succ] at hs
    rw [Finset.sum_range_succ]
    change (max (partialSumMax X n) |realPartialSum X (n+1)|)^2 ≤ _
    change _ ≤ 2*max (partialSumMax X n) |realPartialSum X (n+1)| * |realPartialSum X (n+1)|-_
    nlinarith

lemma partialSumMax_square_pathwise (X : ℕ → ℝ) (n : ℕ) :
    (partialSumMax X n)^2 ≤ 4*(realPartialSum X n)^2-
      4*∑ k ∈ Finset.range n, partialSumMax X k*absSlope (realPartialSum X k)*X k := by
  have h := partialSumMax_pathwise X n
  nlinarith [sq_nonneg (partialSumMax X n-2*|realPartialSum X n|),sq_abs (realPartialSum X n)]

lemma measurable_realPartialSum {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (n : ℕ) : Measurable (fun ω => realPartialSum (fun k => X k ω) n) := by
  unfold realPartialSum
  fun_prop

lemma measurable_partialSumMax {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (n : ℕ) : Measurable (fun ω => partialSumMax (fun k => X k ω) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.max (measurable_realPartialSum X hX (n+1)).abs

lemma measurable_absSlope : Measurable absSlope :=
  Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

lemma integrable_of_abs_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable (Eventually.of_forall fun ω => by
    simpa only [Real.norm_eq_abs] using hC ω)

lemma realPartialSum_congr {X Y : ℕ → ℝ} (n : ℕ) (hXY : ∀ k < n, X k = Y k) :
    realPartialSum X n = realPartialSum Y n := by
  exact Finset.sum_congr rfl fun k hk => hXY k (Finset.mem_range.mp hk)

lemma partialSumMax_congr {X Y : ℕ → ℝ} (n : ℕ) (hXY : ∀ k < n, X k = Y k) :
    partialSumMax X n = partialSumMax Y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [partialSumMax,partialSumMax,ih (fun k hk => hXY k (hk.trans (Nat.lt_succ_self _))),
      realPartialSum_congr (n+1) hXY]

lemma independent_max_transform {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ) (n : ℕ) :
    IndepFun (fun ω => partialSumMax (fun k => X k ω) n*absSlope (realPartialSum (fun k => X k ω) n))
      (X n) μ := by
  let Y (v : Fin n → ℝ) (k : ℕ) := if h : k < n then v ⟨k,h⟩ else 0
  have hY : ∀ k, Measurable (fun v => Y v k) := by
    intro k
    by_cases h : k < n <;> simp only [Y,h,↓reduceDIte] <;> fun_prop
  have hm : Measurable (fun v => partialSumMax (Y v) n*absSlope (realPartialSum (Y v) n)) :=
    (measurable_partialSumMax (fun k v => Y v k) hY n).mul
      (measurable_absSlope.comp (measurable_realPartialSum (fun k v => Y v k) hY n))
  have hh := (independent_past_current μ X hX hind n).comp hm measurable_id
  convert hh using 1
  · funext ω
    have heq : ∀ k < n, X k ω = Y (fun j : Fin n => X j ω) k := fun k hk => by simp [Y,hk]
    rw [partialSumMax_congr n heq,realPartialSum_congr n heq]
    rfl
  · rfl

lemma integrable_partialSumMax_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    Integrable (fun ω => (partialSumMax (fun k => X k ω) n)^2) μ := by
  apply integrable_of_abs_bound μ _ ((measurable_partialSumMax X hX n).pow_const 2) ((n*z)^2)
  intro ω
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (partialSumMax_nonneg _ _) (partialSumMax_bound _ hz (fun k => hbound k ω) n) 2

lemma integrable_realPartialSum_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    Integrable (fun ω => (realPartialSum (fun k => X k ω) n)^2) μ := by
  apply (integrable_partialSumMax_square μ X hX hz hbound n).mono'
    ((measurable_realPartialSum X hX n).pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have := abs_partialSum_le_max (fun k => X k ω) n
    rw [← sq_abs (realPartialSum (fun k => X k ω) n)]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2

lemma integral_partialSumMax_square_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (partialSumMax (fun k => X k ω) n)^2 ∂μ) ≤
      4*∫ ω, (realPartialSum (fun k => X k ω) n)^2 ∂μ := by
  let C (k : ℕ) (ω : Ω) := partialSumMax (fun j => X j ω) k*absSlope (realPartialSum (fun j => X j ω) k)
  have hC (k : ℕ) : Measurable (C k) := (measurable_partialSumMax X hX k).mul
    (measurable_absSlope.comp (measurable_realPartialSum X hX k))
  have hCI (k : ℕ) : Integrable (fun ω => C k ω*X k ω) μ := by
    apply integrable_of_abs_bound μ _ ((hC k).mul (hX k)) (k*z*z)
    intro ω
    dsimp [C]
    rw [abs_mul,abs_mul,abs_absSlope,mul_one,abs_of_nonneg (partialSumMax_nonneg _ _)]
    exact mul_le_mul (partialSumMax_bound _ hz (fun j => hbound j ω) k) (hbound k ω)
      (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hz)
  have hzero (k : ℕ) : ∫ ω, C k ω*X k ω ∂μ = 0 := by
    rw [(independent_max_transform μ X hX hind k).integral_fun_mul_eq_mul_integral
      (hC k).aestronglyMeasurable (hX k).aestronglyMeasurable,hmean,mul_zero]
  have hm := integral_mono (integrable_partialSumMax_square μ X hX hz hbound n)
    (((integrable_realPartialSum_square μ X hX hz hbound n).const_mul 4).sub
      ((integrable_finsetSum (Finset.range n) (fun k _ => hCI k)).const_mul 4))
    (fun ω => partialSumMax_square_pathwise (fun k => X k ω) n)
  simp only [Pi.sub_apply] at hm
  rw [integral_sub ((integrable_realPartialSum_square μ X hX hz hbound n).const_mul 4)
    ((integrable_finsetSum (Finset.range n) (fun k _ => hCI k)).const_mul 4),
    integral_const_mul,integral_const_mul,integral_finsetSum _ (fun k _ => hCI k)] at hm
  simpa only [hzero,Finset.sum_const_zero,mul_zero,sub_zero] using hm

lemma integral_partialSum_square_eq_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {z : ℝ} (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (realPartialSum (fun k => X k ω) n)^2 ∂μ) =
      ∑ k ∈ Finset.range n, ∫ ω, (X k ω)^2 ∂μ := by
  have hLp (k : ℕ) : MemLp (X k) 2 μ := MemLp.of_bound (hX k).aestronglyMeasurable z
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbound k ω)
  have hI (k : ℕ) : Integrable (X k) μ := (hLp k).integrable (by norm_num)
  have hsum : ∫ ω, realPartialSum (fun k => X k ω) n ∂μ = 0 := by
    rw [show (fun ω => realPartialSum (fun k => X k ω) n) =
      (fun ω => ∑ k ∈ Finset.range n, X k ω) from rfl,
      integral_finsetSum _ (fun k _ => hI k)]
    simp only [hmean,Finset.sum_const_zero]
  have hv := IndepFun.variance_sum (s := Finset.range n) (fun k _ => hLp k)
    (fun i _ j _ hij => hind.indepFun hij)
  have heq : (∑ k ∈ Finset.range n, X k) = (fun ω => realPartialSum (fun k => X k ω) n) := by
    ext ω
    simp only [realPartialSum,Finset.sum_apply]
  rw [heq,variance_eq_integral (measurable_realPartialSum X hX n).aemeasurable,hsum] at hv
  simpa only [variance_eq_integral (hX _).aemeasurable,hmean,sub_zero] using hv

lemma integral_partialSumMax_square_le_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (partialSumMax (fun k => X k ω) n)^2 ∂μ) ≤
      4*∑ k ∈ Finset.range n, ∫ ω, (X k ω)^2 ∂μ := by
  rw [← integral_partialSum_square_eq_sum μ X hX hind hmean hbound n]
  exact integral_partialSumMax_square_le μ X hX hind hmean hz hbound n

noncomputable def symmetricTruncate (z x : ℝ) : ℝ := if |x| ≤ z then x else 0
noncomputable def truncatedTailCost (z x : ℝ) : ℝ := if z < |x| then z^2 else 0

lemma measurable_symmetricTruncate (z : ℝ) : Measurable (symmetricTruncate z) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_id measurable_const

lemma measurable_truncatedTailCost (z : ℝ) : Measurable (truncatedTailCost z) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_abs) measurable_const measurable_const

lemma symmetricTruncate_bound {z : ℝ} (hz : 0 ≤ z) (x : ℝ) : |symmetricTruncate z x| ≤ z := by
  unfold symmetricTruncate
  split_ifs with h
  · exact h
  · simpa using hz

lemma symmetricTruncate_neg (z x : ℝ) : symmetricTruncate z (-x) = -symmetricTruncate z x := by
  simp only [symmetricTruncate,abs_neg]
  split_ifs <;> simp

lemma symmetricTruncate_sq_le (z x : ℝ) : (symmetricTruncate z x)^2 ≤ min (x^2) (z^2) := by
  unfold symmetricTruncate
  split_ifs with h
  · exact le_min le_rfl (by nlinarith [abs_nonneg x,sq_abs x])
  · simpa only [zero_pow (by norm_num : 2 ≠ 0)] using le_min (sq_nonneg x) (sq_nonneg z)

lemma truncatedTailCost_nonneg (z x : ℝ) : 0 ≤ truncatedTailCost z x := by
  unfold truncatedTailCost
  split_ifs <;> positivity

lemma truncatedTailCost_le {z : ℝ} (hz : 0 ≤ z) (x : ℝ) :
    truncatedTailCost z x ≤ min (x^2) (z^2) := by
  unfold truncatedTailCost
  split_ifs with h
  · exact le_min (by nlinarith [sq_abs x]) le_rfl
  · exact le_min (sq_nonneg x) (sq_nonneg z)

lemma integral_symmetricTruncate_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → ℝ) (z : ℝ)
    (hsym : IdentDistrib S (fun ω => -S ω) μ μ) :
    (∫ ω, symmetricTruncate z (S ω) ∂μ) = 0 := by
  have he := (hsym.comp (measurable_symmetricTruncate z)).integral_eq
  simp only [Function.comp_apply,symmetricTruncate_neg,integral_neg] at he
  linarith

lemma capped_partialSumMax_le_truncated (X : ℕ → ℝ) (n : ℕ) (z : ℝ) :
    min ((partialSumMax X n)^2) (z^2) ≤
      (partialSumMax (fun k => symmetricTruncate z (X k)) n)^2 +
        ∑ k ∈ Finset.range n, truncatedTailCost z (X k) := by
  classical
  by_cases h : ∀ k < n, |X k| ≤ z
  · have he : partialSumMax X n = partialSumMax (fun k => symmetricTruncate z (X k)) n := by
      apply partialSumMax_congr
      intro k hk
      simp only [symmetricTruncate,ite_eq_left (h k hk)]
    rw [he]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right
      (Finset.sum_nonneg fun k _ => truncatedTailCost_nonneg z (X k)))
  · push Not at h
    obtain ⟨k,hkn,hk⟩ := h
    have hs := Finset.single_le_sum (f := fun k => truncatedTailCost z (X k))
      (fun j _ => truncatedTailCost_nonneg z (X j)) (Finset.mem_range.mpr hkn)
    rw [truncatedTailCost,ite_eq_left hk] at hs
    exact (min_le_right _ _).trans (hs.trans (le_add_of_nonneg_left (sq_nonneg _)))

lemma integral_partialSumMax_capped_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    (∫ ω, min ((partialSumMax (fun k => X k ω) n)^2) (z^2) ∂μ) ≤
      5*(n : ℝ)*truncatedVariance μ (X 0) z := by
  let Y (k : ℕ) (ω : Ω) := symmetricTruncate z (X k ω)
  have hY (k : ℕ) : Measurable (Y k) := (measurable_symmetricTruncate z).comp (hX k)
  have hYb (k : ℕ) (ω : Ω) : |Y k ω| ≤ z := symmetricTruncate_bound hz _
  have hYi : iIndepFun Y μ := hind.comp (fun _ => symmetricTruncate z) (fun _ => measurable_symmetricTruncate z)
  have hYm (k : ℕ) : (∫ ω, Y k ω ∂μ) = 0 := by
    rw [show (∫ ω, Y k ω ∂μ) = ∫ ω, Y 0 ω ∂μ from
      ((hident k).comp (measurable_symmetricTruncate z)).integral_eq]
    exact integral_symmetricTruncate_zero μ (X 0) z hsym
  have htI (k : ℕ) : Integrable (fun ω => truncatedTailCost z (X k ω)) μ := by
    apply (integrable_truncated_square μ (X k) (hX k) z).mono'
      (((measurable_truncatedTailCost z).comp (hX k)).aestronglyMeasurable)
    exact Eventually.of_forall fun ω => by
      simp only [Function.comp_apply]
      rw [Real.norm_of_nonneg (truncatedTailCost_nonneg _ _)]
      exact truncatedTailCost_le hz _
  have hsqI (k : ℕ) : Integrable (fun ω => (Y k ω)^2) μ := by
    apply (integrable_truncated_square μ (X k) (hX k) z).mono'
      ((hY k).pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact symmetricTruncate_sq_le _ _
  have heq (k : ℕ) : truncatedVariance μ (X k) z = truncatedVariance μ (X 0) z :=
    ((hident k).comp ((measurable_id.pow_const 2).min measurable_const)).integral_eq
  have hsq (k : ℕ) : (∫ ω, (Y k ω)^2 ∂μ) ≤ truncatedVariance μ (X 0) z := by
    rw [← heq k]
    exact integral_mono (hsqI k) (integrable_truncated_square μ (X k) (hX k) z)
      (fun ω => symmetricTruncate_sq_le _ _)
  have ht (k : ℕ) : (∫ ω, truncatedTailCost z (X k ω) ∂μ) ≤ truncatedVariance μ (X 0) z := by
    rw [← heq k]
    exact integral_mono (htI k) (integrable_truncated_square μ (X k) (hX k) z)
      (fun ω => truncatedTailCost_le hz _)
  have hm := integral_mono (integrable_truncated_square μ _ (measurable_partialSumMax X hX n) z)
    ((integrable_partialSumMax_square μ Y hY hz hYb n).add
      (integrable_finsetSum (Finset.range n) (fun k _ => htI k)))
    (fun ω => capped_partialSumMax_le_truncated (fun k => X k ω) n z)
  simp only [Pi.add_apply] at hm
  rw [integral_add (integrable_partialSumMax_square μ Y hY hz hYb n)
    (integrable_finsetSum (Finset.range n) (fun k _ => htI k)),
    integral_finsetSum _ (fun k _ => htI k)] at hm
  have hmax := integral_partialSumMax_square_le_sum μ Y hY hYi hYm hz hYb n
  have hsum1 := Finset.sum_le_sum (s := Finset.range n) (fun k _ => hsq k)
  have hsum2 := Finset.sum_le_sum (s := Finset.range n) (fun k _ => ht k)
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum1 hsum2
  linarith

lemma measureReal_partialSumMax_gt_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {z : ℝ} (hz : 0 < z) (n : ℕ) :
    μ.real {ω | z < partialSumMax (fun k => X k ω) n} ≤
      5*(n : ℝ)*truncatedVariance μ (X 0) z / z^2 := by
  have hb := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun ω => le_min
      (sq_nonneg (partialSumMax (fun k => X k ω) n)) (sq_nonneg z)))
    (integrable_truncated_square μ _ (measurable_partialSumMax X hX n) z) (z^2)
  have hmono : μ.real {ω | z < partialSumMax (fun k => X k ω) n} ≤
      μ.real {ω | z^2 ≤ min ((partialSumMax (fun k => X k ω) n)^2) (z^2)} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    change z < partialSumMax (fun k => X k ω) n at hω
    change z^2 ≤ min ((partialSumMax (fun k => X k ω) n)^2) (z^2)
    apply le_min
    · nlinarith only [mul_self_le_mul_self hz.le hω.le]
    · exact le_rfl
  apply (le_div_iff₀ (sq_pos_of_pos hz)).mpr
  calc
    μ.real {ω | z < partialSumMax (fun k => X k ω) n} * z^2 ≤
      z^2 * μ.real {ω | z^2 ≤ min ((partialSumMax (fun k => X k ω) n)^2) (z^2)} := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hmono (sq_nonneg z)
    _ ≤ ∫ ω, min ((partialSumMax (fun k => X k ω) n)^2) (z^2) ∂μ := hb
    _ ≤ _ := integral_partialSumMax_capped_le μ X hX hind hident hsym hz.le n

noncomputable def commonIncrementProcess {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (n : ℕ) (P : Path d × Path d) : ℝ :=
  commonWordIncrement e (commonWords ℓ P n)

lemma measurable_commonIncrementProcess {d : ℕ} (ℓ : Vector d) (e : Direction d) (n : ℕ) :
    Measurable (commonIncrementProcess ℓ e n) :=
  (measurable_of_countable (commonWordIncrement e)).comp
    ((measurable_firstPairWord ℓ).comp ((measurable_renewPairSuffix ℓ).iterate n))

lemma commonIncrements_independent {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d) :
    iIndepFun (commonIncrementProcess ℓ e) (independentConditionedPairLaw ν ℓ) :=
  (common_words_independent ν ℓ htrans height hproj hstep).comp
    (fun _ => commonWordIncrement e) (fun _ => measurable_of_countable _)

lemma commonIncrements_identDistrib {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d) (n : ℕ) :
    IdentDistrib (commonIncrementProcess ℓ e n) (commonIncrementProcess ℓ e 0)
      (independentConditionedPairLaw ν ℓ) (independentConditionedPairLaw ν ℓ) :=
  (common_words_identDistrib ν ℓ htrans height hproj hstep n).comp (measurable_of_countable _)

lemma independent_common_maximal_capped {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d)
    {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    (∫ P, min ((partialSumMax (fun k => commonIncrementProcess ℓ e k P) n)^2) (r^2)
      ∂independentConditionedPairLaw ν ℓ) ≤
      5*(n : ℝ)*truncatedVariance (independentConditionedPairLaw ν ℓ)
        (commonIncrementProcess ℓ e 0) r := by
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  exact integral_partialSumMax_capped_le _ _ (measurable_commonIncrementProcess ℓ e)
    (commonIncrements_independent ν ℓ htrans height hproj hstep e)
    (commonIncrements_identDistrib ν ℓ htrans height hproj hstep e)
    (independent_commonWordIncrement_symmetric ν ℓ htrans e) hr n

lemma independent_common_maximal_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d)
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (independentConditionedPairLaw ν ℓ).real
      {P | r < partialSumMax (fun k => commonIncrementProcess ℓ e k P) n} ≤
      5*(n : ℝ)/fluctuationScale (independentConditionedPairLaw ν ℓ)
        (commonIncrementProcess ℓ e 0) r := by
  let : IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) :=
    independentConditionedPairLaw_probability ν ℓ
      (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  rw [fluctuationScale,div_div_eq_mul_div]
  exact measureReal_partialSumMax_gt_le _ _ (measurable_commonIncrementProcess ℓ e)
    (commonIncrements_independent ν ℓ htrans height hproj hstep e)
    (commonIncrements_identDistrib ν ℓ htrans height hproj hstep e)
    (independent_commonWordIncrement_symmetric ν ℓ htrans e) hr n

lemma signedCoordinate_sub {d : ℕ} (e : Direction d) (x y : Lattice d) :
    signedCoordinate e (x-y) = signedCoordinate e x - signedCoordinate e y := by
  simp only [signedCoordinate, Pi.sub_apply, Int.cast_sub]
  split <;> ring

lemma commonTimes_span {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    (n : ℕ) :
    P.1 (commonTimes ℓ P (n+1)).1 =
      P.1 (commonTimes ℓ P n).1 + wordPath 0 (commonWords ℓ P n).1 (commonWords ℓ P n).1.length ∧
    P.2 (commonTimes ℓ P (n+1)).2 =
      P.2 (commonTimes ℓ P n).2 + wordPath 0 (commonWords ℓ P n).2 (commonWords ℓ P n).2.length := by
  have he := iterate_renewPairSuffix_eq ℓ P h0 h0' n
  have h1 := (hP n).2.1.1 _ le_rfl
  have h2 := (hP n).2.1.2 _ le_rfl
  rw [he] at h1 h2
  rw [commonTimes_succ]
  constructor
  · exact (sub_eq_iff_eq_add.mp h1).trans (add_comm _ _)
  · exact (sub_eq_iff_eq_add.mp h2).trans (add_comm _ _)

lemma common_coordinate_sum {d : ℕ} (ℓ : Vector d) (e : Direction d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    (n : ℕ) :
    signedCoordinate e (P.1 (commonTimes ℓ P n).1) -
      signedCoordinate e (P.2 (commonTimes ℓ P n).2) =
        realPartialSum (fun k => commonIncrementProcess ℓ e k P) n := by
  induction n with
  | zero => simp [commonTimes_zero,h0,h0',signedCoordinate,realPartialSum]
  | succ n ih =>
    obtain ⟨h1,h2⟩ := commonTimes_span ℓ P h0 h0' hP n
    rw [h1,h2,signedCoordinate_add,signedCoordinate_add,realPartialSum_succ,← ih]
    simp only [commonIncrementProcess,commonWordIncrement,wordCoordinate]
    ring

lemma commonIndex_le_recordCount {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    (n : ℕ) : n ≤ recordCount ℓ P.1 (commonTimes ℓ P n).1 := by
  rw [recordCount_commonTimes ℓ P h0 h0' hP n]
  calc
    n = ∑ i ∈ Finset.range n, 1 := by simp
    _ ≤ ∑ i ∈ Finset.range n, wordRecordCount ℓ (commonWords ℓ P i).1 :=
      Finset.sum_le_sum fun i _ => commonWordWidth_positive ℓ _ _ (hP i)

end DirectionalTransience
end
end

end OAI
