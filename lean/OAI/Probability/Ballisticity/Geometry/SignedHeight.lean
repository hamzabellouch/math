import Mathlib
import OAI.Probability.Ballisticity.Estimates.IntegerMedian

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

def signedHeight {d : ℕ} (e : Direction d) (x : Lattice d) : ℤ :=
  if e.2 then x e.1 else -x e.1

lemma signedHeight_projection {d : ℕ} (e : Direction d) (x : Lattice d) :
    dot (realPosition x) (realPosition (step e)) = (signedHeight e x : ℝ) := by
  rw [dot_signed_direction]
  simp only [signedCoordinate,signedHeight,Int.cast_ite,Int.cast_neg]

lemma signedHeight_step_le {d : ℕ} (e : Direction d) (x : Lattice d) (f : Direction d) :
    signedHeight e (x+step f) ≤ signedHeight e x+1 := by
  simp only [signedHeight,Pi.add_apply,step]
  split <;> split <;> (try split) <;> omega

theorem transverse_common_gaussian_marginal {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) (τ : ℝ≥0) :
    letI : IsProbabilityMeasure (independentConditionedPairLaw ν (realPosition (step e))) :=
      independentConditionedPairLaw_probability ν _
        (ne_of_gt (noDrop_positive_of_directionallyTransient ν _ htrans))
    TendstoInDistribution
      (fun i P => realPartialSum (fun k => commonIncrementProcess (realPosition (step e)) f k P)
        (⌊(τ:ℝ)*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) (r i)⌋₊) / r i)
      atTop id (fun _ => independentConditionedPairLaw ν (realPosition (step e))) (gaussianReal 0 τ) :=
  independent_common_gaussian_marginal ν hue _ (signed_direction_unit e) htrans
    (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e) f
    (independent_commonWordIncrement_nonzero ν hue e f hef htrans) r hr τ

lemma max_fourth_increment {m a : ℝ} :
    (max m |a|)^4-m^4 ≤ 2*|a| *((max m |a|)^3-m^3) := by
  by_cases h : |a| ≤ m
  · rw [max_eq_left h]; ring_nf; rfl
  · rw [max_eq_right (le_of_not_ge h)]
    have hp := mul_nonneg (mul_nonneg (abs_nonneg a) (sq_nonneg m))
      (sub_nonneg.mpr (le_of_not_ge h))
    nlinarith [sq_nonneg (|a|^2-m^2)]

lemma partialSumMax_fourth_pathwise (X : ℕ → ℝ) (n : ℕ) :
    (partialSumMax X n)^4 ≤ 2*(partialSumMax X n)^3*|realPartialSum X n|-
      2*∑ k ∈ Finset.range n, (partialSumMax X k)^3*absSlope (realPartialSum X k)*X k := by
  induction n with
  | zero => simp [partialSumMax]
  | succ n ih =>
    have hincr := max_fourth_increment (m := partialSumMax X n)
      (a := realPartialSum X (n+1))
    have hs := mul_le_mul_of_nonneg_left (abs_supporting (realPartialSum X n) (X n))
      (pow_nonneg (partialSumMax_nonneg X n) 3)
    rw [← realPartialSum_succ] at hs
    rw [Finset.sum_range_succ]
    change (max (partialSumMax X n) |realPartialSum X (n+1)|)^4 ≤ _
    change _ ≤ 2*(max (partialSumMax X n) |realPartialSum X (n+1)|)^3 * |realPartialSum X (n+1)|-_
    nlinarith

lemma partialSumMax_fourth_pathwise_bound (X : ℕ → ℝ) (n : ℕ) :
    (partialSumMax X n)^4 ≤ 32*(realPartialSum X n)^4-
      4*∑ k ∈ Finset.range n, (partialSumMax X k)^3*absSlope (realPartialSum X k)*X k := by
  have h := partialSumMax_fourth_pathwise X n
  have hy : 2*(partialSumMax X n)^3*|realPartialSum X n| ≤
      (partialSumMax X n)^4/2+16*(realPartialSum X n)^4 := by
    nlinarith [sq_nonneg ((partialSumMax X n)^2-4*partialSumMax X n*|realPartialSum X n|),
      sq_nonneg ((partialSumMax X n)^2-8*(realPartialSum X n)^2),
      sq_abs (realPartialSum X n)]
  linarith

lemma integrable_partialSumMax_pow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n p : ℕ) :
    Integrable (fun ω => (partialSumMax (fun k => X k ω) n)^p) μ := by
  apply integrable_of_abs_bound μ _ ((measurable_partialSumMax X hX n).pow_const p) ((n*z)^p)
  intro ω
  rw [abs_of_nonneg (pow_nonneg (partialSumMax_nonneg _ _) _)]
  exact pow_le_pow_left₀ (partialSumMax_nonneg _ _) (partialSumMax_bound _ hz (fun k => hbound k ω) n) p

lemma integrable_realPartialSum_pow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n p : ℕ) :
    Integrable (fun ω => (realPartialSum (fun k => X k ω) n)^p) μ := by
  apply integrable_of_abs_bound μ _ ((measurable_realPartialSum X hX n).pow_const p) ((n*z)^p)
  intro ω
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) ((abs_partialSum_le_max _ _).trans
    (partialSumMax_bound _ hz (fun k => hbound k ω) n)) p

lemma absSlope_cube (t : ℝ) : (absSlope t)^3 = absSlope t := by
  unfold absSlope
  split <;> norm_num

lemma independent_max_cube_transform {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ) (n : ℕ) :
    IndepFun (fun ω => (partialSumMax (fun k => X k ω) n)^3*absSlope (realPartialSum (fun k => X k ω) n))
      (X n) μ := by
  have hh := (independent_max_transform μ X hX hind n).comp
    (show Measurable (fun x : ℝ => x^3) by fun_prop) measurable_id
  simpa only [Function.comp_def,mul_pow,absSlope_cube,id_eq] using hh

lemma integral_partialSumMax_fourth_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hmean : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (partialSumMax (fun k => X k ω) n)^4 ∂μ) ≤
      32*∫ ω, (realPartialSum (fun k => X k ω) n)^4 ∂μ := by
  let C (k : ℕ) (ω : Ω) := (partialSumMax (fun j => X j ω) k)^3*absSlope (realPartialSum (fun j => X j ω) k)
  have hC (k : ℕ) : Measurable (C k) := ((measurable_partialSumMax X hX k).pow_const 3).mul
    (measurable_absSlope.comp (measurable_realPartialSum X hX k))
  have hCI (k : ℕ) : Integrable (fun ω => C k ω*X k ω) μ := by
    apply integrable_of_abs_bound μ _ ((hC k).mul (hX k)) ((k*z)^3*z)
    intro ω
    dsimp [C]
    rw [abs_mul,abs_mul,abs_absSlope,mul_one,abs_of_nonneg (pow_nonneg (partialSumMax_nonneg _ _) _)]
    exact mul_le_mul (pow_le_pow_left₀ (partialSumMax_nonneg _ _)
      (partialSumMax_bound _ hz (fun j => hbound j ω) k) 3) (hbound k ω)
      (abs_nonneg _) (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hz) 3)
  have hzero (k : ℕ) : ∫ ω, C k ω*X k ω ∂μ = 0 := by
    rw [(independent_max_cube_transform μ X hX hind k).integral_fun_mul_eq_mul_integral
      (hC k).aestronglyMeasurable (hX k).aestronglyMeasurable,hmean,mul_zero]
  have hm := integral_mono (integrable_partialSumMax_pow μ X hX hz hbound n 4)
    (((integrable_realPartialSum_pow μ X hX hz hbound n 4).const_mul 32).sub
      ((integrable_finsetSum (Finset.range n) (fun k _ => hCI k)).const_mul 4))
    (fun ω => partialSumMax_fourth_pathwise_bound (fun k => X k ω) n)
  simp only [Pi.sub_apply] at hm
  rw [integral_sub ((integrable_realPartialSum_pow μ X hX hz hbound n 4).const_mul 32)
    ((integrable_finsetSum (Finset.range n) (fun k _ => hCI k)).const_mul 4),
    integral_const_mul,integral_const_mul,integral_finsetSum _ (fun k _ => hCI k)] at hm
  simpa only [hzero,Finset.sum_const_zero,mul_zero,sub_zero] using hm

lemma independent_partialSum_current {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ) (n : ℕ) :
    IndepFun (fun ω => realPartialSum (fun k => X k ω) n) (X n) μ := by
  have hh := (independent_past_current μ X hX hind n).comp
    (show Measurable (fun v : Fin n → ℝ => ∑ k, v k) by fun_prop) measurable_id
  convert hh using 1
  · funext ω
    exact (Fin.sum_univ_eq_sum_range (fun k => X k ω) n).symm
  · rfl

lemma integrable_pow_mul_of_abs_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F G : Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G) {a b : ℝ}
    (ha : ∀ ω, |F ω| ≤ a) (hb : ∀ ω, |G ω| ≤ b) (p q : ℕ) :
    Integrable (fun ω => F ω^p*G ω^q) μ := by
  apply integrable_of_abs_bound μ _ (by fun_prop) (a^p*b^q)
  intro ω
  rw [abs_mul,abs_pow,abs_pow]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (ha ω) p)
    (pow_le_pow_left₀ (abs_nonneg _) (hb ω) q) (pow_nonneg (abs_nonneg _) _)
    (pow_nonneg ((abs_nonneg (F ω)).trans (ha ω)) _)

lemma integral_independent_add_fourth {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F G : Ω → ℝ)
    (hF : Measurable F) (hG : Measurable G) (hind : IndepFun F G μ)
    (hmF : ∫ ω, F ω ∂μ = 0) (hmG : ∫ ω, G ω ∂μ = 0)
    {a b : ℝ} (ha : ∀ ω, |F ω| ≤ a) (hb : ∀ ω, |G ω| ≤ b) :
    (∫ ω, (F ω+G ω)^4 ∂μ) =
      (∫ ω, F ω^4 ∂μ)+6*(∫ ω, F ω^2 ∂μ)*(∫ ω, G ω^2 ∂μ)+(∫ ω, G ω^4 ∂μ) := by
  have hI := integrable_pow_mul_of_abs_bound μ F G hF hG ha hb
  have hF4 : Integrable (fun ω => F ω^4) μ := by simpa using hI 4 0
  have hG4 : Integrable (fun ω => G ω^4) μ := by simpa using hI 0 4
  have h31 : Integrable (fun ω => 4*(F ω^3*G ω^1)) μ := (hI 3 1).const_mul 4
  have h22 : Integrable (fun ω => 6*(F ω^2*G ω^2)) μ := (hI 2 2).const_mul 6
  have h13 : Integrable (fun ω => 4*(F ω^1*G ω^3)) μ := (hI 1 3).const_mul 4
  have hfactor (p q : ℕ) : (∫ ω, F ω^p*G ω^q ∂μ) =
      (∫ ω, F ω^p ∂μ)*(∫ ω, G ω^q ∂μ) :=
    (hind.comp (by fun_prop : Measurable (fun x : ℝ => x^p))
      (by fun_prop : Measurable (fun x : ℝ => x^q))).integral_fun_mul_eq_mul_integral
      (hF.pow_const p).aestronglyMeasurable (hG.pow_const q).aestronglyMeasurable
  have heq : (fun ω => (F ω+G ω)^4) =
      (fun ω => F ω^4+4*(F ω^3*G ω^1)+6*(F ω^2*G ω^2)+4*(F ω^1*G ω^3)+G ω^4) := by
    ext ω; ring
  have h12 : Integrable (fun ω => F ω^4+4*(F ω^3*G ω^1)) μ := hF4.add h31
  have h123 : Integrable (fun ω => F ω^4+4*(F ω^3*G ω^1)+6*(F ω^2*G ω^2)) μ := h12.add h22
  have h1234 : Integrable (fun ω => F ω^4+4*(F ω^3*G ω^1)+6*(F ω^2*G ω^2)+4*(F ω^1*G ω^3)) μ := h123.add h13
  rw [heq,integral_add h1234 hG4,integral_add h123 h13,integral_add h12 h22,
    integral_add hF4 h31]
  simp only [integral_const_mul]
  rw [hfactor 3 1,hfactor 2 2,hfactor 1 3]
  simp only [pow_one,hmF,hmG,mul_zero,zero_mul,add_zero]
  ring

lemma integral_iid_partialSum_fourth_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {z : ℝ} (hz : 0 ≤ z) (hbound : ∀ k ω, |X k ω| ≤ z) (n : ℕ) :
    (∫ ω, (realPartialSum (fun k => X k ω) n)^4 ∂μ) ≤
      n*(∫ ω, (X 0 ω)^4 ∂μ)+3*(n:ℝ)^2*(∫ ω, (X 0 ω)^2 ∂μ)^2 := by
  have hmeans (k : ℕ) : ∫ ω, X k ω ∂μ = 0 := (hident k).integral_eq.trans hmean
  have hpows (k p : ℕ) : (∫ ω, (X k ω)^p ∂μ) = (∫ ω, (X 0 ω)^p ∂μ) :=
    ((hident k).comp (u := fun x : ℝ => x^p) (by fun_prop)).integral_eq
  have hsq (n : ℕ) : (∫ ω, (realPartialSum (fun k => X k ω) n)^2 ∂μ) =
      n*(∫ ω, (X 0 ω)^2 ∂μ) := by
    rw [integral_partialSum_square_eq_sum μ X hX hind hmeans hbound]
    simp only [hpows,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hsummean (n : ℕ) : ∫ ω, realPartialSum (fun k => X k ω) n ∂μ = 0 := by
    rw [show (fun ω => realPartialSum (fun k => X k ω) n) =
      (fun ω => ∑ k ∈ Finset.range n, X k ω) from rfl,
      integral_finsetSum _ (fun k _ => integrable_of_abs_bound μ _ (hX k) z (hbound k))]
    simp only [hmeans,Finset.sum_const_zero]
  induction n with
  | zero => simp [realPartialSum]
  | succ n ih =>
    simp only [realPartialSum_succ]
    rw [integral_independent_add_fourth μ _ _ (measurable_realPartialSum X hX n) (hX n)
      (independent_partialSum_current μ X hX hind n) (hsummean n) (hmeans n)
      (fun ω => (abs_partialSum_le_max _ _).trans (partialSumMax_bound _ hz (fun k => hbound k ω) n))
      (hbound n),hsq]
    simp only [hpows]
    push_cast
    nlinarith [sq_nonneg (∫ ω, (X 0 ω)^2 ∂μ)]

lemma integral_iid_truncated_max_fourth_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {z r : ℝ} (hz : 0 ≤ z) (hzr : z ≤ r) (n : ℕ) :
    (∫ ω, (partialSumMax (fun k => symmetricTruncate z (X k ω)) n)^4 ∂μ) ≤
      32*(n:ℝ)*z^2*truncatedVariance μ (X 0) r+
        96*(n:ℝ)^2*(truncatedVariance μ (X 0) r)^2 := by
  let Y := fun k ω => symmetricTruncate z (X k ω)
  have hY (k : ℕ) : Measurable (Y k) := (measurable_symmetricTruncate z).comp (hX k)
  have hYb := fun k ω => symmetricTruncate_bound hz (X k ω)
  have hYi : iIndepFun Y μ := hind.comp (fun _ => symmetricTruncate z) (fun _ => measurable_symmetricTruncate z)
  have hYid (k : ℕ) : IdentDistrib (Y k) (Y 0) μ μ := (hident k).comp (measurable_symmetricTruncate z)
  have hYm : ∫ ω, Y 0 ω ∂μ = 0 := integral_symmetricTruncate_zero μ (X 0) z hsym
  have hYmeans (k : ℕ) : ∫ ω, Y k ω ∂μ = 0 := (hYid k).integral_eq.trans hYm
  have hI (p : ℕ) : Integrable (fun ω => (Y 0 ω)^p) μ := by
    apply integrable_of_abs_bound μ _ ((hY 0).pow_const p) (z^p)
    intro ω
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hYb 0 ω) p
  have hvar : (∫ ω, (Y 0 ω)^2 ∂μ) ≤ truncatedVariance μ (X 0) r := by
    apply integral_mono (hI 2) (integrable_truncated_square μ (X 0) (hX 0) r)
    intro ω
    exact (symmetricTruncate_sq_le z _).trans
      (min_le_min le_rfl (pow_le_pow_left₀ hz hzr 2))
  have hfour : (∫ ω, (Y 0 ω)^4 ∂μ) ≤ z^2*(∫ ω, (Y 0 ω)^2 ∂μ) := by
    rw [← integral_const_mul]
    apply integral_mono (hI 4) ((hI 2).const_mul (z^2))
    intro ω
    have hs : (Y 0 ω)^2 ≤ z^2 := by
      nlinarith [sq_abs (Y 0 ω),hYb 0 ω,abs_nonneg (Y 0 ω)]
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (Y 0 ω))]
  have hv0 : 0 ≤ ∫ ω, (Y 0 ω)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  calc
    _ ≤ 32*(∫ ω, (realPartialSum (fun k => Y k ω) n)^4 ∂μ) :=
      integral_partialSumMax_fourth_le μ Y hY hYi hYmeans hz hYb n
    _ ≤ 32*(n*(∫ ω, (Y 0 ω)^4 ∂μ)+3*(n:ℝ)^2*(∫ ω, (Y 0 ω)^2 ∂μ)^2) :=
      mul_le_mul_of_nonneg_left (integral_iid_partialSum_fourth_le μ Y hY hYi hYid hYm hz hYb n) (by norm_num)
    _ ≤ 32*(n*(z^2*truncatedVariance μ (X 0) r)+3*(n:ℝ)^2*(truncatedVariance μ (X 0) r)^2) := by
      gcongr
      · exact hfour.trans (mul_le_mul_of_nonneg_left hvar (sq_nonneg z))
    _ = _ := by ring

lemma measureReal_truncated_max_gt_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {z r a : ℝ} (hz : 0 ≤ z) (hzr : z ≤ r) (ha : 0 < a) (n : ℕ) :
    μ.real {ω | a < partialSumMax (fun k => symmetricTruncate z (X k ω)) n} ≤
      (32*(n:ℝ)*z^2*truncatedVariance μ (X 0) r+
        96*(n:ℝ)^2*(truncatedVariance μ (X 0) r)^2) / a^4 := by
  let Y := fun k ω => symmetricTruncate z (X k ω)
  have hY (k : ℕ) : Measurable (Y k) := (measurable_symmetricTruncate z).comp (hX k)
  have hYb := fun k ω => symmetricTruncate_bound hz (X k ω)
  have hb := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun ω => pow_nonneg (partialSumMax_nonneg (fun k => Y k ω) n) 4))
    (integrable_partialSumMax_pow μ Y hY hz hYb n 4) (a^4)
  have hmono : μ.real {ω | a < partialSumMax (fun k => Y k ω) n} ≤
      μ.real {ω | a^4 ≤ (partialSumMax (fun k => Y k ω) n)^4} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    exact pow_le_pow_left₀ ha.le hω.le 4
  apply (le_div_iff₀ (pow_pos ha 4)).mpr
  calc
    _ ≤ a^4*μ.real {ω | a^4 ≤ (partialSumMax (fun k => Y k ω) n)^4} := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hmono (pow_nonneg ha.le 4)
    _ ≤ (∫ ω, (partialSumMax (fun k => Y k ω) n)^4 ∂μ) := hb
    _ ≤ _ := integral_iid_truncated_max_fourth_le μ X hX hind hident hsym hz hzr n

lemma measureReal_iid_max_gt_fourth_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {z r a : ℝ} (hz : 0 ≤ z) (hzr : z ≤ r) (ha : 0 < a) (n : ℕ) :
    μ.real {ω | a < partialSumMax (fun k => X k ω) n} ≤
      n*μ.real {ω | z < |X 0 ω|}+
      (32*(n:ℝ)*z^2*truncatedVariance μ (X 0) r+
        96*(n:ℝ)^2*(truncatedVariance μ (X 0) r)^2) / a^4 := by
  let A : ℕ → Set Ω := fun k => {ω | z < |X k ω|}
  let B : Set Ω := {ω | a < partialSumMax (fun k => symmetricTruncate z (X k ω)) n}
  have hsub : {ω | a < partialSumMax (fun k => X k ω) n} ⊆
      (⋃ k ∈ Finset.range n, A k) ∪ B := by
    intro ω hω
    by_cases ht : ω ∈ ⋃ k ∈ Finset.range n, A k
    · exact Or.inl ht
    · right
      have hc : ∀ k < n, X k ω = symmetricTruncate z (X k ω) := by
        intro k hk
        have hnot : ¬ z < |X k ω| := fun h => ht (Set.mem_iUnion.mpr
          ⟨k,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hk,h⟩⟩)
        simp only [symmetricTruncate,ite_eq_left (le_of_not_gt hnot)]
      change a < partialSumMax (fun k => symmetricTruncate z (X k ω)) n
      rwa [← partialSumMax_congr n hc]
  have htail (k : ℕ) : μ.real (A k) = μ.real (A 0) := by
    exact congrArg ENNReal.toReal ((hident k).measure_mem_eq
      (show MeasurableSet {x : ℝ | z < |x|} from measurableSet_lt measurable_const measurable_id.abs))
  calc
    _ ≤ μ.real ((⋃ k ∈ Finset.range n, A k) ∪ B) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real (⋃ k ∈ Finset.range n, A k)+μ.real B := measureReal_union_le _ _
    _ ≤ (∑ k ∈ Finset.range n, μ.real (A k))+μ.real B :=
      add_le_add (measureReal_biUnion_finset_le _ _) le_rfl
    _ = n*μ.real {ω | z < |X 0 ω|}+μ.real B := by
      simp only [htail,Finset.sum_const,Finset.card_range,nsmul_eq_mul,A]
    _ ≤ _ := add_le_add le_rfl (measureReal_truncated_max_gt_le μ X hX hind hident hsym hz hzr ha n)

lemma gaussian_charFun_power_limit_count {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Ω → ℝ) (hS : Measurable S)
    (hI : Integrable S μ) (hne : 0 < μ {x | S x ≠ 0})
    (hsym : IdentDistrib S (fun x => -S x) μ μ) (r : ℕ → ℝ)
    (hr : IsGaussianSequence μ S r) (k : ℕ → ℕ) {τ : ℝ}
    (hk : Tendsto (fun i => (k i : ℝ)/fluctuationScale μ S (r i)) atTop (𝓝 τ)) (t : ℝ) :
    Tendsto (fun i => (charFun (μ.map S) (t/r i))^(k i))
      atTop (𝓝 (Complex.exp (-(τ*t^2/2 : ℝ)))) := by
  have hn : Tendsto (fun i => fluctuationScale μ S (r i)) atTop atTop :=
    (fluctuationScale_tendsto μ S hS hI hne).comp hr.1
  have hd := gaussian_cosine_drift μ S hS hne r hr t
  have hzero : Tendsto (fun i => (∫ x, Real.cos (t*(S x/r i)) ∂μ)-1) atTop (𝓝 0) := by
    have hz := hd.mul (tendsto_inv_atTop_zero.comp hn)
    simp only [mul_zero] at hz
    apply hz.congr'
    filter_upwards [hn.eventually (eventually_gt_atTop (0:ℝ))] with i hi
    dsimp only [Function.comp_def]
    field_simp
  have ha : Tendsto (fun i => ∫ x, Real.cos (t*(S x/r i)) ∂μ) atTop (𝓝 1) := by
    simpa using hzero.add_const 1
  have hdk : Tendsto (fun i => (k i : ℝ)*
      ((∫ x, Real.cos (t*(S x/r i)) ∂μ)-1)) atTop (𝓝 (-(τ*t^2/2))) := by
    have hc := hk.mul hd
    have he : τ * (-(t^2/2)) = -(τ*t^2/2) := by ring
    rw [he] at hc
    apply hc.congr'
    filter_upwards [hn.eventually (eventually_gt_atTop (0:ℝ))] with i hi
    field_simp
  convert (tendsto_pow_variable_of_drift ha hdk).ofReal using 1
  · ext i
    rw [symmetric_charFun_cosine μ S hS hsym, ← Complex.ofReal_pow]
    congr 2
    apply integral_congr_ae
    filter_upwards [] with x
    congr 1
    ring
  · simp

lemma charFun_independent_finite_blocks {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (k : ι → ℕ) (g : (j : ι) → Fin (k j) → ℕ)
    (hg : Function.Injective (fun p : (j : ι) × Fin (k j) => g p.1 p.2)) (r : ℝ)
    (t : EuclideanSpace ℝ ι) :
    charFun (μ.map (fun ω => WithLp.toLp 2 (fun j => (∑ l, X (g j l) ω)/r))) t =
      ∏ j, (charFun (μ.map (X 0)) (t j/r))^(k j) := by
  classical
  let Y (p : (j : ι) × Fin (k j)) (ω : Ω) := (t p.1/r)*X (g p.1 p.2) ω
  have hY p : Measurable (Y p) := (hX _).const_mul _
  have hiY : iIndepFun Y μ := (hind.precomp hg).comp
    (fun p x => (t p.1/r)*x) (fun _ => by fun_prop)
  have heq : charFun (μ.map (fun ω => WithLp.toLp 2 (fun j => (∑ l, X (g j l) ω)/r))) t =
      charFun (μ.map (fun ω => ∑ p, Y p ω)) 1 := by
    rw [charFun, charFun, integral_map (by fun_prop) (by fun_prop),
      integral_map (by fun_prop) (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [] with ω
    congr 2
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      one_mul, Fintype.sum_sigma, Y]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum]
    ring
  rw [heq,hiY.charFun_map_fun_sum_eq_prod (fun p => (hY p).aemeasurable)]
  simp only [Finset.prod_apply]
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  have hterm (l : Fin (k j)) : charFun (μ.map (Y ⟨j,l⟩)) 1 =
      charFun (μ.map (X 0)) (t j/r) := by
    dsimp [Y]
    rw [charFun_map_mul_comp (hX _).aemeasurable,mul_one,(hident _).map_eq]
  simp only [hterm,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem gaussian_iid_finite_block_limit {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hI : Integrable (X 0) μ) (hne : 0 < μ {x | X 0 x ≠ 0})
    (hsym : IdentDistrib (X 0) (fun x => -X 0 x) μ μ)
    (r : ℕ → ℝ) (hr : IsGaussianSequence μ (X 0) r)
    (k : ℕ → ι → ℕ) (g : (i : ℕ) → (j : ι) → Fin (k i j) → ℕ)
    (hg : ∀ i, Function.Injective (fun p : (j : ι) × Fin (k i j) => g i p.1 p.2))
    (τ : ι → ℝ≥0)
    (hk : ∀ j, Tendsto (fun i => (k i j : ℝ)/fluctuationScale μ (X 0) (r i)) atTop (𝓝 (τ j : ℝ))) :
    TendstoInDistribution
      (fun i ω => WithLp.toLp 2 (fun j => (∑ l, X (g i j l) ω)/r i)) atTop
      (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) (fun _ => μ)
      (Measure.pi (fun j => gaussianReal 0 (τ j))) where
  forall_aemeasurable _ := by fun_prop
  aemeasurable_limit := by fun_prop
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    change Tendsto (fun i => charFun (μ.map (fun ω => WithLp.toLp 2 (fun j => (∑ l, X (g i j l) ω)/r i))) t)
      atTop (𝓝 (charFun ((Measure.pi (fun j => gaussianReal 0 (τ j))).map (WithLp.toLp 2)) t))
    simp only [charFun_independent_finite_blocks μ X hX hind hident _ _ (hg _) _,charFun_pi]
    apply tendsto_finsetProd _
    intro j _
    simpa only [charFun_gaussianReal,Complex.ofReal_zero,mul_zero,zero_mul,zero_sub,
      Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.ofReal_ofNat] using
      gaussian_charFun_power_limit_count μ (X 0) (hX 0) hI hne hsym r hr (fun i => k i j) (hk j) (t j)

end DirectionalTransience
end
end

end OAI
