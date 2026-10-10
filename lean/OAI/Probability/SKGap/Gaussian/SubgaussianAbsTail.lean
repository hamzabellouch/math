import Mathlib
import OAI.Probability.SKGap.Localization.StandardArrayLaw

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
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
namespace SKGapCutoff.Regression

lemma subgaussian_abs_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ {ω | ε ≤ |X ω|} ≤ 2 * ENNReal.ofReal (Real.exp (-ε^2/(2*(c:ℝ)))) := by
  have hu := ENNReal.ofReal_le_ofReal (hX.measure_ge_le hε)
  have hl := ENNReal.ofReal_le_ofReal (hX.neg.measure_ge_le hε)
  simp only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hu hl
  have hs : {ω | ε ≤ |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    intro ω h
    simpa only [Set.mem_union, Set.mem_ofPred_eq, le_abs] using h
  calc
    _ ≤ _ := measure_mono hs
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add hu hl
    _ = _ := (two_mul _).symm

lemma iid_bounded_average_tail_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hXi : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) μ) (f : ℝ → ℝ)
    (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ z, |f z| ≤ B)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ {g |
      ε ≤ |(∑ i : Fin n, f (X i g))/(n:ℝ) - ∫ z, f z ∂gaussianReal 0 1|} ≤
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(2*B^2))) := by
  let m := ∫ z, f z ∂gaussianReal 0 1
  have hi : iIndepFun (fun i (g : Ω) => f (X i g) - m) μ :=
    hXi.comp (fun _ z => f z-m) (fun _ => hf.sub_const m)
  have hm (i : Fin n) :
      (∫ g : Ω, f (X i g) ∂μ) = m := by
    exact (hX i).integral_comp hf.aestronglyMeasurable
  have hsub (i : Fin n) : HasSubgaussianMGF (fun g : Ω => f (X i g)-m)
      ((‖B-(-B)‖₊/2)^2) μ := by
    have hb : ∀ᵐ g : Ω ∂μ, f (X i g) ∈ Set.Icc (-B) B :=
      Eventually.of_forall (fun g => abs_le.mp (hbound (X i g)))
    simpa only [hm] using hasSubgaussianMGF_of_mem_Icc
      (show AEMeasurable (fun g : Ω => f (X i g)) μ from
        hf.comp_aemeasurable (hX i).aemeasurable) hb
  have hh := subgaussian_abs_tail
    (HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ) (fun i _ => hsub i))
    (ε*n) (by positivity)
  have he (g : Ω) :
      (ε*(n:ℝ) ≤ |∑ i : Fin n, (f (X i g)-m)|) ↔
      ε ≤ |(∑ i : Fin n, f (X i g))/(n:ℝ)-m| := by
    have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have heq : (∑ i : Fin n, f (X i g))-(n:ℝ)*m =
        (n:ℝ)*((∑ i : Fin n, f (X i g))/(n:ℝ)-m) := by field_simp
    rw [heq, abs_mul, abs_of_pos hnR]
    rw [mul_comm ε (n:ℝ), mul_le_mul_iff_right₀ hnR]
  simp only [he] at hh
  convert hh using 1
  congr 3
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
    coe_nnnorm, Real.norm_eq_abs]
  rw [abs_of_nonneg (by linarith : 0 ≤ B-(-B))]
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  by_cases hB0 : B=0
  · simp [hB0]
  · field_simp
    ring

lemma iid_bounded_average_tail {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ)
    (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ z, |f z| ≤ B)
    (ε : ℝ) (hε : 0 ≤ ε) :
    standardArrayLaw (Fin n) {g |
      ε ≤ |(∑ i : Fin n, f (g i))/(n:ℝ) - ∫ z, f z ∂gaussianReal 0 1|} ≤
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(2*B^2))) := by
  exact iid_bounded_average_tail_of_hasLaw (μ := standardArrayLaw (Fin n)) hn
    (fun (i : Fin n) (g : Fin n → ℝ) => g i)
    coordinates_independent coordinate_hasLaw f hf B hB hbound ε hε

lemma gaussian_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : HasSubgaussianMGF X v μ where
  integrable_exp_mul t := by
    rw [← mgf_pos_iff, mgf_gaussianReal hX]
    exact Real.exp_pos _
  mgf_le t := by
    rw [mgf_gaussianReal hX]
    simp

lemma average_common_shift_bound {n : ℕ} (hn : 0 < n) {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (v : Fin n → ℝ) (r : ℝ) :
    |(∑ i, f (v i+r))/(n:ℝ) - (∑ i, f (v i))/(n:ℝ)| ≤ (K:ℝ)*|r| := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hnR]
  apply (div_le_iff₀ hnR).mpr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, (K:ℝ)*|r| := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.dist_eq, add_sub_cancel_left] using hf.dist_le_mul (v i+r) (v i)
    _ = _ := by simp [mul_comm]

lemma iid_common_shift_average_tail {n : ℕ} (hn : 0 < n) (m a b : ℝ)
    (f : ℝ → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ z, |f z| ≤ B)
    (ε : ℝ) (hε : 0 ≤ ε) :
    standardArrayLaw (Option (Fin n)) {g |
      ε ≤ |(∑ i : Fin n, f (m+a*g (some i)+b*g none))/(n:ℝ) -
        ∫ z, f (m+a*z) ∂gaussianReal 0 1|} ≤
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(8*B^2))) +
      2 * ENNReal.ofReal (Real.exp (-ε^2/(8*(K:ℝ)^2*b^2))) := by
  let M := ∫ z, f (m+a*z) ∂gaussianReal 0 1
  let A (g : Option (Fin n) → ℝ) := (∑ i : Fin n, f (m+a*g (some i)))/(n:ℝ)
  have hi : iIndepFun (fun i : Fin n => fun g : Option (Fin n) → ℝ => g (some i))
      (standardArrayLaw (Option (Fin n))) := coordinates_independent.precomp (Option.some_injective (Fin n))
  have ht := iid_bounded_average_tail_of_hasLaw (μ := standardArrayLaw (Option (Fin n))) hn
    (fun (i : Fin n) (g : Option (Fin n) → ℝ) => g (some i)) hi
    (fun i => coordinate_hasLaw (some i)) (fun z => f (m+a*z))
    (hf.continuous.measurable.comp (measurable_const.add (measurable_const.mul measurable_id)))
    B hB (fun z => hbound _) (ε/2) (by positivity)
  have hz := subgaussian_abs_tail
    ((gaussian_hasSubgaussianMGF (coordinate_hasLaw (none : Option (Fin n)))).const_mul ((K:ℝ)*b))
    (ε/2) (by positivity)
  have hsub : {g | ε ≤ |(∑ i : Fin n, f (m+a*g (some i)+b*g none))/(n:ℝ)-M|} ⊆
      {g | ε/2 ≤ |A g-M|} ∪ {g | ε/2 ≤ |(K:ℝ)*b*g none|} := by
    intro g hg
    by_cases ha : ε/2 ≤ |A g-M|
    · exact Or.inl ha
    apply Or.inr
    have hd := average_common_shift_bound hn hf (fun i => m+a*g (some i)) (b*g none)
    have htri := abs_add_le
      ((∑ i : Fin n, f (m+a*g (some i)+b*g none))/(n:ℝ) - A g) (A g-M)
    have hrad : (K:ℝ)*|b*g none| = |(K:ℝ)*b*g none| := by
      simp [abs_mul, abs_of_nonneg K.coe_nonneg, mul_assoc]
    rw [hrad] at hd
    simp only [sub_add_sub_cancel] at htri
    change ε ≤ _ at hg
    change |(∑ i : Fin n, f (m+a*g (some i)+b*g none))/(n:ℝ) - A g| ≤ _ at hd
    have : |A g-M| < ε/2 := lt_of_not_ge ha
    change ε/2 ≤ |(K:ℝ)*b*g none|
    linarith
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  have h1 : standardArrayLaw (Option (Fin n)) {g | ε/2 ≤ |A g-M|} ≤
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(8*B^2))) := by
    convert ht using 1
    congr 3
    ring
  have h2 : standardArrayLaw (Option (Fin n)) {g | ε/2 ≤ |(K:ℝ)*b*g none|} ≤
      2 * ENNReal.ofReal (Real.exp (-ε^2/(8*(K:ℝ)^2*b^2))) := by
    convert hz using 1
    congr 3
    change -ε^2 / (8 * (K:ℝ)^2 * b^2) = -(ε / 2)^2 / (2 * ((((K:ℝ)*b)^2) * 1))
    ring
  exact add_le_add h1 h2

end SKGapCutoff.Regression

end

end OAI
