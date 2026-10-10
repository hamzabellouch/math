import Mathlib
import OAI.Probability.SKGap.Localization.BilinearCoefficient
import OAI.Probability.SKGap.Localization.QueryResidual
import OAI.Probability.SKGap.Gaussian.SubgaussianAbsTail

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
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise NNReal ENNReal
namespace SKGapCutoff.Regression

noncomputable def gaussianRankCorrection {ι κ η : Type*} [Fintype κ] [Fintype η]
    (V : ι → κ → ℝ) (W : κ → η → ℝ) (g : η → ℝ) (i : ι) : ℝ :=
  ∑ a, V i a * ∑ j, W a j * g j

lemma rankCorrection_sq_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (V : ι → κ → ℝ) (c : κ → ℝ) (M : ℝ)
    (hV : ∀ a, ∑ i, V i a ^ 2 ≤ M) :
    ∑ i, (∑ a, V i a * c a)^2 ≤ M * Fintype.card κ * ∑ a, c a^2 := by
  calc
    _ ≤ ∑ i, (∑ a, V i a^2) * ∑ a, c a^2 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
    _ = (∑ a, ∑ i, V i a^2) * ∑ a, c a^2 := by
      rw [← Finset.sum_mul, Finset.sum_comm]
    _ ≤ (∑ _a : κ, M) * ∑ a, c a^2 := by
      exact mul_le_mul_of_nonneg_right (Finset.sum_le_sum (fun a _ => hV a))
        (Finset.sum_nonneg (fun a _ => sq_nonneg _))
    _ = _ := by simp [mul_comm]

lemma gaussian_linear_unit_tail {η : Type*} [Fintype η] (W : η → ℝ)
    (hW : ∑ j, W j^2 ≤ 1) (b : ℝ) (hb : 0 < b) :
    standardArrayLaw η {g | b ≤ |∑ j, W j * g j|} ≤
      2 * ENNReal.ofReal (Real.exp (-b^2/2)) := by
  have h := RandomMatrix.gaussian_linear_abs_tail 1 W b b hb
  refine h.trans (mul_le_mul' (le_refl 2) (ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr ?_)))
  simp only [NNReal.coe_one, one_mul]
  nlinarith [mul_le_mul_of_nonneg_right hW (sq_nonneg b)]

theorem gaussian_rank_correction_tail {ι κ η : Type*}
    [Fintype ι] [Fintype κ] [Fintype η] [Nonempty κ]
    (V : ι → κ → ℝ) (W : κ → η → ℝ)
    (hV : ∀ a, ∑ i, V i a^2 ≤ 2) (hW : ∀ a, ∑ j, W a j^2 ≤ 1)
    (N ε : ℝ) (hN : 0 < N) (hε : 0 < ε) :
    standardArrayLaw η {g | N*ε < ∑ i, gaussianRankCorrection V W g i^2} ≤
      (2 * Fintype.card κ : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-(N*ε)/(4*(Fintype.card κ : ℝ)^2))) := by
  classical
  let m : ℝ := Fintype.card κ
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card κ)
  let b : ℝ := Real.sqrt (N*ε/(2*m^2))
  have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
  have hb2 : b^2 = N*ε/(2*m^2) := Real.sq_sqrt (by positivity)
  have hsub : {g | N*ε < ∑ i, gaussianRankCorrection V W g i^2} ⊆
      ⋃ a : κ, {g | b ≤ |∑ j, W a j*g j|} := by
    intro g hg
    by_contra hnot
    have hcoeff (a : κ) : (∑ j, W a j*g j)^2 ≤ b^2 := by
      have ha : |∑ j, W a j*g j| < b := lt_of_not_ge
        (fun ha => hnot (Set.mem_iUnion.mpr ⟨a, ha⟩))
      nlinarith [sq_abs (∑ j, W a j*g j), abs_nonneg (∑ j, W a j*g j)]
    have he := rankCorrection_sq_bound V (fun a => ∑ j, W a j*g j) 2 hV
    have hs : (∑ a, (∑ j, W a j*g j)^2) ≤ m*b^2 := by
      calc
        _ ≤ ∑ _a : κ, b^2 := Finset.sum_le_sum (fun a _ => hcoeff a)
        _ = _ := by simp [m]
    have he' : ∑ i, gaussianRankCorrection V W g i^2 ≤ N*ε := by
      calc
        _ ≤ 2*m * ∑ a, (∑ j, W a j*g j)^2 := he
        _ ≤ 2*m*(m*b^2) := mul_le_mul_of_nonneg_left hs (by positivity)
        _ = _ := by rw [hb2]; field_simp
    exact not_lt_of_ge he' hg
  calc
    _ ≤ standardArrayLaw η (⋃ a : κ, {g | b ≤ |∑ j, W a j*g j|}) := measure_mono hsub
    _ ≤ ∑ a : κ, standardArrayLaw η {g | b ≤ |∑ j, W a j*g j|} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _a : κ, 2 * ENNReal.ofReal (Real.exp (-b^2/2)) :=
      Finset.sum_le_sum (fun a _ => gaussian_linear_unit_tail (W a) (hW a) b hb)
    _ = _ := by
      have hbexp : -b^2/2 = -(N*ε)/(4*(Fintype.card κ : ℝ)^2) := by
        rw [hb2]; dsimp [m]; ring
      rw [hbexp]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

noncomputable def innovationErrorVectors {n r : ℕ}
    (U : Matrix (Fin n) (Fin r) ℝ) (q : Fin n → ℝ) (i : Fin n) : Fin r ⊕ Bool → ℝ :=
  Sum.elim (fun a => -U i a) (fun b => if b then Real.sqrt 2*q i else -q i)

def innovationErrorCoefficients {n r : ℕ}
    (U : Matrix (Fin n) (Fin r) ℝ) (q : Fin n → ℝ) :
    (Fin r ⊕ Bool) → (Fin n ⊕ Unit) → ℝ :=
  Sum.elim (fun a => Sum.elim (fun j => U j a) (fun _ => 0))
    (fun b => if b then Sum.elim (fun _ => 0) (fun _ => 1)
      else Sum.elim q (fun _ => 0))

lemma innovationErrorVectors_sq_le {n r : ℕ}
    (U : Matrix (Fin n) (Fin r) ℝ) (q : Fin n → ℝ)
    (hU : ∀ a, ∑ i, U i a^2 ≤ 1) (hq : ∑ i, q i^2 ≤ 1)
    (a : Fin r ⊕ Bool) : ∑ i, innovationErrorVectors U q i a^2 ≤ 2 := by
  rcases a with a | (_ | _)
  · simpa [innovationErrorVectors] using (hU a).trans (by norm_num : (1:ℝ) ≤ 2)
  · simpa [innovationErrorVectors] using hq.trans (by norm_num : (1:ℝ) ≤ 2)
  · simp only [innovationErrorVectors, Sum.elim_inr, ↓reduceIte,
      mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), ← Finset.mul_sum]
    linarith

lemma innovationErrorCoefficients_sq_le {n r : ℕ}
    (U : Matrix (Fin n) (Fin r) ℝ) (q : Fin n → ℝ)
    (hU : ∀ a, ∑ i, U i a^2 ≤ 1) (hq : ∑ i, q i^2 ≤ 1)
    (a : Fin r ⊕ Bool) : ∑ j, innovationErrorCoefficients U q a j^2 ≤ 1 := by
  rcases a with a | (_ | _)
  · simpa [innovationErrorCoefficients, Fintype.sum_sum_type] using hU a
  · simpa [innovationErrorCoefficients, Fintype.sum_sum_type] using hq
  · simp [innovationErrorCoefficients, Fintype.sum_sum_type]

lemma queryInnovation_error_eq {n r : ℕ} (hn : 0 < n)
    (U : Matrix (Fin n) (Fin r) ℝ) (q : Fin n → ℝ)
    (g : (Fin n ⊕ Unit) → ℝ) (i : Fin n) :
    Real.sqrt n * queryInnovation (residualProjection U) q g i - g (Sum.inl i) =
      gaussianRankCorrection (innovationErrorVectors U q) (innovationErrorCoefficients U q) g i := by
  have hsn : Real.sqrt (n:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hh : ∑ k, (residualProjection U i k-q i*q k)*g (Sum.inl k) =
      g (Sum.inl i) - ∑ a, U i a * (∑ k, U k a*g (Sum.inl k)) -
        q i*(∑ k, q k*g (Sum.inl k)) := by
    simp only [residualProjection, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
      sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp [Matrix.one_apply, Finset.mul_sum]
  simp only [queryInnovation, queryComplement_apply]
  rw [mul_div_cancel₀ _ hsn, hh]
  simp only [gaussianRankCorrection, innovationErrorVectors, innovationErrorCoefficients,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_bool, Bool.false_eq_true,
    ↓reduceIte, zero_mul, one_mul, Finset.sum_const_zero, add_zero,
    Fintype.sum_unique, neg_mul, Finset.sum_neg_distrib]
  ring

theorem queryInnovation_iid_error_tail {n r : ℕ} (hn : 0 < n)
    (U : Matrix (Fin n) (Fin r) ℝ) (q : Fin n → ℝ)
    (hU : ∀ a, ∑ i, U i a^2 ≤ 1) (hq : ∑ i, q i^2 ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    standardArrayLaw (Fin n ⊕ Unit) {g | (n:ℝ)*ε < ∑ i,
      (Real.sqrt n * queryInnovation (residualProjection U) q g i - g (Sum.inl i))^2} ≤
      (2*(r+2) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-((n:ℝ)*ε)/(4*((r:ℝ)+2)^2))) := by
  simp_rw [queryInnovation_error_eq hn U q]
  have h := gaussian_rank_correction_tail (innovationErrorVectors U q)
    (innovationErrorCoefficients U q) (innovationErrorVectors_sq_le U q hU hq)
    (innovationErrorCoefficients_sq_le U q hU hq) n ε (Nat.cast_pos.mpr hn) hε
  simpa only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool, Nat.cast_add,
    Nat.cast_ofNat] using h

lemma probability_prod_section_bound {H A : Type*} [MeasurableSpace H] [MeasurableSpace A]
    (ρ : Measure H) [IsProbabilityMeasure ρ] (μ : Measure A) [SFinite μ]
    (s : Set (H × A)) (hs : MeasurableSet s) (b : ℝ≥0∞)
    (hb : ∀ h, μ (Prod.mk h ⁻¹' s) ≤ b) : (ρ.prod μ) s ≤ b := by
  rw [Measure.prod_apply hs]
  calc
    _ ≤ ∫⁻ _h, b ∂ρ := lintegral_mono hb
    _ = _ := by simp

theorem adaptive_queryInnovation_iid_error_tail {n r : ℕ} (hn : 0 < n)
    {H : Type*} [MeasurableSpace H] (ρ : Measure H) [IsProbabilityMeasure ρ]
    (U : H → Fin n → Fin r → ℝ) (q : H → Fin n → ℝ)
    (hUm : Measurable U) (hqm : Measurable q)
    (hU : ∀ h a, ∑ i, U h i a^2 ≤ 1) (hq : ∀ h, ∑ i, q h i^2 ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    (ρ.prod (standardArrayLaw (Fin n ⊕ Unit))) {z | (n:ℝ)*ε < ∑ i,
      (Real.sqrt n * queryInnovation (residualProjection (U z.1)) (q z.1) z.2 i - z.2 (Sum.inl i))^2} ≤
      (2*(r+2) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-((n:ℝ)*ε)/(4*((r:ℝ)+2)^2))) := by
  have hP : Measurable (fun h => fun i j => residualProjection (U h) i j) := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    change Measurable (fun h => (if i=j then (1:ℝ) else 0) - ∑ a, U h i a*U h j a)
    apply measurable_const.sub
    apply Finset.measurable_sum
    intro a _
    exact ((measurable_pi_apply a).comp ((measurable_pi_apply i).comp hUm)).mul
      ((measurable_pi_apply a).comp ((measurable_pi_apply j).comp hUm))
  have hI := measurable_queryInnovation_comp
    (fun z : H × ((Fin n ⊕ Unit) → ℝ) => residualProjection (U z.1))
    (fun z => q z.1) (fun z => z.2) (hP.comp measurable_fst)
    (hqm.comp measurable_fst) measurable_snd
  apply probability_prod_section_bound
  · apply measurableSet_lt measurable_const
    apply Finset.measurable_sum
    intro i _
    exact (((measurable_pi_apply i).comp hI).const_mul _ |>.sub
      ((measurable_pi_apply (Sum.inl i)).comp measurable_snd)).pow_const 2
  · intro h
    exact queryInnovation_iid_error_tail hn (U h) (q h) (hU h) (hq h) ε hε

lemma independent_bounded_average_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hXi : iIndepFun X μ)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 1) μ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ i z, |f i z| ≤ B) (ε : ℝ) (hε : 0 ≤ ε) :
    μ {g | ε ≤ |((∑ i, f i (X i g)) - ∑ i, ∫ z, f i z ∂gaussianReal 0 1)/(n:ℝ)|} ≤
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(2*B^2))) := by
  let m (i : Fin n) := ∫ z, f i z ∂gaussianReal 0 1
  have hi : iIndepFun (fun i (g : Ω) => f i (X i g)-m i) μ :=
    hXi.comp (fun i z => f i z-m i) (fun i => (hf i).sub_const (m i))
  have hm (i : Fin n) : (∫ g : Ω, f i (X i g) ∂μ) = m i :=
    (hX i).integral_comp (hf i).aestronglyMeasurable
  have hsub (i : Fin n) : HasSubgaussianMGF (fun g : Ω => f i (X i g)-m i)
      ((‖B-(-B)‖₊/2)^2) μ := by
    have hb : ∀ᵐ g : Ω ∂μ, f i (X i g) ∈ Set.Icc (-B) B :=
      Filter.Eventually.of_forall (fun g => abs_le.mp (hbound i (X i g)))
    simpa only [hm] using hasSubgaussianMGF_of_mem_Icc
      (show AEMeasurable (fun g : Ω => f i (X i g)) μ from
        (hf i).comp_aemeasurable (hX i).aemeasurable) hb
  have hh := subgaussian_abs_tail
    (HasSubgaussianMGF.sum_of_iIndepFun hi (s := Finset.univ) (fun i _ => hsub i))
    (ε*n) (by positivity)
  have he (g : Ω) :
      (ε*(n:ℝ) ≤ |∑ i, (f i (X i g)-m i)|) ↔
        ε ≤ |((∑ i, f i (X i g)) - ∑ i, m i)/(n:ℝ)| := by
    rw [Finset.sum_sub_distrib, abs_div, abs_of_pos (show (0:ℝ) < n from Nat.cast_pos.mpr hn)]
    exact (le_div_iff₀ (Nat.cast_pos.mpr hn)).symm
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

lemma average_Lipschitz_error_sq {n : ℕ} (hn : 0 < n)
    (f : Fin n → ℝ → ℝ) {K : ℝ≥0} (hf : ∀ i, LipschitzWith K (f i))
    (v w : Fin n → ℝ) :
    |((∑ i, f i (v i))-(∑ i, f i (w i)))/(n:ℝ)|^2 ≤
      (K:ℝ)^2 * (∑ i, (v i-w i)^2)/(n:ℝ) := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  rw [sq_abs, div_pow, ← Finset.sum_sub_distrib]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin n => (1:ℝ)) (fun i => f i (v i)-f i (w i))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  have hsite (i : Fin n) : (f i (v i)-f i (w i))^2 ≤ (K:ℝ)^2*(v i-w i)^2 := by
    have h := (hf i).dist_le_mul (v i) (w i)
    rw [Real.dist_eq, Real.dist_eq] at h
    have hs := mul_self_le_mul_self (abs_nonneg _) h
    simpa [← pow_two, mul_pow] using hs
  apply (div_le_iff₀ (sq_pos_of_pos hnR)).mpr
  calc
    _ ≤ (n:ℝ) * ∑ i, (f i (v i)-f i (w i))^2 := hcs
    _ ≤ (n:ℝ) * ∑ i, (K:ℝ)^2*(v i-w i)^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hsite i)) hnR.le
    _ = _ := by rw [← Finset.mul_sum]; field_simp

theorem queryInnovation_empirical_tail {n r : ℕ} (hn : 0 < n)
    (U : Matrix (Fin n) (Fin r) ℝ) (q : Fin n → ℝ)
    (hU : ∀ a, ∑ i, U i a^2 ≤ 1) (hq : ∑ i, q i^2 ≤ 1)
    (f : Fin n → ℝ → ℝ) {K : ℝ≥0} (hf : ∀ i, LipschitzWith K (f i))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ i z, |f i z| ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    standardArrayLaw (Fin n ⊕ Unit) {g | ε ≤
      |((∑ i, f i (Real.sqrt n * queryInnovation (residualProjection U) q g i)) -
        ∑ i, ∫ z, f i z ∂gaussianReal 0 1)/(n:ℝ)|} ≤
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(8*B^2))) +
      (2*(r+2) : ℝ≥0∞) * ENNReal.ofReal
        (Real.exp (-((n:ℝ)*ε^2)/(64*((K:ℝ)+1)^2*((r:ℝ)+2)^2))) := by
  let δ := ε^2/(16*((K:ℝ)+1)^2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  let M := ∑ i, ∫ z, f i z ∂gaussianReal 0 1
  let A (g : (Fin n ⊕ Unit) → ℝ) := ∑ i, f i (g (Sum.inl i))
  let C (g : (Fin n ⊕ Unit) → ℝ) :=
    ∑ i, f i (Real.sqrt n * queryInnovation (residualProjection U) q g i)
  let E (g : (Fin n ⊕ Unit) → ℝ) :=
    ∑ i, (Real.sqrt n * queryInnovation (residualProjection U) q g i-g (Sum.inl i))^2
  have hi : iIndepFun (fun i : Fin n => fun g : (Fin n ⊕ Unit) → ℝ => g (Sum.inl i))
      (standardArrayLaw (Fin n ⊕ Unit)) := coordinates_independent.precomp Sum.inl_injective
  have h1 := independent_bounded_average_tail (μ := standardArrayLaw (Fin n ⊕ Unit)) hn
    (fun i g => g (Sum.inl i)) hi (fun i => coordinate_hasLaw (Sum.inl i)) f
    (fun i => (hf i).continuous.measurable) B hB hbound (ε/2) (by positivity)
  have h2 := queryInnovation_iid_error_tail hn U q hU hq δ hδ
  have hsub : {g | ε ≤ |(C g-M)/(n:ℝ)|} ⊆
      {g | ε/2 ≤ |(A g-M)/(n:ℝ)|} ∪ {g | (n:ℝ)*δ < E g} := by
    intro g hg
    by_cases ha : ε/2 ≤ |(A g-M)/(n:ℝ)|
    · exact Or.inl ha
    apply Or.inr
    by_contra he
    have he' : E g ≤ (n:ℝ)*δ := le_of_not_gt he
    have hcs := average_Lipschitz_error_sq hn f hf
      (fun i => Real.sqrt n * queryInnovation (residualProjection U) q g i)
      (fun i => g (Sum.inl i))
    change |(C g-A g)/(n:ℝ)|^2 ≤ (K:ℝ)^2*E g/(n:ℝ) at hcs
    have hk : (K:ℝ)^2*δ ≤ ε^2/16 := by
      dsimp [δ]
      have hkp : 0 < ((K:ℝ)+1)^2 := by positivity
      apply (le_div_iff₀ (by norm_num : (0:ℝ)<16)).mpr
      field_simp
      have hkk : (K:ℝ)^2 ≤ ((K:ℝ)+1)^2 := by nlinarith [K.coe_nonneg]
      exact hkk
    have hsq : |(C g-A g)/(n:ℝ)|^2 ≤ ε^2/16 := hcs.trans
      ((calc
        (K:ℝ)^2*E g/(n:ℝ) ≤ (K:ℝ)^2*((n:ℝ)*δ)/(n:ℝ) := by gcongr
        _ = (K:ℝ)^2*δ := by field_simp).trans hk)
    have hd : |(C g-A g)/(n:ℝ)| ≤ ε/2 := by
      nlinarith [abs_nonneg ((C g-A g)/(n:ℝ))]
    have ht := abs_add_le ((C g-A g)/(n:ℝ)) ((A g-M)/(n:ℝ))
    rw [← add_div, sub_add_sub_cancel] at ht
    have ha' : |(A g-M)/(n:ℝ)| < ε/2 := lt_of_not_ge ha
    change ε ≤ |(C g-M)/(n:ℝ)| at hg
    linarith
  apply (measure_mono hsub).trans ((measure_union_le _ _).trans _)
  have h1' : standardArrayLaw (Fin n ⊕ Unit) {g | ε/2 ≤ |(A g-M)/(n:ℝ)|} ≤
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(8*B^2))) := by
    convert h1 using 1
    congr 3
    ring
  have h2' : standardArrayLaw (Fin n ⊕ Unit) {g | (n:ℝ)*δ < E g} ≤
      (2*(r+2) : ℝ≥0∞) * ENNReal.ofReal
        (Real.exp (-((n:ℝ)*ε^2)/(64*((K:ℝ)+1)^2*((r:ℝ)+2)^2))) := by
    convert h2 using 1
    congr 3
    dsimp [δ]
    field_simp
    ring
  exact add_le_add h1' h2'

lemma measurable_residualProjection_comp {n r : ℕ} {H : Type*} [MeasurableSpace H]
    (U : H → Fin n → Fin r → ℝ) (hU : Measurable U) :
    Measurable (fun h => fun i j => residualProjection (U h) i j) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  change Measurable (fun h => (if i=j then (1:ℝ) else 0) - ∑ a, U h i a*U h j a)
  apply measurable_const.sub
  apply Finset.measurable_sum
  intro a _
  exact ((measurable_pi_apply a).comp ((measurable_pi_apply i).comp hU)).mul
    ((measurable_pi_apply a).comp ((measurable_pi_apply j).comp hU))

theorem adaptive_queryInnovation_empirical_tail {n r : ℕ} (hn : 0 < n)
    {H : Type*} [MeasurableSpace H] (ρ : Measure H) [IsProbabilityMeasure ρ]
    (U : H → Fin n → Fin r → ℝ) (q : H → Fin n → ℝ)
    (hUm : Measurable U) (hqm : Measurable q)
    (hU : ∀ h a, ∑ i, U h i a^2 ≤ 1) (hq : ∀ h, ∑ i, q h i^2 ≤ 1)
    (f : H → Fin n → ℝ → ℝ) (hfm : ∀ i, Measurable (fun z : H × ℝ => f z.1 i z.2))
    {K : ℝ≥0} (hf : ∀ h i, LipschitzWith K (f h i))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ h i z, |f h i z| ≤ B) (ε : ℝ) (hε : 0 < ε) :
    (ρ.prod (standardArrayLaw (Fin n ⊕ Unit))) {z | ε ≤
      |((∑ i, f z.1 i (Real.sqrt n *
          queryInnovation (residualProjection (U z.1)) (q z.1) z.2 i)) -
        ∑ i, ∫ x, f z.1 i x ∂gaussianReal 0 1)/(n:ℝ)|} ≤
      2 * ENNReal.ofReal (Real.exp (-(ε^2*(n:ℝ))/(8*B^2))) +
      (2*(r+2) : ℝ≥0∞) * ENNReal.ofReal
        (Real.exp (-((n:ℝ)*ε^2)/(64*((K:ℝ)+1)^2*((r:ℝ)+2)^2))) := by
  have hI := measurable_queryInnovation_comp
    (fun z : H × ((Fin n ⊕ Unit) → ℝ) => residualProjection (U z.1))
    (fun z => q z.1) (fun z => z.2)
    ((measurable_residualProjection_comp U hUm).comp measurable_fst)
    (hqm.comp measurable_fst) measurable_snd
  have hM (i : Fin n) : Measurable (fun h => ∫ x, f h i x ∂gaussianReal 0 1) :=
    (hfm i).stronglyMeasurable.integral_prod_right.measurable
  apply probability_prod_section_bound
  · apply measurableSet_le measurable_const
    apply Measurable.abs
    apply Measurable.div_const
    apply Measurable.sub
    · apply Finset.measurable_sum
      intro i _
      exact (hfm i).comp (measurable_fst.prodMk (((measurable_pi_apply i).comp hI).const_mul _))
    · apply Finset.measurable_sum
      intro i _
      exact (hM i).comp measurable_fst
  · intro h
    exact queryInnovation_empirical_tail hn (U h) (q h) (hU h) (hq h)
      (f h) (hf h) B hB (hbound h) ε hε

end SKGapCutoff.Regression

open scoped BigOperators
open Filter Topology

end

end OAI
