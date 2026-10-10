import OAI.NumberTheory.CubicMoment.Decomposition.PrimeProductPolynomialBounds
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryPrimeUpper

namespace OAI

/-! The prime-counting savings in the actual coefficients of an
exceptional triple. These are consequences of the ordinary prime PNT;
no moment estimate for the new paper is assumed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_subset_primeCutoff (R : ℝ) (W : ι → ℝ → ℂ)
    (X : ι → ℝ) (i : ι) : fullPrimeSupport R W X i ⊆ primeCutoff (R*X i) := by
  intro p hp
  obtain ⟨hpre,hq⟩ := Finset.mem_filter.mp hp
  obtain ⟨hb,_hw⟩ := Finset.mem_filter.mp hpre
  exact mem_primeCutoff.mpr ⟨⟨(mem_primaryElementBall.mp hb).1,hq⟩,
    (mem_primaryElementBall.mp hb).2⟩

lemma fullSquarefreePrimeSupport_card_le_product (R : ℝ) (W : ι → ℝ → ℂ)
    (X : ι → ℝ) (e : Eisenstein) :
    ((fullSquarefreePrimeSupport R W X e).card:ℝ) ≤
      ∏ i, ((fullPrimeSupport R W X i).card:ℝ) := by
  calc
    _ ≤ ((orderedConvolutionSupport (fullPrimeSupport R W X)).card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    _ ≤ ((Fintype.piFinset (fullPrimeSupport R W X)).card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_image_le)
    _ = _ := by rw [Fintype.card_piFinset,Nat.cast_prod]

omit [Fintype ι] [DecidableEq ι] in
theorem fullPrimeSupport_card_log_bound (hpnt : PrimaryPrimePNT) {R : ℝ} (hR : 1 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ (W : ι → ℝ → ℂ) (X : ι → ℝ) (L : ℝ),
      0 < L → (∀ i, 2 ≤ X i) → (∀ i, L ≤ Real.log (X i)) →
      ∀ i, ((fullPrimeSupport R W X i).card:ℝ) ≤ K*X i/L := by
  obtain ⟨C,hC,hcount⟩ := primaryPrimeCount_upper hpnt
  refine ⟨C*R,mul_pos hC (zero_lt_one.trans_le hR),?_⟩
  intro W X L hL hX hlog i
  have hXp : 0 < X i := lt_of_lt_of_le (by norm_num) (hX i)
  have hRX : 2 ≤ R*X i := (hX i).trans
    (le_mul_of_one_le_left hXp.le hR)
  have hlogRX : L ≤ Real.log (R*X i) := (hlog i).trans
    (Real.log_le_log hXp (le_mul_of_one_le_left hXp.le hR))
  calc
    _ ≤ primaryPrimeCount (R*X i) := Nat.cast_le.mpr
      (Finset.card_le_card (fullPrimeSupport_subset_primeCutoff R W X i))
    _ ≤ C*(R*X i)/Real.log (R*X i) := hcount _ hRX
    _ ≤ C*(R*X i)/L := div_le_div_of_nonneg_left (by positivity) hL hlogRX
    _ = _ := by ring

theorem fullPrimeCoefficient_sharp_moments (hpnt : PrimaryPrimePNT)
    {R : ℝ} (hR : 1 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ (W : ι → ℝ → ℂ) (X : ι → ℝ) (L : ℝ),
      0 < L → (∀ i, 2 ≤ X i) → (∀ i, L ≤ Real.log (X i)) →
      (∀ i x, ‖W i x‖ ≤ 1) → ∀ e : Eisenstein,
      (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖) ≤
          K*(∏ i, X i)/L^(Fintype.card ι) ∧
      (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖^2) ≤
          K*(∏ i, X i)/L^(Fintype.card ι) := by
  obtain ⟨C,hC,hcard⟩ := fullPrimeSupport_card_log_bound (ι := ι) hpnt hR
  let n := Fintype.card ι
  let M : ℝ := (n^n:ℕ)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  refine ⟨(M+1)^2*C^n,by positivity,?_⟩
  intro W X L hL hX hlog hW e
  have hbound (b : Eisenstein) : ‖fullPrimeCoefficient R W X b‖ ≤ M := by
    simpa only [M,n,Finset.prod_const,Finset.card_univ,one_pow,mul_one] using
      fullPrimeCoefficient_norm_bound R W X (fun _ => 1) (fun _ => zero_le_one) hW b
  have hcount : ((fullSquarefreePrimeSupport R W X e).card:ℝ) ≤
      C^n*(∏ i, X i)/L^n := by
    apply (fullSquarefreePrimeSupport_card_le_product R W X e).trans
    apply (Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
      (fun i _ => hcard W X L hL hX hlog i)).trans_eq
    simp only [Finset.prod_div_distrib,Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_univ,n]
  have hrow (b : Eisenstein) : ‖fullPrimeCoefficient R W X b‖ ≤ (M+1)^2 ∧
      ‖fullPrimeCoefficient R W X b‖^2 ≤ (M+1)^2 := by
    constructor
    · exact (hbound b).trans (by nlinarith)
    · exact (pow_le_pow_left₀ (_root_.norm_nonneg _) (hbound b) 2).trans (by nlinarith)
  constructor
  · calc
      _ ≤ ∑ b ∈ fullSquarefreePrimeSupport R W X e, (M+1)^2 :=
        Finset.sum_le_sum (fun b _ => (hrow b).1)
      _ = ((fullSquarefreePrimeSupport R W X e).card:ℝ)*(M+1)^2 := by simp
      _ ≤ (C^n*(∏ i, X i)/L^n)*(M+1)^2 :=
        mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
      _ = _ := by ring
  · calc
      _ ≤ ∑ b ∈ fullSquarefreePrimeSupport R W X e, (M+1)^2 :=
        Finset.sum_le_sum (fun b _ => (hrow b).2)
      _ = ((fullSquarefreePrimeSupport R W X e).card:ℝ)*(M+1)^2 := by simp
      _ ≤ (C^n*(∏ i, X i)/L^n)*(M+1)^2 :=
        mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
      _ = _ := by ring

theorem fullPrimeCoefficient_power_scale_moments (hpnt : PrimaryPrimePNT)
    {R c : ℝ} (hR : 1 ≤ R) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Y : ℝ in Filter.atTop,
      ∀ (W : ι → ℝ → ℂ) (X : ι → ℝ), (∀ i, Y^c ≤ X i) →
      (∀ i x, ‖W i x‖ ≤ 1) → ∀ e : Eisenstein,
      (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖) ≤
          K*(∏ i, X i)/(1+Real.log Y)^(Fintype.card ι) ∧
      (∑ b ∈ fullSquarefreePrimeSupport R W X e, ‖fullPrimeCoefficient R W X b‖^2) ≤
          K*(∏ i, X i)/(1+Real.log Y)^(Fintype.card ι) := by
  obtain ⟨C,hC,hbound⟩ := fullPrimeCoefficient_sharp_moments (ι := ι) hpnt hR
  refine ⟨C/(c/2)^(Fintype.card ι),by positivity,?_⟩
  filter_upwards [(tendsto_rpow_atTop hc).eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_gt_atTop (0:ℝ)] with Y hYc hlogY hY
  intro W X hX hW e
  have hXi : ∀ i, 2 ≤ X i := fun i => hYc.trans (hX i)
  have hL : 0 < 1+Real.log Y := by linarith
  have hlog (i : ι) : (c/2)*(1+Real.log Y) ≤ Real.log (X i) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hY c) (hX i)
    rw [Real.log_rpow hY] at hh
    nlinarith
  have hh := hbound W X ((c/2)*(1+Real.log Y)) (by positivity) hXi hlog hW e
  have he : C*(∏ i, X i)/((c/2)*(1+Real.log Y))^(Fintype.card ι) =
      (C/(c/2)^(Fintype.card ι))*(∏ i, X i)/(1+Real.log Y)^(Fintype.card ι) := by
    rw [mul_pow]
    ring
  exact ⟨hh.1.trans_eq he,hh.2.trans_eq he⟩

end CubicFirstMoment

end

end OAI
