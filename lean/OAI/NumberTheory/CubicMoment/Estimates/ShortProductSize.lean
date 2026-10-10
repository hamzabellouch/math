import OAI.NumberTheory.CubicMoment.Estimates.SmoothShortFamily

namespace OAI

/-! A uniform trivial product bound used only to control Mellin tails. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem short_family_product_size :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ShortFactorFamily ι) (j : ℕ) (a b : Eisenstein),
      primary a → primary b →
      ‖∏ i, F.mixedValue j i (a,b)‖ ≤ C*(∏ i, F.length j i)^2 := by
  obtain ⟨K,hK,hbound⟩ := shortFactorPolynomial_norm_small_power (show (0:ℝ) < 1 by norm_num)
  refine ⟨K^(Fintype.card ι),pow_pos hK _,?_⟩
  intro F j a b ha hb
  have hi (i : ι) : ‖F.mixedValue j i (a,b)‖ ≤ K*(F.length j i)^2 := by
    have h := hbound (F.cutoff j) (F.length j i) (F.coefficient j i)
      (F.factor_spec j i) (F.length_ge_one j i)
      (fun n => F.twist j i n*mixedCubic a b n) (by
        intro n hn
        rw [norm_mul]
        exact (mul_le_mul (F.twist_bound j i n hn) (norm_mixedCubic_le_one ha hb n)
          (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
    simpa only [ShortFactorFamily.mixedValue,show (1+(1:ℝ)) = 2 by norm_num,
      Real.rpow_two] using h
  calc
    _ = ∏ i, ‖F.mixedValue j i (a,b)‖ := norm_prod _ _
    _ ≤ ∏ i, K*(F.length j i)^2 := Finset.prod_le_prod₀
      (fun _ _ => _root_.norm_nonneg _) (fun i _ => hi i)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.prod_pow,Finset.card_univ]

omit [DecidableEq ι] in
theorem smooth_short_product_size {D : ℝ} (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (W : ι → ℝ → ℂ)
      (t : ι → ℝ) (a b : Eisenstein),
      (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, q i ≠ 0) → (∀ i x, ‖W i x‖ ≤ 1) → (∀ i x, 2 < x → W i x = 0) →
      (∏ i, X i) ≤ D*Y → primary a → primary b →
      ‖∏ i, primaryShortSmoothSum (A i) a b (q i) (η i) (W i) (X i/2) (t i)‖ ≤ C*Y^2 := by
  obtain ⟨C,hC,hbound⟩ := short_family_product_size (ι := ι)
  refine ⟨C*D^2,mul_pos hC (sq_pos_of_pos hD),?_⟩
  intro F Y X A q η W t a b hA hX hq hW hcut hprod ha hb
  let K := shortFamilyOfSmoothWeights F X A q η W t hA hX hq hW
  have h := hbound K 0 a b ha hb
  simp only [K,smoothShortFamily_mixedValue F X A q η W t hA hX hq hW hcut] at h
  apply h.trans
  have hp := pow_le_pow_left₀ (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hX i))) hprod 2
  calc
    _ ≤ C*(D*Y)^2 := mul_le_mul_of_nonneg_left hp hC.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
