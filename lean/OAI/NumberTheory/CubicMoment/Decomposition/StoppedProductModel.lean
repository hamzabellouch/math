import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductMean
import OAI.NumberTheory.CubicMoment.Estimates.CenteredProductMellin

namespace OAI

/-! Exact collection of the product squarefree model and its ordinary
height mean for the actual stopped outer coefficient. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def squarefreeProductModel (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) : ℂ :=
  ∑ a ∈ P, ∑ b ∈ B, if Squarefree (a*b) then
    α a*β b*normTwist u (a*b)*((norm (a*b)^(-1/6:ℝ):ℝ):ℂ) else 0

lemma squarefreeProductModel_collection (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) :
    squarefreeProductModel P B α β u =
      dispersionModel (squarefreePairSupport P B)
        (primaryPairCoefficient P B (fun p => α p.1*β p.2)) u := by
  rw [dispersionModel]
  simpa only [squarefreeProductModel,mul_assoc] using
    (squarefree_pair_sum P B α β (fun n =>
      normTwist u n*((norm n^(-1/6:ℝ):ℝ):ℂ))).symm

lemma continuous_squarefreeProductModel (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) :
    Continuous (fun t => squarefreeProductModel P B α β (t+u)) := by
  unfold squarefreeProductModel
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  split_ifs
  · exact (continuous_const.mul ((continuous_normTwist (a*b)).comp
      (continuous_id.add continuous_const))).mul continuous_const
  · exact continuous_const

lemma centered_product_eq_gauss_sub_model (P B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (u : ℝ) :
    centeredProductPolynomial P B α β 0 u =
      (∑ a ∈ P, ∑ b ∈ B, α a*β b*gauss (a*b)*normTwist u (a*b))-
        (cStar:ℂ)*squarefreeProductModel P B α β u := by
  simp only [centeredProductPolynomial,theta_zero, mul_one,
    squarefreeProductModel,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [centeredGauss,idealMoebius_sq_complex]
  by_cases hs : Squarefree (a*b)
  · simp only [ite_eq_left hs]
    ring
  · simp only [ite_eq_right hs,mul_zero,zero_mul,sub_zero]

lemma divisor_model_norm_bound (S : Finset Eisenstein) (γ : Eisenstein → ℂ)
    {X M : ℝ} (hX : 0 < X) (hM : 0 ≤ M)
    (hS : ∀ n ∈ S, X ≤ norm n)
    (hγ : ∀ n ∈ S, ‖γ n‖ ≤ M*(4:ℝ)^(primaryPrimeFactors n).card) (u : ℝ) :
    ‖dispersionModel S γ u‖ ≤
      M*X^(-1/6:ℝ)*(∑ n ∈ S, (4:ℝ)^(primaryPrimeFactors n).card) := by
  unfold dispersionModel
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul,norm_mul,norm_normTwist,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg n) _)]
  calc
    _ ≤ (M*(4:ℝ)^(primaryPrimeFactors n).card)*X^(-1/6:ℝ) :=
      mul_le_mul (hγ n hn)
        (Real.rpow_le_rpow_of_nonpos hX (hS n hn) (by norm_num))
        (Real.rpow_nonneg (norm_nonneg n) _) (by positivity)
    _ = _ := by ring

theorem stopped_product_model_norm (hpnt : PrimaryPrimePNT) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (E U P B : Finset Eisenstein)
      (ψ : ℝ → ℝ) (w : ℝ) (remaining : Eisenstein → Prop)
      (β : Eisenstein → ℂ) (X Y M u : ℝ),
      (∀ e ∈ E, primary e) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      Real.exp 1 ≤ Y → 0 < X → 0 ≤ M →
      (∀ a ∈ P, primary a) → (∀ b ∈ B, primary b) →
      (∀ a ∈ P, ∀ b ∈ B, X ≤ norm (a*b) ∧ norm (a*b) ≤ Y) →
      (∀ b ∈ B, ‖β b‖ ≤ M) →
      ‖squarefreeProductModel P B (stoppedAlpha E U ψ w remaining) β u‖ ≤
        K*M*Y*X^(-1/6:ℝ)*(1+Real.log Y)^d := by
  obtain ⟨K,d,hK,hmoment⟩ := squarefree_fixed_divisor_moment hpnt 4 (by norm_num)
  refine ⟨K,d,hK,?_⟩
  intro E U P B ψ w remaining β X Y M u hE hψ hY hX hM hP hB hnorm hβ
  let S := squarefreePairSupport P B
  let γ := primaryPairCoefficient P B (fun p => stoppedAlpha E U ψ w remaining p.1*β p.2)
  have hS (n : Eisenstein) (hn : n ∈ S) :
      primary n ∧ Squarefree n ∧ X ≤ norm n ∧ norm n ≤ Y := by
    have hs := squarefreePairSupport_primary P B hP hB hn
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hn).1
    have hm := Finset.mem_product.mp hp
    exact ⟨hs.1,hs.2,he ▸ (hnorm p.1 hm.1 p.2 hm.2)⟩
  have hγ : ∀ n ∈ S, ‖γ n‖ ≤ M*(4:ℝ)^(primaryPrimeFactors n).card := by
    intro n hn
    exact stopped_pair_coefficient_bound E U P B ψ w remaining β hM hE hP hψ hβ
      (hS n hn).1 (hS n hn).2.1
  rw [squarefreeProductModel_collection]
  apply (divisor_model_norm_bound S γ hX hM (fun n hn => (hS n hn).2.2.1) hγ u).trans
  calc
    _ ≤ M*X^(-1/6:ℝ)*(K*Y*(1+Real.log Y)^d) :=
      mul_le_mul_of_nonneg_left (hmoment Y S hY
        (fun n hn => ⟨(hS n hn).1,(hS n hn).2.1,(hS n hn).2.2.2⟩)) (by positivity)
    _ = _ := by ring

theorem stopped_product_model_height_mean (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (E U P B : Finset Eisenstein)
      (ψ : ℝ → ℝ) (w : ℝ) (remaining : Eisenstein → Prop)
      (β : Eisenstein → ℂ) (N : ℕ) (X T M u : ℝ),
      (∀ e ∈ E, primary e) → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      Real.exp 1 ≤ (N:ℝ) → 0 < X → 0 < T → 0 ≤ M →
      (∀ a ∈ P, primary a) → (∀ b ∈ B, primary b) →
      (∀ a ∈ P, ∀ b ∈ B, X ≤ norm (a*b) ∧ norm (a*b) ≤ (N:ℝ)) →
      (∀ b ∈ B, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t =>
        ‖squarefreeProductModel P B (stoppedAlpha E U ψ w remaining) β (t+u)‖^2) T ≤
        K*M^2*(1+(N:ℝ)/T)*(N:ℝ)*X^(-1/3:ℝ)*(1+Real.log N)^d := by
  obtain ⟨K,d,hK,hmean⟩ := divisor_model_height_mean hpnt hMV hC
  refine ⟨K,d,hK,?_⟩
  intro E U P B ψ w remaining β N X T M u hE hψ hN hX hT hM hP hB hn hβ
  simp_rw [squarefreeProductModel_collection]
  apply hmean _ _ N X T M u hN hX hT hM
  · intro n hns
    have hs := squarefreePairSupport_primary P B hP hB hns
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hns).1
    have hm := Finset.mem_product.mp hp
    exact ⟨hs.1,hs.2,he ▸ (hn p.1 hm.1 p.2 hm.2)⟩
  · intro n hn
    have hs := squarefreePairSupport_primary P B hP hB hn
    exact stopped_pair_coefficient_bound E U P B ψ w remaining β hM hE hP hψ hβ hs.1 hs.2

end CubicFirstMoment

end

end OAI
