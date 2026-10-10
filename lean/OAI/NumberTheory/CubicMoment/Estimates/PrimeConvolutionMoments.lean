import OAI.NumberTheory.CubicMoment.Estimates.PrimeConvolutionBounds
import OAI.NumberTheory.CubicMoment.Estimates.UnrestrictedCubicSieve

namespace OAI

/-! Energy and actual character moments of fixed-length independent prime products. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primeConvolutionEnergy (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ) : ℝ :=
  ∏ i, ∑ p ∈ S i, ‖w i p‖^2

omit [DecidableEq ι] in
lemma primeConvolutionEnergy_nonneg (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) : 0 ≤ primeConvolutionEnergy S w :=
  Finset.prod_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Collecting ordered tuples loses at most their exact uniform fiber
bound, once, in the quadratic coefficient energy. -/
theorem orderedConvolution_energy_le (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) :
    (∑ b ∈ orderedConvolutionSupport S, ‖orderedConvolution S w b‖^2) ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*primeConvolutionEnergy S w := by
  let T := Fintype.piFinset S
  let W : (ι → Eisenstein) → ℂ := fun f => ∏ i, w i (f i)
  have hfiber (b : Eisenstein) :
      ‖orderedConvolution S w b‖^2 ≤
        ((Fintype.card ι)^(Fintype.card ι):ℕ)*
          ∑ f ∈ T with (∏ i, f i) = b, ‖W f‖^2 := by
    have hCS := complex_bilinear_rows_sq (T.filter (fun f => (∏ i, f i) = b))
      (fun _ => (1:ℂ)) W
    simp only [one_mul, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCS
    change ‖orderedConvolution S w b‖^2 ≤ _ at hCS
    apply hCS.trans
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (prime_tuple_fiber_card S hS b))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  calc
    _ ≤ ∑ b ∈ orderedConvolutionSupport S,
        ((Fintype.card ι)^(Fintype.card ι):ℕ)*
          ∑ f ∈ T with (∏ i, f i) = b, ‖W f‖^2 :=
      Finset.sum_le_sum (fun b _ => hfiber b)
    _ = ((Fintype.card ι)^(Fintype.card ι):ℕ)*∑ f ∈ T, ‖W f‖^2 := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_fiberwise_of_maps_to
        (fun f hf => Finset.mem_image_of_mem _ hf) _
    _ = _ := by
      congr 1
      simp only [W, norm_prod, ← Finset.prod_pow]
      exact (Finset.prod_univ_sum S (fun i p => ‖w i p‖^2)).symm

lemma orderedConvolution_twisted_energy_le (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (χ : Eisenstein → ℂ) (hχ : ∀ b ∈ orderedConvolutionSupport S, ‖χ b‖ ≤ 1) :
    (∑ b ∈ orderedConvolutionSupport S, ‖orderedConvolution S w b*χ b‖^2) ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*primeConvolutionEnergy S w := by
  apply le_trans _ (orderedConvolution_energy_le S w hS)
  apply Finset.sum_le_sum
  intro b hb
  rw [norm_mul]
  exact pow_le_pow_left₀ (mul_nonneg (_root_.norm_nonneg _) (_root_.norm_nonneg _))
    (mul_le_of_le_one_right (_root_.norm_nonneg _) (hχ b hb)) 2

def primeCubicProductPolynomial (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (a : Eisenstein) : ℂ :=
  ∏ i, ∑ p ∈ S i, w i p*cubicSymbol a p

lemma primeCubicProductPolynomial_eq (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) {a : Eisenstein} (ha : primary a) :
    primeCubicProductPolynomial S w a =
      ∑ b ∈ orderedConvolutionSupport S, orderedConvolution S w b*cubicSymbol a b := by
  have h := orderedConvolution_mixedCubic S w ha (by simp [primary] : primary 1)
  simpa only [mixedCubic, cubicSymbol_one_lower, star_one, mul_one,
    primeCubicProductPolynomial] using h.symm

/-- The actual product polynomial inherits the unrestricted cubic sieve
with the proved fixed-length coefficient energy. -/
theorem primeConvolution_cubic_moment {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → ∀ (P : Finset Eisenstein) (N Y : ℝ),
      1 ≤ N → 1 ≤ Y →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      (∑ a ∈ P, ‖primeCubicProductPolynomial S w a‖^2) ≤
        C*(N*Y)^ε*(N*Y^(1/3:ℝ)+(N*Y)^(2/3:ℝ)+Y^(4/3:ℝ)+Y)*
          (((Fintype.card ι)^(Fintype.card ι):ℕ)*primeConvolutionEnergy S w) := by
  obtain ⟨C,hC,hbound⟩ := unrestricted_cubic_sieve hε hε₁
  refine ⟨C,hC,?_⟩
  intro S w hS P N Y hN hY hP hprod
  have hH : ∀ b ∈ orderedConvolutionSupport S, b ≠ 0 ∧ norm b ≤ Y := by
    intro b hb
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
    refine ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => ?_),hprod f hf⟩
    exact (hS i (f i) (Fintype.mem_piFinset.mp hf i)).2.ne_zero
  have he : (∑ a ∈ P, ‖primeCubicProductPolynomial S w a‖^2) =
      ∑ a ∈ P, ‖∑ b ∈ orderedConvolutionSupport S,
        orderedConvolution S w b*cubicSymbol a b‖^2 := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [primeCubicProductPolynomial_eq S w (hP a ha).1]
  rw [he]
  apply (hbound P (orderedConvolutionSupport S) N Y hN hY hP hH
    (orderedConvolution S w)).trans
  exact mul_le_mul_of_nonneg_left (orderedConvolution_energy_le S w hS) (by positivity)

/-- Norm-at-most-one fixed coefficient twists cost nothing in this
moment estimate, whether or not they factor over the prime tuple. -/
theorem primeConvolution_twisted_cubic_moment {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ),
      (∀ i, ∀ p ∈ S i, primaryPrime p) → ∀ (P : Finset Eisenstein) (N Y : ℝ),
      1 ≤ N → 1 ≤ Y →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ f ∈ Fintype.piFinset S, norm (∏ i, f i) ≤ Y) →
      ∀ χ : Eisenstein → ℂ, (∀ b ∈ orderedConvolutionSupport S, ‖χ b‖ ≤ 1) →
      (∑ a ∈ P, ‖∑ b ∈ orderedConvolutionSupport S,
        (orderedConvolution S w b*χ b)*cubicSymbol a b‖^2) ≤
        C*(N*Y)^ε*(N*Y^(1/3:ℝ)+(N*Y)^(2/3:ℝ)+Y^(4/3:ℝ)+Y)*
          (((Fintype.card ι)^(Fintype.card ι):ℕ)*primeConvolutionEnergy S w) := by
  obtain ⟨C,hC,hbound⟩ := unrestricted_cubic_sieve hε hε₁
  refine ⟨C,hC,?_⟩
  intro S w hS P N Y hN hY hP hprod χ hχ
  have hH : ∀ b ∈ orderedConvolutionSupport S, b ≠ 0 ∧ norm b ≤ Y := by
    intro b hb
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
    refine ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => ?_),hprod f hf⟩
    exact (hS i (f i) (Fintype.mem_piFinset.mp hf i)).2.ne_zero
  apply (hbound P (orderedConvolutionSupport S) N Y hN hY hP hH
    (fun b => orderedConvolution S w b*χ b)).trans
  exact mul_le_mul_of_nonneg_left (orderedConvolution_twisted_energy_le S w hS χ hχ)
    (by positivity)

private lemma eisenstein_norm_finset_prod {κ : Type*} (s : Finset κ)
    (f : κ → Eisenstein) : norm (∏ i ∈ s, f i) = ∏ i ∈ s, norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [norm]
  | @insert i s hi ih => rw [Finset.prod_insert hi, norm_mul_eq, ih, Finset.prod_insert hi]

/-- Repeating one prime polynomial gives its actual `2k`-th character
moment, with coefficient energy `k^k` times the `k`-th power of its
original quadratic energy. -/
theorem primePolynomial_even_moment (k : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (w : Eisenstein → ℂ),
      (∀ p ∈ S, primaryPrime p) → ∀ (P : Finset Eisenstein) (N X : ℝ),
      1 ≤ N → 1 ≤ X →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ p ∈ S, norm p ≤ X) →
      (∑ a ∈ P, ‖∑ p ∈ S, w p*cubicSymbol a p‖^(2*k)) ≤
        C*(N*X^k)^ε*(N*(X^k)^(1/3:ℝ)+(N*X^k)^(2/3:ℝ)+(X^k)^(4/3:ℝ)+X^k)*
          ((k^k:ℕ)*(∑ p ∈ S, ‖w p‖^2)^k) := by
  obtain ⟨C,hC,hbound⟩ := primeConvolution_cubic_moment (ι := Fin k) hε hε₁
  refine ⟨C,hC,?_⟩
  intro S w hS P N X hN hX hP hnorm
  have hprod : ∀ f ∈ Fintype.piFinset (fun _ : Fin k => S),
      norm (∏ i, f i) ≤ X^k := by
    intro f hf
    rw [eisenstein_norm_finset_prod]
    calc
      _ ≤ ∏ _i : Fin k, X := Finset.prod_le_prod₀
        (fun i _ => norm_nonneg _) (fun i _ => hnorm _ (Fintype.mem_piFinset.mp hf i))
      _ = _ := by simp
  have h := hbound (fun _ : Fin k => S) (fun _ => w) (fun _ => hS)
    P N (X^k) hN (one_le_pow₀ hX) hP hprod
  have he (a : Eisenstein) :
      ‖primeCubicProductPolynomial (fun _ : Fin k => S) (fun _ => w) a‖^2 =
        ‖∑ p ∈ S, w p*cubicSymbol a p‖^(2*k) := by
    simp only [primeCubicProductPolynomial, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, norm_pow, ← pow_mul]
    congr 1
    omega
  simpa only [he, primeConvolutionEnergy, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using h

end CubicFirstMoment

end

end OAI
