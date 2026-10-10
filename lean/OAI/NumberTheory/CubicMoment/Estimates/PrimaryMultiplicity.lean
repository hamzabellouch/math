import OAI.NumberTheory.CubicMoment.Estimates.SharpPrimaryMoments

namespace OAI

/-! Actual fixed multiplicities in the exceptional-moment argument. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private lemma prod_fixed_copies {M : Type*} [CommMonoid M]
    (k : ι → ℕ) (v : ι → M) :
    (∏ j : (Σ i, Fin (k i)), v j.1) = ∏ i, (v i)^(k i) := by
  rw [Fintype.prod_sigma]
  simp

private lemma fixed_copies_norm_bound (k : ι → ℕ)
    (S : ι → Finset Eisenstein) (X : ι → ℝ)
    (hSX : ∀ i, ∀ a ∈ S i, norm a ≤ X i)
    (f : (Σ i, Fin (k i)) → Eisenstein)
    (hf : f ∈ Fintype.piFinset (fun j : (Σ i, Fin (k i)) => S j.1)) :
    norm (∏ j, f j) ≤ ∏ i, (X i)^(k i) := by
  rw [norm_finset_prod]
  calc
    _ ≤ ∏ j : (Σ i, Fin (k i)), X j.1 := Finset.prod_le_prod₀
      (fun _ _ => norm_nonneg _)
      (fun j _ => hSX j.1 (f j) (Fintype.mem_piFinset.mp hf j))
    _ = _ := prod_fixed_copies k X

/-- Every fixed multiplicity vector gives the actual power product of
the primary polynomials, with the sharp cubic-sieve length factor. -/
theorem primaryPolynomial_multiplicity_moment (k : ι → ℕ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (M X : ι → ℝ),
      (∀ i, ∀ a ∈ S i, primary a) → (∀ i, 0 ≤ M i) →
      (∀ i, ∀ a ∈ S i, ‖w i a‖ ≤ M i) → (∀ i, 1 ≤ X i) →
      (∀ i, ∀ a ∈ S i, norm a ≤ X i) →
      ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ N →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∑ a ∈ P, ‖∏ i, (∑ n ∈ S i, w i n*cubicSymbol a n)^(k i)‖^2) ≤
        C*(N*(∏ i, (X i)^(k i)))^ε*(∏ i, (X i)^(k i))*
          (N+(∏ i, (X i)^(k i))+(N*(∏ i, (X i)^(k i)))^(2/3:ℝ))*
          ((∏ i, (X i)^(k i))^δ*(∏ i, (M i)^(k i))^2) := by
  obtain ⟨C,hC,hbound⟩ := primaryConvolution_sharp_product_moment
    (ι := Σ i, Fin (k i)) hε hδ
  refine ⟨C,hC,?_⟩
  intro S w M X hS hM hw hX hSX P N hN hP
  have hL : 1 ≤ ∏ i, (X i)^(k i) :=
    Finset.one_le_prod₀ (fun i _ => one_le_pow₀ (hX i))
  have h := hbound (fun j => S j.1) (fun j => w j.1) (fun j => M j.1)
    (fun j => hS j.1) (fun j => hM j.1) (fun j => hw j.1)
    P N (∏ i, (X i)^(k i)) hN hL hP
    (fixed_copies_norm_bound k S X hSX)
  simpa only [primeCubicProductPolynomial,Fintype.prod_sigma,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin] using h

/-- The same fixed copies in the ordinary mixed-character sieve retain
the exact product of quadratic factor energies. -/
theorem primaryPolynomial_mixed_multiplicity_moment
    (hHuxley : HuxleyAdditiveLargeSieve) (k : ι → ℕ)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : ι → Finset Eisenstein)
      (w : ι → Eisenstein → ℂ) (X : ι → ℝ),
      (∀ i, ∀ a ∈ S i, primary a) → (∀ i, 1 ≤ X i) →
      (∀ i, ∀ a ∈ S i, norm a ≤ X i) →
      ∀ (P : Finset (Eisenstein × Eisenstein)) (Q : ℝ), 1 ≤ Q →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∑ p ∈ P, ‖∏ i, (∑ n ∈ S i, w i n*mixedCubic p.1 p.2 n)^(k i)‖^2) ≤
        C*Q^ε*(Q^2+(∏ i, (X i)^(k i)))*
          ((∏ i, (X i)^(k i))^δ*(∏ i, (∑ n ∈ S i, ‖w i n‖^2)^(k i))) := by
  obtain ⟨C,hC,hbound⟩ := primaryConvolution_mixed_moment
    (ι := Σ i, Fin (k i)) hHuxley hε hδ
  refine ⟨C,hC,?_⟩
  intro S w X hS hX hSX P Q hQ hP
  have hL : 1 ≤ ∏ i, (X i)^(k i) :=
    Finset.one_le_prod₀ (fun i _ => one_le_pow₀ (hX i))
  have h := hbound (fun j => S j.1) (fun j => w j.1) (fun j => hS j.1)
    P Q (∏ i, (X i)^(k i)) hQ hL hP
    (fixed_copies_norm_bound k S X hSX)
  simpa only [primeConvolutionEnergy,Fintype.prod_sigma,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin] using h

end CubicFirstMoment

end

end OAI
