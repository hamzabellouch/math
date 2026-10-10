import OAI.NumberTheory.Ostmann.Characters.SparsePrimeMean
import OAI.NumberTheory.Ostmann.Characters.SparseFiniteContraction

namespace OAI

/-! # A positive prime mean for the actual contracting weight -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

 theorem sparseWeightedPrimeSum_lower (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z)
    (P : PublishedSmoothExplicitFormula Z) (hPNT : PublishedSmoothPrincipalPNT)
    (C : ℝ) (hC : 1000 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∃ exception : Option PrimitiveComplexCharacter,
      ∀ (n : ℕ) (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
        (S : ∀ i, Finset (ZMod (p i))),
        Pairwise (fun i j => (p i).Coprime (p j)) →
        (∀ i, (S i).Nonempty) → (∀ i, (S i).card < p i) →
        (∀ i, (100 : ℝ) ≤ p i) →
        (∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i)) →
        (∀ i, residueDensity (S i) ≤ 2 / 3) →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 1000000 →
        (∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2) →
        (∑ i, (p i : ℝ)⁻¹) ≤ L →
        (∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L)) →
        (∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ i, p i) →
        let U := ∏ i, sparseKernelUnitFactor (p i)
          (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
        0 < U ∧ Real.exp (-L) ≤ U ∧ ((∫ t : ℝ, primeMeanTest t) / 4) * U * Real.exp (Real.exp L) ≤
          sparseWeightedPrimeSum p S (sparseTruncationDegree C L) (Real.exp (Real.exp L)) := by
  filter_upwards [sparseWeightedPrimeSum_decay Z hD hR P hPNT C 10 (by linarith),
    eventual_sparse_prime_error_margin (∫ t : ℝ, primeMeanTest t) primeMeanTest_integral_pos,
    eventual_sparse_prime_below_half, eventually_ge_atTop (1 : ℝ)] with L hmean hmargin hhalf hL
  obtain ⟨exception, he⟩ := hmean
  refine ⟨exception, ?_⟩
  intro n p hp hprod S hc hS hSp hp100 hlo hhi ε hε hεsmall hL1 hH hlog havoid U
  let K := sparseTruncationDegree C L
  let H := ∑ i, (p i : ℝ)⁻¹
  let E := fun i => largeTransformSpectrum (normalizedResidueTransform (S i))
  let X := Real.exp (Real.exp L)
  let I := ∫ t : ℝ, primeMeanTest t
  have hK : 1000 * L ≤ K :=
    (mul_le_mul_of_nonneg_right hC (by linarith)).trans (Nat.le_ceil _)
  obtain ⟨hU, hunit, _⟩ := sparse_finite_contraction p S hS hSp hp100 hlo hhi ε hε hεsmall
    hL1 L hL hH K hK
  have hspec (i) := normalizedResidueTransform_sparse (S i) (hS i) (hSp i)
    ε (ε ^ 2) (by nlinarith) le_rfl (hL1 i)
  have hlow := (sparse_unit_mass_range p E hp100 ε hε hεsmall
    (fun i => (hspec i).2.2.1)).1
  have hH0 : 0 ≤ H := Finset.sum_nonneg (fun _ _ => by positivity)
  have hucoarse : Real.exp (-L) ≤ U := by
    apply le_trans _ hlow
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (show 8 * ε ≤ 1 by linarith) hH0
    change _ ≤ -8 * ε * H
    dsimp [H] at hh ⊢
    linarith
  refine ⟨hU, hucoarse, ?_⟩
  have hm := he n p S hc (fun i => by linarith [hp100 i]) hH hlog
    (fun i => hhalf (p i) (Fact.out : (p i).Prime).one_le (hlog i)) havoid
  change |sparseWeightedPrimeSum p S K X - tensorRealUnitMean p (sparseSubsetWeight p S K) *
    (X * I)| ≤ 2 * X * Real.exp (-10 * L) at hm
  have herr : 2 * X * Real.exp (-10 * L) ≤ (I / 4) * U * X := by
    calc
      _ = (2 * Real.exp (-10 * L)) * X := by ring
      _ ≤ ((I / 4) * Real.exp (-L)) * X :=
        mul_le_mul_of_nonneg_right hmargin (Real.exp_nonneg _)
      _ ≤ (I / 4) * U * X := by
        gcongr
        exact div_nonneg primeMeanTest_integral_pos.le (by norm_num)
  have hbase := mul_le_mul_of_nonneg_right hunit
    (mul_nonneg (Real.exp_nonneg (Real.exp L)) primeMeanTest_integral_pos.le)
  have helo := (abs_le.mp hm).1
  change U / 2 * (X * I) ≤ _ at hbase
  nlinarith

end Ostmann

end OAI
