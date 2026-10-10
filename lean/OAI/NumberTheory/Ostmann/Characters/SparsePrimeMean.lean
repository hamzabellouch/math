import OAI.NumberTheory.Ostmann.Characters.SparsePrimeIdentity
import OAI.NumberTheory.Ostmann.ZeroDensity.SparsePrincipalMean
import OAI.NumberTheory.Ostmann.Characters.SparseExpandedMean
import OAI.NumberTheory.Ostmann.Construction.PrimePowerDecayRate

namespace OAI

/-! # The prime-weighted mean of the actual sparse subset weight -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def sparseWeightedPrimeSum {n : ℕ} (p : Fin n → ℕ)
    [∀ i, NeZero (p i)] (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (X : ℝ) : ℝ :=
  ∑ q ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
    Real.log q * sparseSubsetWeight p S K (fun i => (q : ZMod (p i))) * primeMeanTest (q / X)

 theorem sparseWeightedPrimeSum_decay (Z : ∀ χ, ComplexZeroEnumeration χ)
    (hD : PublishedComplexZeroDensity Z) (hR : PublishedComplexZeroRegion Z)
    (P : PublishedSmoothExplicitFormula Z) (hPNT : PublishedSmoothPrincipalPNT)
    (C D : ℝ) (hC : 0 < C) :
    ∀ᶠ L : ℝ in atTop, ∃ exception : Option PrimitiveComplexCharacter,
      ∀ (n : ℕ) (p : Fin n → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
        (S : ∀ i, Finset (ZMod (p i))),
        Pairwise (fun i j => (p i).Coprime (p j)) →
        (∀ i, (36 : ℝ) ≤ p i) → (∑ i, (p i : ℝ)⁻¹) ≤ L →
        (∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L)) →
        (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp L) / 2) →
        (∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ i, p i) →
        |sparseWeightedPrimeSum p S (sparseTruncationDegree C L) (Real.exp (Real.exp L)) -
          tensorRealUnitMean p (sparseSubsetWeight p S (sparseTruncationDegree C L)) *
            (Real.exp (Real.exp L) * ∫ t : ℝ, primeMeanTest t)| ≤
          2 * Real.exp (Real.exp L) * Real.exp (-D * L) := by
  filter_upwards [sparseExpandedMangoldtMean_decay Z hD hR P hPNT C D hC,
    eventual_prime_power_error (2 * C + 3) 6 D (by linarith),
    eventually_ge_atTop (1 : ℝ)] with L hmean hpp hL
  obtain ⟨exception, he⟩ := hmean
  refine ⟨exception, ?_⟩
  intro n p hp hprod S hc hp36 hmass hlog hbound havoid
  let E := fun i => largeTransformSpectrum (normalizedResidueTransform (S i))
  let K := sparseTruncationDegree C L
  let X := Real.exp (Real.exp L)
  let F := (sparsePrimitiveSupport p E (17 / 20) K).eraseNone
  let c := fun ρ => sparsePrimitiveCoefficient p E (17 / 20) K (some ρ)
  let c₀ := sparsePrimitiveCoefficient p E (17 / 20) K none
  have hE (i) : 0 ∉ E i :=
    largeTransformSpectrum_zero_not_mem _ (normalizedResidueTransform_zero (S i))
  have hsym (i) : ∀ b, -b ∈ E i ↔ b ∈ E i :=
    largeTransformSpectrum_neg _ (normalizedResidueTransform_neg (S i))
  have hcoeff (e : Option PrimitiveComplexCharacter) :
      ‖sparsePrimitiveCoefficient p E (17 / 20) K e‖ ≤ Real.exp (6 * L) := by
    exact (sparsePrimitiveCoefficient_norm_le p E hE hsym (17 / 20) (by norm_num)
      (by norm_num) hp36 K e).trans (Real.exp_le_exp.mpr (by linarith))
  have hQ (ρ) (hρ : ρ ∈ F) : ρ.modulus ≤ sparseConductorCutoff C L :=
    sparsePrimitiveSupport_modulus_le p E C L (17 / 20) hlog ρ hρ
  have hX : 1 ≤ X := Real.one_le_exp (Real.exp_nonneg L)
  have hA := he n p E (17 / 20) hE hsym (by norm_num) (by norm_num) hp36 hmass hlog havoid
  have hB := character_prime_power_error_of_conductor F c c₀ X (Real.exp (6 * L)) hX
    (Real.exp_nonneg _) (hcoeff none) (fun ρ _ => hcoeff (some ρ))
    (sparseConductorCutoff C L) hQ
  have hrate := hpp (sparseConductorCutoff C L) (sparseConductorCutoff_pos C L)
    (sparseConductorCutoff_log_upper C L hC.le hL)
  have hid := sparsePrimeSum_identity p hc S K X (Real.exp_pos _) hbound
  change smoothPrimeSum (primitiveCharacterPolynomial F c c₀) X =
    (sparseWeightedPrimeSum p S K X : ℂ) at hid
  have hcmean := sparsePrimitiveCoefficient_real_mean p hc S K
  have hmain : c₀ * smoothPrincipalMain X =
      ((tensorRealUnitMean p (sparseSubsetWeight p S K) *
        (X * ∫ t : ℝ, primeMeanTest t) : ℝ) : ℂ) := by
    rw [show c₀ = _ from hcmean]
    simp only [smoothPrincipalMain, Complex.ofReal_mul]
  have htri := (norm_sub_le_norm_sub_add_norm_sub (smoothPrimeSum (primitiveCharacterPolynomial F c c₀) X)
    (sparseExpandedMangoldtMean p E (17 / 20) K X) (c₀ * smoothPrincipalMain X)).trans
      (add_le_add (by simpa only [norm_sub_rev, sparseExpandedMangoldtMean, F, c, c₀] using hB.trans hrate) hA)
  rw [hid, hmain, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at htri
  convert htri using 1
  ring

end Ostmann

end OAI
