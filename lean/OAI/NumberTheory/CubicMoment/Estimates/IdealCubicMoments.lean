import OAI.NumberTheory.CubicMoment.Estimates.HeckeDualMoment
import OAI.NumberTheory.CubicMoment.Estimates.SharpPrimaryMoments

namespace OAI

/-! The proved element sieves apply directly to complete ideal-indexed
polynomials through the injective chosen-generator map. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma sum_ideal_generator_image (S : Finset EisensteinIdealExponent)
    (f : EisensteinIdealExponent → Eisenstein → ℂ) :
    (∑ n ∈ S.image idealExponentGenerator, f (idealExponentOf n) n) =
      ∑ ν ∈ S, f ν (idealExponentGenerator ν) := by
  rw [Finset.sum_image (fun ν _ κ _ h => idealExponentGenerator_injective h)]
  simp only [idealExponentOf_generator]

/-- Cubic moments for complete ideal supports, including the prime above 3. -/
theorem ideal_cubic_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (S : Finset EisensteinIdealExponent)
      (N Y D : ℝ), 1 ≤ N → 1 ≤ Y → 0 ≤ D →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ ν ∈ S, idealExponentNorm ν ≤ Y) → ∀ v : EisensteinIdealExponent → ℂ,
      (∀ ν ∈ S, ‖v ν‖ ≤ D) →
      (∑ a ∈ P, ‖∑ ν ∈ S, v ν*cubicSymbol a (idealExponentGenerator ν)‖^2) ≤
        C*(N*Y)^ε*Y*(N+Y+(N*Y)^(2/3:ℝ))*D^2 := by
  obtain ⟨C,hC,hbound⟩ := bounded_cubic_moment hε
  refine ⟨C,hC,?_⟩
  intro P S N Y D hN hY hD hP hS v hv
  have hsupport : ∀ n ∈ S.image idealExponentGenerator, n ≠ 0 ∧ norm n ≤ Y := by
    intro n hn
    obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hn
    exact ⟨idealExponentGenerator_ne_zero ν,by simpa only [idealExponentNorm,normNat_cast] using hS ν hν⟩
  have hv' : ∀ n ∈ S.image idealExponentGenerator, ‖v (idealExponentOf n)‖ ≤ D := by
    intro n hn
    obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hn
    simpa only [idealExponentOf_generator] using hv ν hν
  have h := hbound P (S.image idealExponentGenerator) N Y D hN hY hD hP hsupport
    (fun n => v (idealExponentOf n)) hv'
  have hsum (a : Eisenstein) :
      (∑ n ∈ S.image idealExponentGenerator, v (idealExponentOf n)*cubicSymbol a n) =
        ∑ ν ∈ S, v ν*cubicSymbol a (idealExponentGenerator ν) :=
    sum_ideal_generator_image S (fun ν n => v ν*cubicSymbol a n)
  simpa only [hsum] using h

/-- The ordinary mixed-character moment keeps its exact ideal coefficient energy. -/
theorem ideal_mixed_moment (hHuxley : HuxleyAdditiveLargeSieve)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset (Eisenstein × Eisenstein))
      (S : Finset EisensteinIdealExponent) (Q Y : ℝ), 1 ≤ Q → 1 ≤ Y →
      (∀ p ∈ P, PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ Q) →
      (∀ ν ∈ S, idealExponentNorm ν ≤ Y) → ∀ v : EisensteinIdealExponent → ℂ,
      (∑ p ∈ P, ‖∑ ν ∈ S, v ν*mixedCubic p.1 p.2 (idealExponentGenerator ν)‖^2) ≤
        C*Q^ε*(Q^2+Y)*∑ ν ∈ S, ‖v ν‖^2 := by
  obtain ⟨C,hC,hbound⟩ := ordinary_mixed_cubic_sieve_finite hHuxley hε
  refine ⟨C,hC,?_⟩
  intro P S Q Y hQ hY hP hS v
  have hsupport : ∀ n ∈ S.image idealExponentGenerator, n ≠ 0 ∧ norm n ≤ Y := by
    intro n hn
    obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hn
    exact ⟨idealExponentGenerator_ne_zero ν,by simpa only [idealExponentNorm,normNat_cast] using hS ν hν⟩
  have h := hbound Q Y hQ hY P (S.image idealExponentGenerator) hP hsupport
    (fun n => v (idealExponentOf n))
  have hsum (p : Eisenstein × Eisenstein) :
      (∑ n ∈ S.image idealExponentGenerator, v (idealExponentOf n)*mixedCubic p.1 p.2 n) =
        ∑ ν ∈ S, v ν*mixedCubic p.1 p.2 (idealExponentGenerator ν) :=
    sum_ideal_generator_image S (fun ν n => v ν*mixedCubic p.1 p.2 n)
  simp_rw [hsum] at h
  have he : (∑ n ∈ S.image idealExponentGenerator, ‖v (idealExponentOf n)‖^2) =
      ∑ ν ∈ S, ‖v ν‖^2 := by
    rw [Finset.sum_image (fun ν _ κ _ h => idealExponentGenerator_injective h)]
    simp only [idealExponentOf_generator]
  rw [he] at h
  exact h

lemma normalizedDualPolynomial_cubic (S : Finset EisensteinIdealExponent)
    (a : Eisenstein) (J u : ℝ) :
    normalizedDualPolynomial S (fun ν => cubicSymbol a (idealExponentGenerator ν))
      idealExponentNorm J u =
      ∑ ν ∈ S, (((J/idealExponentNorm ν)^(1/2:ℝ):ℝ)*mellinPhase u (idealExponentNorm ν))*
        cubicSymbol a (idealExponentGenerator ν) := by
  unfold normalizedDualPolynomial
  apply Finset.sum_congr rfl
  intro ν hν
  ring

/-- Normalized cubic dual blocks have coefficients bounded by one,
uniformly in their additional norm twist. -/
theorem normalized_ideal_cubic_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (S : Finset EisensteinIdealExponent)
      (N Y J u : ℝ), 1 ≤ N → 1 ≤ Y → 0 < J →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ ν ∈ S, J ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ Y) →
      (∑ a ∈ P, ‖normalizedDualPolynomial S
        (fun ν => cubicSymbol a (idealExponentGenerator ν)) idealExponentNorm J u‖^2) ≤
        C*(N*Y)^ε*Y*(N+Y+(N*Y)^(2/3:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := ideal_cubic_moment hε
  refine ⟨C,hC,?_⟩
  intro P S N Y J u hN hY hJ hP hS
  simp_rw [normalizedDualPolynomial_cubic]
  simpa only [one_pow,mul_one] using hbound P S N Y 1 hN hY zero_le_one hP
    (fun ν hν => (hS ν hν).2)
    (fun ν => (((J/idealExponentNorm ν)^(1/2:ℝ):ℝ)*mellinPhase u (idealExponentNorm ν)))
    (fun ν hν => by
      rw [norm_mul,mellinPhase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (div_nonneg hJ.le (idealExponentNorm_pos ν).le) _)]
      exact dual_dyad_weight_le_one hJ (hS ν hν).1)

end CubicFirstMoment

end

end OAI
