import OAI.NumberTheory.Ostmann.Characters.SparseCoefficientSupport
import OAI.NumberTheory.Ostmann.Characters.SparseWeightMellinExpansion
import OAI.NumberTheory.Ostmann.Construction.InjectiveCoefficientTransport

namespace OAI

/-! # The sparse weight as a bounded sum of primitive characters -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable local instance {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def sparsePrimitiveLabel {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ) : Option PrimitiveComplexCharacter :=
  primitiveCharacterReduction (sparseProductCharacter p χ)

noncomputable def sparsePrimitiveCoefficient {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ) :
    Option PrimitiveComplexCharacter → ℂ :=
  injectiveCoefficient (sparsePrimitiveLabel p) (sparseTruncatedMellinCoefficient p E t K)

noncomputable def sparsePrimitiveSupport {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ) : Finset (Option PrimitiveComplexCharacter) :=
  ((Finset.univ : Finset (∀ i, MulChar (ZMod (p i)) ℂ)).filter
    (fun χ => sparseTruncatedMellinCoefficient p E t K χ ≠ 0)).image (sparsePrimitiveLabel p)

theorem sparsePrimitiveLabel_injective {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j))) :
    Function.Injective (sparsePrimitiveLabel p) :=
  (primitiveCharacterReduction_injective _).comp (sparseProductCharacter_injective p hc)

theorem sparsePrimitiveCoefficient_norm_le {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (hE : ∀ i, 0 ∉ E i)
    (hsym : ∀ i b, -b ∈ E i ↔ b ∈ E i) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hp : ∀ i, (36 : ℝ) ≤ p i) (K : ℕ) (e : Option PrimitiveComplexCharacter) :
    ‖sparsePrimitiveCoefficient p E t K e‖ ≤ Real.exp (6 * ∑ i, (p i : ℝ)⁻¹) :=
  injectiveCoefficient_norm_le _ _ _ (Real.exp_nonneg _)
    (sparseTruncatedMellinCoefficient_norm_le p E hE hsym t ht ht1 hp K) e

theorem sparsePrimitiveSupport_modulus_le {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (C L t : ℝ)
    (hlog : ∀ i, Real.log (p i) ≤ Real.exp ((9 / 10 : ℝ) * L))
    (ρ : PrimitiveComplexCharacter)
    (hρ : ρ ∈ (sparsePrimitiveSupport p E t (sparseTruncationDegree C L)).eraseNone) :
    ρ.modulus ≤ sparseConductorCutoff C L := by
  obtain ⟨χ, hχ, he⟩ := Finset.mem_image.mp (Finset.mem_eraseNone.mp hρ)
  exact sparse_coefficient_primitive_modulus_le p E C L t χ (Finset.mem_filter.mp hχ).2 hlog ρ he

theorem sparseWeight_primitive_expansion {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ) (u : (ZMod (∏ i, p i))ˣ) :
    elementaryTruncation
        (fun i => sparseAdditiveKernel (E i) t (crtUnitEquiv p hc u i)) K ^ 2 =
      sparsePrimitiveCoefficient p E t K none +
      ∑ ρ ∈ (sparsePrimitiveSupport p E t K).eraseNone,
        sparsePrimitiveCoefficient p E t K (some ρ) *
          liftPrimitiveCharacter (∏ i, p i) (some ρ) u := by
  let f := sparsePrimitiveLabel p
  let w := sparseTruncatedMellinCoefficient p E t K
  let g : Option PrimitiveComplexCharacter → ℂ := fun e => liftPrimitiveCharacter (∏ i, p i) e u
  have hf := sparsePrimitiveLabel_injective p hc
  have hsum := injectiveCoefficient_sum f hf w g
  have hsplit := sum_option_support (sparsePrimitiveSupport p E t K)
    (fun e => sparsePrimitiveCoefficient p E t K e * g e) (by
      intro he
      have hz : sparsePrimitiveCoefficient p E t K none = 0 := by
        by_contra hh
        obtain ⟨χ, hχ, hw⟩ := injectiveCoefficient_ne_zero f w none hh
        exact he (Finset.mem_image.mpr ⟨χ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩, hχ⟩)
      rw [hz, zero_mul])
  have hlabel (χ : ∀ i, MulChar (ZMod (p i)) ℂ) :
      g (f χ) = sparseProductCharacter p χ u := by
    exact congrArg (fun z : DirichletCharacter ℂ (∏ i, p i) => z u)
      (lift_primitiveCharacterReduction (sparseProductCharacter p χ))
  calc
    _ = ∑ χ : (∀ i, MulChar (ZMod (p i)) ℂ), w χ * sparseProductCharacter p χ u := by
      rw [sparseWeight_mellin_expansion]
      apply Finset.sum_congr rfl
      intro χ _
      rw [sparseProductCharacter_apply p hc]
    _ = ∑ χ, w χ * g (f χ) := by simp only [hlabel]
    _ = ∑ e ∈ sparsePrimitiveSupport p E t K, sparsePrimitiveCoefficient p E t K e * g e :=
      by
        dsimp only [f, w, sparsePrimitiveSupport, sparsePrimitiveCoefficient] at hsum ⊢
        convert hsum.symm using 2
        ext e
        simp only [Finset.mem_image]
    _ = _ := by
      rw [hsplit]
      simp only [g, liftPrimitiveCharacter, MulChar.one_apply_coe, mul_one]

theorem sparsePrimitiveSupport_modulus_dvd {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ)
    (ρ : PrimitiveComplexCharacter)
    (hρ : ρ ∈ (sparsePrimitiveSupport p E t K).eraseNone) : ρ.modulus ∣ ∏ i, p i := by
  obtain ⟨χ, _, he⟩ := Finset.mem_image.mp (Finset.mem_eraseNone.mp hρ)
  rw [primitiveCharacterReduction_modulus (sparseProductCharacter p χ) ρ he]
  exact DirichletCharacter.conductor_dvd_level _

theorem sparsePrimitiveSupport_avoids {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ)
    (exception : Option PrimitiveComplexCharacter)
    (havoid : ∀ ρ, exception = some ρ → ¬ ρ.modulus ∣ ∏ i, p i) :
    ∀ ρ ∈ (sparsePrimitiveSupport p E t K).eraseNone, some ρ ≠ exception := by
  intro ρ hρ he
  exact havoid ρ he.symm (sparsePrimitiveSupport_modulus_dvd p E t K ρ hρ)

end Ostmann

end OAI
