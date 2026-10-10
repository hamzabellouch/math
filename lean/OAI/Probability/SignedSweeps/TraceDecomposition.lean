import OAI.Probability.SignedSweeps.IrreducibleClassification

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical

instance partitionFintype (n : ℕ) : Fintype (Partition n) := Fintype.ofFinite _

lemma class_function_expansion {n : ℕ} (f : ConjClasses (SymmetricGroup n) → ℂ) :
    f = ∑ lam : Partition n, classCharacterPairing (spechtRepresentation lam) f •
      quotientCharacter (spechtRepresentation lam) := by
  have hf : f ∈ Submodule.span ℂ (Set.range (fun lam : Partition n =>
    quotientCharacter (spechtRepresentation lam))) := by rw [specht_characters_span]; trivial
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨mu, rfl⟩ := hx
    simp only [specht_classCharacterPairing, ite_smul, one_smul, zero_smul]
    simp
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | smul c x _ hx =>
    simp only [map_smul, smul_assoc, ← Finset.smul_sum]
    rw [← hx]

theorem character_specht_expansion {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (g : SymmetricGroup n) :
    ρ.character g = ∑ lam : Partition n,
      (finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam) ρ) : ℂ) *
        (spechtRepresentation lam).character g := by
  let : Invertible (Nat.card (SymmetricGroup n) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := SymmetricGroup n)).ne')
  have he := congrFun (class_function_expansion (quotientCharacter ρ)) (ConjClasses.mk g)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, quotientCharacter_mk] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro lam _
  congr 1
  exact Representation.card_inv_mul_sum_char_mul_char_eq_finrank _ _

lemma trace_coefficientAction {G E : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) (f : G → ℂ) :
    LinearMap.trace ℂ E (coefficientAction ρ f) = ∑ g, f g * ρ.character g := by
  simp only [coefficientAction, map_sum, map_smul, smul_eq_mul, Representation.character]

theorem trace_specht_expansion {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρ : Representation ℂ (SymmetricGroup n) E) (f : SymmetricGroup n → ℂ) :
    LinearMap.trace ℂ E (coefficientAction ρ f) =
      ∑ lam : Partition n,
        (finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam) ρ) : ℂ) *
          LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f) := by
  simp only [trace_coefficientAction, character_specht_expansion ρ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro lam _
  apply Finset.sum_congr rfl
  intro g _
  ring

lemma finiteRegular_character {G : Type*} [Group G] [Fintype G] (g : G) :
    (finiteRegularRepresentation (G := G)).character g =
      if g = 1 then (Fintype.card G : ℂ) else 0 := by
  have he : coefficientAction (finiteRegularRepresentation (G := G))
      (fun h => if h = g then 1 else 0) = finiteRegularRepresentation g := by
    simp [coefficientAction, ite_smul]
  rw [Representation.character, ← he, finiteRegular_trace]
  by_cases hg : g = 1
  · simp [hg]
  · simp [hg, Ne.symm hg]

lemma specht_regular_multiplicity {n : ℕ} (lam : Partition n) :
    finrank ℂ (Representation.IntertwiningMap (spechtRepresentation lam)
      (finiteRegularRepresentation (G := SymmetricGroup n))) = spechtDimension lam := by
  let : Invertible (Nat.card (SymmetricGroup n) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := SymmetricGroup n)).ne')
  apply Nat.cast_injective (R := ℂ)
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank]
  simp only [finiteRegular_character, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, inv_one, Representation.char_one, Fintype.card_eq_nat_card]
  have hg : (Nat.card (SymmetricGroup n) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := SymmetricGroup n)).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hg, one_mul]
  rfl

theorem regular_trace_specht_expansion {n : ℕ} (f : SymmetricGroup n → ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (SymmetricGroup n))
      (coefficientAction finiteRegularRepresentation f) =
      ∑ lam : Partition n, (spechtDimension lam : ℂ) *
        LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f) := by
  rw [trace_specht_expansion]
  simp only [specht_regular_multiplicity]

end SignedSweeps
end

end OAI
