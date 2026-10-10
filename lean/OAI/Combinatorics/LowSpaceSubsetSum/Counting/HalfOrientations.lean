import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationConcentration

namespace OAI

/-!
# Orienting three pairs of mixer halves

The orientations here describe the conditional sign experiment; they are
analysis variables, not extra random draws made by the algorithm. Every
unordered pair of halves has a good orientation by deficiency
superadditivity. A uniform vector of three orientations therefore succeeds
with probability at least one eighth. The product-space bound also permits
an arbitrary preceding event depending on the unordered pairs.
-/

namespace LowSpaceSubsetSum

theorem finiteUniformProbability_ge_card_inv_of_exists {Ω : Type*} [Fintype Ω]
    [Nonempty Ω] (P : Ω → Prop) (hP : ∃ ω, P ω) :
    (Fintype.card Ω : ℝ)⁻¹ ≤ finiteUniformProbability P := by
  classical
  unfold finiteUniformProbability
  rw [inv_eq_one_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hcard : 0 < Fintype.card {ω // P ω} := by
    apply Fintype.card_pos_iff.mpr
    obtain ⟨ω, hω⟩ := hP
    exact ⟨⟨ω, hω⟩⟩
  exact_mod_cast hcard

def orientedHalf {ι : Type*} (A B : Finset ι) (b : Bool) : Finset ι :=
  if b then A else B

theorem exists_good_half_orientation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (A B M : Finset ι) (hAB : Disjoint A B) (hM : A ∪ B = M)
    (τ : ℝ) (hA : deficiency a A ≤ τ) (hB : deficiency a B ≤ τ) :
    ∃ b : Bool, deficiency a (orientedHalf A B b) ≤ min τ (deficiency a M / 2) := by
  have hsum := deficiency_superadditive a hAB
  rw [hM] at hsum
  by_cases ha : deficiency a A ≤ deficiency a M / 2
  · exact ⟨true, by simpa [orientedHalf] using le_min hA ha⟩
  · refine ⟨false, ?_⟩
    simp only [orientedHalf, Bool.false_eq_true, ↓reduceIte]
    exact le_min hB (by linarith)

theorem three_half_orientations_probability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (A B M : Fin 3 → Finset ι)
    (hAB : ∀ i, Disjoint (A i) (B i)) (hM : ∀ i, A i ∪ B i = M i)
    (τ : ℝ) (hA : ∀ i, deficiency a (A i) ≤ τ)
    (hB : ∀ i, deficiency a (B i) ≤ τ) :
    (1 / 8 : ℝ) ≤ finiteUniformProbability (fun b : Fin 3 → Bool =>
      ∀ i, deficiency a (orientedHalf (A i) (B i) (b i)) ≤
        min τ (deficiency a (M i) / 2)) := by
  classical
  have hgood (i : Fin 3) := exists_good_half_orientation a (A i) (B i) (M i)
    (hAB i) (hM i) τ (hA i) (hB i)
  have hex : ∃ b : Fin 3 → Bool, ∀ i,
      deficiency a (orientedHalf (A i) (B i) (b i)) ≤ min τ (deficiency a (M i) / 2) :=
    ⟨fun i => Classical.choose (hgood i), fun i => Classical.choose_spec (hgood i)⟩
  have h := finiteUniformProbability_ge_card_inv_of_exists _ hex
  simpa using h

/-- Counting one successful orientation over every preceding good outcome
gives the joint lower bound without assuming that the preceding event and
the successful orientation event are independent. -/
theorem finiteUniformProbability_joint_orientation {Ω : Type*} [Fintype Ω]
    [Nonempty Ω] (E : Ω → Prop) (G : Ω → (Fin 3 → Bool) → Prop)
    (hG : ∀ ω, E ω → ∃ b, G ω b) :
    finiteUniformProbability E / 8 ≤
      finiteUniformProbability (fun p : Ω × (Fin 3 → Bool) => E p.1 ∧ G p.1 p.2) := by
  classical
  let : DecidablePred E := fun _ => Classical.propDecidable _
  let : DecidablePred (fun p : Ω × (Fin 3 → Bool) => E p.1 ∧ G p.1 p.2) :=
    fun _ => Classical.propDecidable _
  let witness (ω : {ω // E ω}) : Fin 3 → Bool := Classical.choose (hG ω.val ω.property)
  let embed : {ω // E ω} → {p : Ω × (Fin 3 → Bool) // E p.1 ∧ G p.1 p.2} :=
    fun ω => ⟨(ω.val, witness ω), ω.property, Classical.choose_spec (hG ω.val ω.property)⟩
  have hinj : Function.Injective embed := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z => z.val.1) h
  have hcard := Fintype.card_le_of_injective embed hinj
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  unfold finiteUniformProbability
  rw [Fintype.card_prod]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_mul]
  norm_num
  rw [div_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

end LowSpaceSubsetSum

end OAI
