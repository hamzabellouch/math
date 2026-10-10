import OAI.Combinatorics.SharpThreshold.FourierBasis

namespace OAI

universe u

noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

/-- Separate Fourier supports according to whether the distinguished coordinate occurs. -/
def optionFinsetEquiv : Finset (Option ι) ≃ Finset ι ⊕ Finset ι := by
  classical
  refine
    { toFun := fun S => if none ∈ S then Sum.inr S.eraseNone else Sum.inl S.eraseNone
      invFun := Sum.elim (fun S => S.map Function.Embedding.some) Finset.insertNone
      left_inv := ?_
      right_inv := ?_ }
  · intro S
    by_cases h : none ∈ S
    · simp [h, Finset.insert_eq_of_mem h]
    · simp [h]
  · intro S
    cases S <;> simp

theorem sum_option_finset (F : Finset (Option ι) → ℝ) :
    (∑ S, F S) =
      (∑ S : Finset ι, F (S.map Function.Embedding.some)) +
      ∑ S : Finset ι, F (Finset.insertNone S) := by
  classical
  rw [← optionFinsetEquiv.symm.sum_comp F]
  simp [Fintype.sum_sum_type, optionFinsetEquiv]

omit [Fintype ι] in
@[simp] theorem char_map_some (p : ℝ) (S : Finset ι) (x : Option ι → Bool) :
    char p (S.map Function.Embedding.some) x = char p S (fun i => x (some i)) := by
  classical
  simp [char]

omit [Fintype ι] in
@[simp] theorem char_insertNone (p : ℝ) (S : Finset ι) (x : Option ι → Bool) :
    char p (Finset.insertNone S) x =
      chi p (x none) * char p S (fun i => x (some i)) := by
  classical
  simp [char, Finset.insertNone]

/-- A noise-weighted Fourier polynomial separates into its two first-coordinate pieces. -/
theorem synthesis_option (p ρ : ℝ) (c : Finset (Option ι) → ℝ)
    (x : Option ι → Bool) :
    (∑ S, ρ ^ S.card * c S * char p S x) =
      (∑ S : Finset ι, ρ ^ S.card * c (S.map Function.Embedding.some) *
        char p S (fun i => x (some i))) +
      ρ * chi p (x none) *
        ∑ S : Finset ι, ρ ^ S.card * c (Finset.insertNone S) *
          char p S (fun i => x (some i)) := by
  classical
  rw [sum_option_finset]
  simp only [Finset.card_map, char_map_some, Finset.card_insertNone, char_insertNone,
    pow_succ]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem coefficient_energy_option (c : Finset (Option ι) → ℝ) :
    (∑ S, c S ^ 2) =
      (∑ S : Finset ι, c (S.map Function.Embedding.some) ^ 2) +
        ∑ S : Finset ι, c (Finset.insertNone S) ^ 2 :=
  sum_option_finset _

end Problem313.BiasedFourier

end

end OAI
