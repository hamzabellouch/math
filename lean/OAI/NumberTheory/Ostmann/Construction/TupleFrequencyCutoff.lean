import OAI.NumberTheory.Ostmann.Characters.TupleCharacterPoisson

namespace OAI

/-! # The actual finite frequency support of the initial tuple amplitude -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

noncomputable def tupleFrequencies {I : Type*} [Fintype I] (p : I → ℕ) (N : ℕ) : Finset ℤ :=
  (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter
    (fun v => v ≠ 0 ∧ ∀ i, IsUnit (v : ZMod (p i)))

private theorem tupleGraphPhase_zero_at_zero {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℕ) [∀ i, NeZero (p i)] (hp : ∀ i, 2 ≤ p i)
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (t : ∀ i, ZMod (p i)) :
    tupleGraphPhase p χ t 0 = 0 := by
  obtain ⟨i⟩ := ‹Nonempty I›
  have hp1 : p i ≠ 1 := by have h := hp i; omega
  let : Nontrivial (ZMod (p i)) := ZMod.nontrivial_iff.mpr hp1
  exact tupleGraphPhase_zero p χ t 0 i (by simp)

private theorem fourier_zero_beyond_tuple_cutoff {I : Type*} [Fintype I]
    (p : I → ℕ) [NeZero (∏ i, p i)] (ψ : 𝓢(ℝ, ℂ))
    (X H : ℝ) (hX : 0 < X) (N : ℕ) (hcut : H * (∏ i, p i : ℕ) ≤ N * X)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) (v : ℤ)
    (hv : v ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) = 0 := by
  have hn : (N : ℝ) < |(v : ℝ)| := by
    have hi : (N : ℤ) < |v| := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hv
      rcases hv with hv | hv
      · exact (show (N : ℤ) < -v by omega).trans_le (neg_le_abs v)
      · exact hv.trans_le (le_abs_self v)
    exact_mod_cast hi
  have hM : (0 : ℝ) < (∏ i, p i : ℕ) := by exact_mod_cast NeZero.pos (∏ i, p i)
  apply hsupp
  rw [abs_div, abs_mul, abs_of_pos hX, abs_of_pos hM, lt_div_iff₀ hM]
  exact hcut.trans_lt (mul_lt_mul_of_pos_right hn hX)

private theorem tupleFrequencyTerm_zero {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hp : ∀ i, 2 ≤ p i) (χ : ∀ i, DirichletCharacter ℂ (p i))
    (t : ∀ i, ZMod (p i)) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (N : ℕ) (hcut : H * (∏ i, p i : ℕ) ≤ N * X)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) (v : ℤ)
    (hv : v ∉ tupleFrequencies p N) :
    (Real.sqrt (X / (∏ i, p i : ℕ)) : ℂ) *
      𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) * tupleGraphPhase p χ t v = 0 := by
  simp only [tupleFrequencies, Finset.mem_filter] at hv
  by_cases hr : v ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
  · by_cases hz : v = 0
    · subst v
      rw [tupleGraphPhase_zero_at_zero p hp χ t, mul_zero]
    · have hunit : ¬∀ i, IsUnit (v : ZMod (p i)) := fun hu => hv ⟨hr, hz, hu⟩
      obtain ⟨i, hi⟩ := not_forall.mp hunit
      rw [tupleGraphPhase_zero p χ t v i hi, mul_zero]
  · rw [fourier_zero_beyond_tuple_cutoff p ψ X H hX N hcut hsupp v hr,
      mul_zero, zero_mul]

theorem tuple_character_poisson_finite {I : Type*} [Fintype I] [Nonempty I]
    (p : I → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hp : ∀ i, 2 ≤ p i) (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (χ : ∀ i, DirichletCharacter ℂ (p i)) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i)) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (N : ℕ) (hcut : H * (∏ i, p i : ℕ) ≤ N * X)
    (hsupp : ∀ x : ℝ, H < |x| → 𝓕 ψ x = 0) :
    (∑' n : ℤ, (∏ i, χ i ((n : ZMod (p i)) - t i)) * ψ ((n : ℝ) / X)) /
        (Real.sqrt X : ℂ) =
      ∑ v ∈ tupleFrequencies p N, (Real.sqrt (X / (∏ i, p i : ℕ)) : ℂ) *
        𝓕 ψ ((v : ℝ) * X / (∏ i, p i : ℕ)) * tupleGraphPhase p χ t v := by
  rw [tuple_character_poisson_normalized p hc χ hχ t ψ X hX]
  exact tsum_eq_sum (tupleFrequencyTerm_zero p hp χ t ψ X H hX N hcut hsupp)

end Ostmann

end OAI
