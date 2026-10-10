import OAI.NumberTheory.Ostmann.QuadraticSieveComplement
import OAI.NumberTheory.Ostmann.QuadraticSieveCoprimePoisson

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

noncomputable def complementarySchwartzSum (W : 𝓢(ℝ, ℂ)) (M : ℝ) (K d q : ℕ) : ℂ :=
  ∑' n : {n : ℕ // 0 < n}, if squarefreeKernel n.val ≤ K then
    (if Odd n.val then (jacobiSym (n.val : ℤ) (d ^ 2 * q) : ℂ) *
      W ((n.val : ℝ) / M) else 0) else 0

noncomputable def complementaryPoissonMain (W : 𝓢(ℝ, ℂ)) (M : ℝ) (K d q : ℕ)
    (X₁ X₂ L : ℕ → ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∑ v ∈ oddSquarefreeUpTo K, if Nat.Coprime v d then
    (jacobiSym (v : ℤ) q : ℂ) * coprimePoissonMain (squarePullback W 1 (by norm_num))
      (2 * q * d) (Real.sqrt (M / v)) (X₁ v) (X₂ v) (L v) else 0

theorem complementaryPoisson_error (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ), 0 < M → ∀ (K d q : ℕ), d ≠ 0 → q ≠ 0 →
      ∀ (X₁ X₂ J L : ℕ → ℝ),
        (∀ v ∈ oddSquarefreeUpTo K,
          0 < X₁ v ∧ X₁ v ≤ Real.sqrt (M / v) ∧ Real.sqrt (M / v) ≤ X₂ v ∧
          0 < J v ∧ J v ≤ min (Real.sqrt (M / v) / X₁ v) (X₂ v / Real.sqrt (M / v)) ∧
          (X₂ v / Real.sqrt (M / v)) ^ 2 ≤ L v) →
        ‖complementarySchwartzSum W M K d q - complementaryPoissonMain W M K d q X₁ X₂ L‖ ≤
          C * ∑ v ∈ oddSquarefreeUpTo K, Real.sqrt (M / v) / J v ^ A := by
  let ψ := squarePullback W 1 (by norm_num)
  obtain ⟨C, hC, hbound⟩ := coprime_poisson_truncated ψ A
  refine ⟨C / 2, by positivity, ?_⟩
  intro M hM K d q hd hq X₁ X₂ J L hp
  let : NeZero d := ⟨hd⟩
  let : NeZero q := ⟨hq⟩
  have hk : 2 ≤ 2 * q * d := by
    have hdp := Nat.pos_of_ne_zero hd
    have hqp := Nat.pos_of_ne_zero hq
    nlinarith
  let E : ℕ → ℂ := fun v =>
    (∑' m : ℤ, if Nat.Coprime m.natAbs (2 * q * d) then
      ψ ((m : ℝ) / Real.sqrt (M / v)) else 0) -
        coprimePoissonMain ψ (2 * q * d) (Real.sqrt (M / v)) (X₁ v) (X₂ v) (L v)
  have hdiff : complementarySchwartzSum W M K d q -
      complementaryPoissonMain W M K d q X₁ X₂ L =
        (1 / 2 : ℂ) * ∑ v ∈ oddSquarefreeUpTo K,
          if Nat.Coprime v d then (jacobiSym (v : ℤ) q : ℂ) * E v else 0 := by
    rw [complementarySchwartzSum, schwartz_complement_eq_coprime_lattices W M hM,
      complementaryPoissonMain, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hc : Nat.Coprime v d
    · simp only [ite_eq_left hc]
      dsimp only [E, ψ]
      ring
    · simp only [ite_eq_right hc, sub_self]
  have hn : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hdiff, norm_mul, hn]
  calc
    (1 / 2 : ℝ) * ‖∑ v ∈ oddSquarefreeUpTo K,
        if Nat.Coprime v d then (jacobiSym (v : ℤ) q : ℂ) * E v else 0‖ ≤
        (1 / 2 : ℝ) * ∑ v ∈ oddSquarefreeUpTo K,
          ‖if Nat.Coprime v d then (jacobiSym (v : ℤ) q : ℂ) * E v else 0‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * ∑ v ∈ oddSquarefreeUpTo K,
        C * Real.sqrt (M / v) / J v ^ A := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨h1, h2, h3, hJ, hmin, hL⟩ := hp v hv
      have he := hbound (2 * q * d) (Real.sqrt (M / v)) (X₁ v) (X₂ v) (J v) (L v)
        hk h1 h2 h3 hJ hmin hL
      change ‖E v‖ ≤ C * Real.sqrt (M / v) / J v ^ A at he
      by_cases hc : Nat.Coprime v d
      · rw [ite_eq_left hc]
        apply le_trans _ he
        rcases jacobiSym.trichotomy (v : ℤ) q with h | h | h <;> simp [h]
      · rw [ite_eq_right hc, norm_zero]
        positivity
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring

end Ostmann.QuadraticSieve

end OAI
