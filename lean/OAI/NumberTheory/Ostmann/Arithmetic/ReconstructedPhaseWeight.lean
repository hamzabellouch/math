import OAI.NumberTheory.Ostmann.Construction.CopiedDirectedPhase
import OAI.NumberTheory.Ostmann.Construction.OriginalAveragedTransfer

namespace OAI

/-! # The forced-pivot off-diagonal is the actual next directed amplitude -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

private theorem branchPairwise_parts {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ)
    (hc : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j))) :
    Pairwise (fun h k => (L h).Coprime (L k)) ∧
      Pairwise (fun y z => (U y).Coprime (U z)) ∧ (∏ h, L h).Coprime (∏ y, U y) := by
  refine ⟨fun h k hne => hc (fun he => hne (Sum.inl.inj he)),
    fun y z hne => hc (fun he => hne (Sum.inr.inj he)), ?_⟩
  exact Nat.coprime_fintype_prod_left_iff.mpr fun h =>
    Nat.coprime_fintype_prod_right_iff.mpr fun y => hc (i := .inl h) (j := .inr y) (by intro he; cases he)

noncomputable def retainedWeightedCoefficient {A H Y : Type*} [Fintype H] [Fintype Y]
    (L : A → H → ℕ) (U : Y → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ y, Fact (U y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (ν : A → H → ℂ) (νY : A → Y → ℂ) (v : A → ℤ)
    (W : ℕ → A → ℂ) (M : ℕ) (a : A) : ℂ :=
  W M a * retainedPrimePhase (L a) U t χH χY b (ν a) (νY a) M (v a)

noncomputable def copiedWeightedAmplitude {A H Y : Type*} [Fintype A] [Fintype H] [Fintype Y]
    (L : A → H → ℕ) (U : Y → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ y, Fact (U y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (ν : A → H → ℂ) (νY : A → Y → ℂ) (v : A → ℤ)
    (W : ℕ → A → ℂ) (T : Finset ℕ) (V : ℕ) : ℂ :=
  ∑ s ∈ transferFrequencyRange V, ∑ a, ∑ a',
    let N := v a * (∏ h, L a' h) - v a' * (∏ h, L a h)
    let M := reconstructedPivot N s
    if validTransferredPivot T N s then
      W M a * conj (W M a') *
        copiedDirectedPhase (L a) (L a') U t χH χY b (ν a) (ν a') (νY a) (νY a') (v a) (v a') s
    else 0

/-- Only the original branch supports are hypotheses. Cross-copy distinctness
and the units at the new root are consequences of the equation and ranges. -/
theorem reconstructedOffDiagonal_eq_copiedWeightedAmplitude
    {A H Y : Type*} [Fintype A] [Fintype H] [Fintype Y]
    (L : A → H → ℕ) (U : Y → ℕ)
    [∀ a h, Fact (L a h).Prime] [∀ y, Fact (U y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (ν : A → H → ℂ) (νY : A → Y → ℂ) (v : A → ℤ)
    (W : ℕ → A → ℂ) (T : Finset ℕ) (B K V : ℕ)
    (hT : ∀ M ∈ T, 0 < M)
    (hsupport : ∀ M ∈ T, ∀ a, W M a ≠ 0 →
      Pairwise (fun i j => (Sum.elim (L a) U i).Coprime (Sum.elim (L a) U j)) ∧
      M.Coprime ((∏ h, L a h) * ∏ y, U y) ∧ (v a).natAbs ≤ B ∧ (∏ h, L a h) ≤ K)
    (hscale : ∀ M ∈ T, 2 * B * K ≤ V * M)
    (hlargeL : ∀ a h, V < L a h) (hlargeU : ∀ y, V < U y)
    (hb : ∀ y, b (some (.inr y)) (some (.inr y)) = 0) :
    reconstructedOffDiagonal T V (fun a => ∏ h, L a h) v
        (retainedWeightedCoefficient L U t χH χY b ν νY v W) =
      copiedWeightedAmplitude L U t χH χY b ν νY v W T V := by
  unfold reconstructedOffDiagonal copiedWeightedAmplitude
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro a' _
  dsimp only
  split_ifs with hvalid
  · let M := reconstructedPivot (v a * (∏ h, L a' h) - v a' * (∏ h, L a h)) s
    by_cases hWa : W M a = 0
    · dsimp only [M] at hWa
      simp only [retainedWeightedCoefficient, hWa, zero_mul]
    by_cases hWa' : W M a' = 0
    · dsimp only [M] at hWa'
      simp only [retainedWeightedCoefficient, hWa', zero_mul, map_zero, mul_zero]
    have hMT : M ∈ T := hvalid.2.2.2
    obtain ⟨hpA, hmA, hvA, hLA⟩ := hsupport M hMT a hWa
    obtain ⟨hpB, hmB, hvB, hLB⟩ := hsupport M hMT a' hWa'
    obtain ⟨hpL, hpU, hLU⟩ := branchPairwise_parts (L a) U hpA
    obtain ⟨hpR, _, hRU⟩ := branchPairwise_parts (L a') U hpB
    have he := transfer_copiedDirectedPhase_of_ranges (L a) (L a') U t χH χY b
      (ν a) (ν a') (νY a) (νY a') M (v a) (v a') s
      (validTransferredPivot_equation T _ s hvalid) B K V (hT M hMT) hvalid.1 hvA hvB hLA hLB
      (hscale M hMT) hpL hpR hpU hLU hRU
      (Nat.coprime_mul_iff_right.mp hmA).1 (Nat.coprime_mul_iff_right.mp hmB).1
      (Nat.coprime_mul_iff_right.mp hmA).2 (hlargeL a) (hlargeL a') hlargeU hb
    simp only [retainedWeightedCoefficient, map_mul (starRingEnd ℂ)]
    calc
      _ = (W M a * conj (W M a')) *
          (retainedPrimePhase (L a) U t χH χY b (ν a) (νY a) M (v a) *
            conj (retainedPrimePhase (L a') U t χH χY b (ν a') (νY a') M (v a'))) := by ring
      _ = _ := by rw [he]
  · rfl

end Ostmann

end OAI
