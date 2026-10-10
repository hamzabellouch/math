import OAI.NumberTheory.Ostmann.Dirichlet.Zeros
import OAI.NumberTheory.Ostmann.ZeroDensity.FiniteDecay
import OAI.NumberTheory.Ostmann.ZeroDensity.Target

namespace OAI

noncomputable section
open scoped BigOperators

namespace Ostmann.ZeroDensity

def NonprincipalPrimitiveFamily (Q : ℕ) :=
  {χ : PrimitiveFamily Q // χ.2.1 ≠ 1}

instance (Q : ℕ) : Fintype (NonprincipalPrimitiveFamily Q) := by
  classical
  unfold NonprincipalPrimitiveFamily
  infer_instance

def ZeroOccurrence (Q : ℕ) (T : ℝ) :=
  Σ χ : NonprincipalPrimitiveFamily Q,
    Σ ρ : {ρ : ℂ // ρ ∈ Ostmann.Dirichlet.zerosUpTo χ.1.2.1 T},
      Fin (Ostmann.Dirichlet.zeroMultiplicity χ.1.2.1 ρ.1)

instance (Q : ℕ) (T : ℝ) : Fintype (ZeroOccurrence Q T) := by
  classical
  letI (χ : NonprincipalPrimitiveFamily Q) :
      Fintype {ρ : ℂ // ρ ∈ Ostmann.Dirichlet.zerosUpTo χ.1.2.1 T} :=
    (Ostmann.Dirichlet.zerosUpTo_finite χ.1.2.1 χ.2 T).fintype
  unfold ZeroOccurrence
  infer_instance

def ZeroOccurrence.point {Q : ℕ} {T : ℝ} (z : ZeroOccurrence Q T) : ℂ := z.2.1.1

def retainedZeros (Q : ℕ) (exception : Option (PrimitiveFamily Q)) (σ T : ℝ) :
    Finset (ZeroOccurrence Q T) := by
  classical
  exact Finset.univ.filter (fun z => some z.1.1 ≠ exception ∧ σ ≤ z.point.re)

def totalZeroCount (Q : ℕ) (exception : Option (PrimitiveFamily Q)) (σ T : ℝ) : ℕ :=
  (retainedZeros Q exception σ T).card

theorem ZeroOccurrence.isNontrivialZero {Q : ℕ} {T : ℝ} (z : ZeroOccurrence Q T) :
    Ostmann.Dirichlet.IsNontrivialZero z.1.1.2.1 z.point := z.2.1.2.1

theorem totalZeroCount_le_none (Q : ℕ) (exception : Option (PrimitiveFamily Q))
    (σ T : ℝ) :
    totalZeroCount Q exception σ T ≤ totalZeroCount Q none σ T := by
  classical
  apply Finset.card_le_card
  intro z hz
  obtain ⟨_, _, hzσ⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp, hzσ⟩

theorem totalZeroCount_antitone (Q : ℕ) (exception : Option (PrimitiveFamily Q))
    (T : ℝ) : Antitone (fun σ => totalZeroCount Q exception σ T) := by
  classical
  intro σ τ hστ
  apply Finset.card_le_card
  intro z hz
  obtain ⟨_, hexc, hzτ⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hexc, hστ.trans hzτ⟩

theorem totalZeroCount_pos_of_zero (Q : ℕ) (exception : Option (PrimitiveFamily Q))
    (χ : NonprincipalPrimitiveFamily Q) (hexc : some χ.1 ≠ exception)
    {σ T : ℝ} {ρ : ℂ} (hρ : ρ ∈ Ostmann.Dirichlet.zerosUpTo χ.1.2.1 T)
    (hσ : σ ≤ ρ.re) : 0 < totalZeroCount Q exception σ T := by
  classical
  apply Finset.card_pos.mpr
  have hm := Ostmann.Dirichlet.zeroMultiplicity_pos χ.1.2.1 χ.2 hρ.1.1
  refine ⟨⟨χ, ⟨ρ, hρ⟩, ⟨0, hm⟩⟩, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hexc, hσ⟩

theorem actual_zero_density_exp_sum_le (Q : ℕ) (exception : Option (PrimitiveFamily Q))
    {T M A B u : ℝ} (hM : 0 < M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hMA : 2 * A ≤ M) (hu : u ≤ (1 : ℝ) / 2)
    (hstrip : ∀ z ∈ retainedZeros Q exception (1 / 2) T, u ≤ 1 - z.point.re)
    (hdensity : ∀ y ∈ Set.Icc u (1 / 2),
      (totalZeroCount Q exception (1 - y) T : ℝ) ≤ B * Real.exp (A * y)) :
    ∑ z ∈ retainedZeros Q exception (1 / 2) T, Real.exp (-M * (1 - z.point.re)) ≤
      (⌊M / 2⌋₊ + 1 : ℝ) * B * Real.exp (1 - M * u / 2) := by
  classical
  let s := retainedZeros Q exception (1 / 2) T
  let gap : ZeroOccurrence Q T → ℝ := fun z => 1 - z.point.re
  have htop : ∀ z ∈ s, gap z ≤ (1 : ℝ) / 2 := by
    intro z hz
    have hz' := (Finset.mem_filter.mp hz).2.2
    dsimp [gap]
    linarith
  have hzero : ∀ z ∈ s, 0 ≤ gap z := by
    intro z _
    have hz := z.isNontrivialZero.2.2
    dsimp [gap]
    linarith
  have hcount : ∀ y ∈ Set.Icc u (1 / 2),
      ((s.filter (fun z => gap z ≤ y)).card : ℝ) ≤ B * Real.exp (A * y) := by
    intro y hy
    have hsub : s.filter (fun z => gap z ≤ y) ⊆ retainedZeros Q exception (1 - y) T := by
      intro z hz
      obtain ⟨hzs, hzy⟩ := Finset.mem_filter.mp hz
      obtain ⟨_, hexc, _⟩ := Finset.mem_filter.mp hzs
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hexc, ?_⟩
      dsimp [gap] at hzy
      linarith
    exact le_trans (by exact_mod_cast Finset.card_le_card hsub) (hdensity y hy)
  simpa only [mul_one_div] using
    finite_density_exp_sum_le s gap hM hA hB hMA hstrip hzero htop
      (extend_density_bound s gap hA hB hu htop hcount)

end Ostmann.ZeroDensity

end

end OAI
