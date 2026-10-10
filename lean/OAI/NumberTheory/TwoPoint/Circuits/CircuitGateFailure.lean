import OAI.NumberTheory.TwoPoint.Circuits.CircuitRandomGate
import OAI.NumberTheory.TwoPoint.Circuits.CircuitSamplingGrid

namespace OAI

/-! The sampled AND polynomial agrees with the Boolean gate whenever the
samplers isolate a false child; all-true inputs are always exact. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

def sampledCoordinates {k : ℕ} (x : BooleanCube k) : Finset (Fin k) :=
  univ.filter (fun i => x i = true)

def falseCoordinates {k : ℕ} (b : Fin k → Bool) : Finset (Fin k) :=
  univ.filter (fun i => b i = false)

noncomputable def sampledAndPolynomial {k s : ℕ}
    (x : GateSamplingChoices k k s) (u : Fin k → ℝ) : ℝ :=
  ∏ a, ∏ i, andGateFactor (sampledCoordinates (x a i)) u

noncomputable def boolAndValue {k : ℕ} (b : Fin k → Bool) : ℝ :=
  if ∀ i, b i = true then 1 else 0

lemma sampledAndPolynomial_degree {n k s : ℕ} (x : GateSamplingChoices k k s)
    (P : Fin k → BooleanCube n → ℝ) (d : ℕ) (hP : ∀ i, WalshDegreeLE (P i) d) :
    WalshDegreeLE (fun y => sampledAndPolynomial x (fun i => P i y))
      (d * s * (Nat.log 2 k + 3)) := by
  have hinner (a : Fin (Nat.log 2 k + 3)) :
      WalshDegreeLE (fun y => ∏ i : Fin s,
        andGateFactor (sampledCoordinates (x a i)) (fun j => P j y)) (d * s) := by
    have hh := WalshDegreeLE.prod univ
      (fun i y => andGateFactor (sampledCoordinates (x a i)) (fun j => P j y)) d
        (fun i _ => WalshDegreeLE.andGateFactor _ P d (fun j _ => hP j))
    simpa only [card_univ, Fintype.card_fin] using hh
  have hh := WalshDegreeLE.prod univ
    (fun a y => ∏ i : Fin s,
      andGateFactor (sampledCoordinates (x a i)) (fun j => P j y)) (d * s)
      (fun a _ => hinner a)
  change WalshDegreeLE (fun y => ∏ a, ∏ i : Fin s,
    andGateFactor (sampledCoordinates (x a i)) (fun j => P j y)) _
  simpa only [card_univ, Fintype.card_fin] using hh

lemma isolatesOne_card {k : ℕ} {S : Finset (Fin k)} {x : BooleanCube k}
    (h : isolatesOne S x) : (S.filter (fun i => x i = true)).card = 1 := by
  obtain ⟨i, hi, hx⟩ := h
  have heq : S.filter (fun j => x j = true) = {i} := by
    ext j
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hj, htrue⟩
      have hh := hx j hj
      rw [htrue] at hh
      simpa [singleBitPattern] using hh.symm
    · intro hj
      subst j
      exact ⟨hi, by simpa [singleBitPattern] using hx i hi⟩
  rw [heq, card_singleton]

lemma sampled_false_card {k : ℕ} (b : Fin k → Bool) (x : BooleanCube k)
    (h : isolatesOne (falseCoordinates b) x) :
    ((sampledCoordinates x).filter (fun i => b i = false)).card = 1 := by
  have heq : (sampledCoordinates x).filter (fun i => b i = false) =
      (falseCoordinates b).filter (fun i => x i = true) := by
    ext i
    simp only [sampledCoordinates, falseCoordinates, mem_filter, mem_univ, true_and]
    tauto
  rw [heq]
  exact isolatesOne_card h

lemma sampledAndPolynomial_all_true {k s : ℕ} (x : GateSamplingChoices k k s)
    (b : Fin k → Bool) (hb : ∀ i, b i = true) :
    sampledAndPolynomial x (fun i => if b i then 1 else 0) = 1 := by
  unfold sampledAndPolynomial
  have hh (a : Fin (Nat.log 2 k + 3)) (i : Fin s) :
      andGateFactor (sampledCoordinates (x a i)) (fun j => if b j then 1 else 0) = 1 :=
    andGateFactor_all_true _ b (fun j _ => hb j)
  simp only [hh, prod_const_one]

lemma sampledAndPolynomial_isolated {k s : ℕ} (x : GateSamplingChoices k k s)
    (b : Fin k → Bool) (h : ∃ a i, isolatesOne (falseCoordinates b) (x a i)) :
    sampledAndPolynomial x (fun i => if b i then 1 else 0) = 0 := by
  obtain ⟨a, i, hi⟩ := h
  unfold sampledAndPolynomial
  apply prod_eq_zero (mem_univ a)
  apply prod_eq_zero (mem_univ i)
  exact andGateFactor_one_false _ b (sampled_false_card b (x a i) hi)

lemma sampledAndPolynomial_failure {k s : ℕ} (x : GateSamplingChoices k k s)
    (b : Fin k → Bool)
    (h : sampledAndPolynomial x (fun i => if b i then 1 else 0) ≠ boolAndValue b) :
    ∀ a i, ¬isolatesOne (falseCoordinates b) (x a i) := by
  have hn : ¬∀ i, b i = true := by
    intro hb
    apply h
    rw [sampledAndPolynomial_all_true x b hb]
    exact (ite_eq_left hb).symm
  intro a i hi
  apply h
  rw [sampledAndPolynomial_isolated x b ⟨a, i, hi⟩]
  exact (ite_eq_right hn).symm

end TwoPointCorrelations

end OAI
