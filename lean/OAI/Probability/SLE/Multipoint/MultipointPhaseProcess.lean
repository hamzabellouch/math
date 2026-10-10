import OAI.Probability.SLE.Multipoint.MultipointPatternProduct
import OAI.Probability.SLE.Multipoint.MultipointPiecewiseClock

namespace OAI

/-! The actual finite phase process read from the three stopping times of
each marked point. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

def phaseAt {Ω ι : Type*} (ρ : (ι × Fin 3) → Ω → ℝ≥0)
    (t : ℝ≥0) (ω : Ω) (i : ι) : Fin 4 :=
  if ρ (i,2) ω ≤ t then 3 else if ρ (i,1) ω ≤ t then 2
  else if ρ (i,0) ω ≤ t then 1 else 0

def phaseOfPattern {ι : Type*} [DecidableEq ι] (A : Finset (ι × Fin 3)) (i : ι) : Fin 4 :=
  if (i,2) ∈ A then 3 else if (i,1) ∈ A then 2 else if (i,0) ∈ A then 1 else 0

lemma phaseAt_of_pattern {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (τ : Ω → ℝ≥0) (A : Finset (ι × Fin 3))
    {ω : Ω} (hω : ω ∈ switchPatternEvent Finset.univ ρ τ A) :
    phaseAt ρ (τ ω) ω = phaseOfPattern A := by
  funext i
  simp only [phaseAt, phaseOfPattern, hω (i,2) (Finset.mem_univ _),
    hω (i,1) (Finset.mem_univ _), hω (i,0) (Finset.mem_univ _)]

lemma phaseAt_monotone {Ω ι : Type*} (ρ : (ι × Fin 3) → Ω → ℝ≥0)
    (ω : Ω) (i : ι) : Monotone (fun t => phaseAt ρ t ω i) := by
  intro t u htu
  have h0 : ρ (i,0) ω ≤ t → ρ (i,0) ω ≤ u := fun h => h.trans htu
  have h1 : ρ (i,1) ω ≤ t → ρ (i,1) ω ≤ u := fun h => h.trans htu
  have h2 : ρ (i,2) ω ≤ t → ρ (i,2) ω ≤ u := fun h => h.trans htu
  dsimp only [phaseAt]
  split_ifs <;> simp_all

lemma phaseAt_ge_iff {Ω ι : Type*} (ρ : (ι × Fin 3) → Ω → ℝ≥0)
    (ω : Ω) (i : ι) (hρ : Monotone (fun k => ρ (i,k) ω)) (t : ℝ≥0) (k : Fin 3) :
    k.val+1 ≤ (phaseAt ρ t ω i).val ↔ ρ (i,k) ω ≤ t := by
  have h01 : ρ (i,0) ω ≤ ρ (i,1) ω := hρ (by decide)
  have h12 : ρ (i,1) ω ≤ ρ (i,2) ω := hρ (by decide)
  have h02 := h01.trans h12
  fin_cases k <;> unfold phaseAt <;> split_ifs <;> simp_all <;> linarith

lemma phaseAt_const_sorted_interval {Ω ι : Type*}
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (hl : ∀ σ ∈ l, ∀ ω, σ ω ≤ H) (hρ : ∀ k, ρ k ∈ l)
    (n : ℕ) (ω : Ω) (t : ℝ≥0)
    (hnt : sortedStopAt l H n ω ≤ t) (ht : t < sortedStopAt l H (n+1) ω) :
    phaseAt ρ t ω = phaseAt ρ (sortedStopAt l H n ω) ω := by
  funext i
  simp only [phaseAt, sortedStopAt_reached_iff l H hl _ (hρ (i,2)) n ω t hnt ht,
    sortedStopAt_reached_iff l H hl _ (hρ (i,1)) n ω t hnt ht,
    sortedStopAt_reached_iff l H hl _ (hρ (i,0)) n ω t hnt ht]

lemma phaseAt_crossed_sorted_switch {Ω ι : Type*}
    (ρ : (ι × Fin 3) → Ω → ℝ≥0) (l : List (Ω → ℝ≥0)) (H : ℝ≥0)
    (hl : ∀ σ ∈ l, ∀ ω, σ ω ≤ H) (hρ : ∀ k, ρ k ∈ l)
    (n : ℕ) (ω : Ω) (i : ι) (k : Fin 3)
    (hord : Monotone (fun j => ρ (i,j) ω))
    (hbefore : (phaseAt ρ (sortedStopAt l H n ω) ω i).val ≤ k.val)
    (hafter : k.val+1 ≤ (phaseAt ρ (sortedStopAt l H (n+1) ω) ω i).val) :
    ρ (i,k) ω = sortedStopAt l H (n+1) ω := by
  have hlt : sortedStopAt l H n ω < ρ (i,k) ω := by
    by_contra h
    have hc := (phaseAt_ge_iff ρ ω i hord _ k).mpr (le_of_not_gt h)
    omega
  exact le_antisymm ((phaseAt_ge_iff ρ ω i hord _ k).mp hafter)
    (sortedStopAt_no_intermediate l H hl _ (hρ (i,k)) n ω hlt)

lemma phaseAt_horizon {Ω ι : Type*} (ρ : (ι × Fin 3) → Ω → ℝ≥0)
    (H : ℝ≥0) (hρ : ∀ k ω, ρ k ω ≤ H) (ω : Ω) :
    phaseAt ρ H ω = fun _ => 3 := by
  funext i
  simp only [phaseAt, ite_eq_left (hρ (i,2) ω)]

end SLEExactGauge.Multipoint

end

end OAI
