import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.MarkedDemand
import OAI.Combinatorics.TriangleRemoval.Probability.ProductPMFMeanProduct

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave

noncomputable def markedSuccess (p : PMF (Bool × Bool)) : ℝ :=
  pmfMean p (fun z => if z.1 then 1 else 0)

@[simp] theorem markedFailure_eq_one_sub (p : PMF (Bool × Bool)) :
    markedFailure p = 1 - markedSuccess p := by
  unfold markedFailure markedSuccess
  rw [← pmfMean_const p 1, ← pmfMean_sub]
  apply pmfMean_congr
  intro z _
  cases z.1 <;> simp

noncomputable def selectedClockLaw {K : Type*} [DecidableEq K]
    (N : ℕ) [NeZero N] (S : Finset K) (σ : K → Fin N) (k : K) : PMF (Fin N) :=
  if k ∈ S then PMF.pure (σ k) else PMF.uniformOfFintype (Fin N)

theorem selectedClockLaw_support {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (S : Finset K) (σ ω : K → Fin N)
    (hω : ω ∈ (productPMF (selectedClockLaw N S σ)).support) :
    ∀ k ∈ S, ω k = σ k := by
  intro k hk
  have h := (productPMF_support _ ω).mp hω k
  simpa [selectedClockLaw,hk] using h

noncomputable def rowChild {K : Type*} [DecidableEq K] {N : ℕ}
    (S : Finset K) (p : K → Fin N → PMF (Bool × Bool))
    (deadline : ℕ) (ω : K → Fin N) (k : K) : MarkedChild :=
  ⟨decide (k ∈ S), if (ω k).val < deadline then p k (ω k)
      else PMF.pure (false,false), (ω k).val⟩

noncomputable def markedRow {K : Type*} [Fintype K] [DecidableEq K] {N : ℕ}
    (S : Finset K) (p : K → Fin N → PMF (Bool × Bool))
    (deadline : ℕ) (ω : K → Fin N) : List MarkedChild :=
  ((Finset.univ.toList).map (rowChild S p deadline ω)).mergeSort
    (fun a b => decide (a.priority ≤ b.priority))

theorem markedRow_sorted {K : Type*} [Fintype K] [DecidableEq K] {N : ℕ}
    (S : Finset K) (p : K → Fin N → PMF (Bool × Bool))
    (deadline : ℕ) (ω : K → Fin N) :
    (markedRow S p deadline ω).Pairwise (fun a b => a.priority ≤ b.priority) := by
  unfold markedRow
  simpa only [decide_eq_true_eq] using List.pairwise_mergeSort
    (le := fun a b : MarkedChild => decide (a.priority ≤ b.priority))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true,decide_eq_true_eq]; omega) _

theorem markedRow_factor_product {K : Type*} [Fintype K] [DecidableEq K] {N : ℕ}
    (S : Finset K) (p : K → Fin N → PMF (Bool × Bool))
    (deadline t : ℕ) (ω : K → Fin N) :
    ((markedRow S p deadline ω).map
      (chargedFactor (fun a => decide (a.priority < t)))).prod =
    ∏ k, chargedFactor (fun a => decide (a.priority < t)) (rowChild S p deadline ω k) := by
  unfold markedRow
  rw [(List.mergeSort_perm _ _).map _ |>.prod_eq,List.map_map]
  exact Finset.prod_map_toList _ _

theorem markedRow_pointwise {K : Type*} [Fintype K] [DecidableEq K] {N : ℕ}
    (S : Finset K) (p : K → Fin N → PMF (Bool × Bool))
    (deadline t : ℕ) (htd : t ≤ deadline) (ω : K → Fin N)
    (hsel : ∀ k ∈ S, (ω k).val < deadline)
    (ht : ∃ k ∈ S, t ≤ (ω k).val) :
    markedGood (markedCheck (markedRow S p deadline ω)) ≤
      ∏ k, if k ∈ S then markedGood (p k (ω k))
        else if (ω k).val < t then markedFailure (p k (ω k)) else 1 := by
  have hw : ∃ a ∈ markedRow S p deadline ω, a.required = true ∧ t ≤ a.priority := by
    obtain ⟨k,hk,hkt⟩ := ht
    refine ⟨rowChild S p deadline ω k, ?_, ?_, hkt⟩
    · simp only [markedRow,List.mem_mergeSort,List.mem_map,Finset.mem_toList]
      exact ⟨k,Finset.mem_univ _,rfl⟩
    · simpa only [rowChild,decide_eq_true_eq] using hk
  have hb := marked_visitation_priority _ t (markedRow_sorted S p deadline ω) hw
  rw [markedRow_factor_product] at hb
  convert hb using 1
  apply Finset.prod_congr rfl
  intro k _
  by_cases hk : k ∈ S
  · simp [chargedFactor,rowChild,hk,hsel k hk]
  · by_cases hkt : (ω k).val < t
    · have hkd : (ω k).val < deadline := lt_of_lt_of_le hkt htd
      simp [chargedFactor,rowChild,hk,hkt,hkd]
    · simp [chargedFactor,rowChild,hk,hkt]

theorem markedRow_integrated {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (S : Finset K) (σ : K → Fin N)
    (p : K → Fin N → PMF (Bool × Bool)) (deadline t : ℕ)
    (htd : t ≤ deadline) (hsel : ∀ k ∈ S, (σ k).val < deadline)
    (ht : ∃ k ∈ S, t ≤ (σ k).val) :
    pmfMean (productPMF (selectedClockLaw N S σ))
      (fun ω => markedGood (markedCheck (markedRow S p deadline ω))) ≤
    ∏ k, if k ∈ S then markedGood (p k (σ k)) else
      1 - (∑ u : Fin N, if u.val < t then markedSuccess (p k u) else 0) / (N : ℝ) := by
  calc
    _ ≤ pmfMean (productPMF (selectedClockLaw N S σ))
        (fun ω => ∏ k, if k ∈ S then markedGood (p k (ω k))
          else if (ω k).val < t then markedFailure (p k (ω k)) else 1) := by
      apply pmfMean_mono
      intro ω hω
      have he := selectedClockLaw_support N S σ ω hω
      apply markedRow_pointwise S p deadline t htd ω
      · intro k hk
        simpa only [he k hk] using hsel k hk
      · obtain ⟨k,hk,htk⟩ := ht
        exact ⟨k,hk,by rwa [he k hk]⟩
    _ = _ := by
      rw [productPMF_mean_product (selectedClockLaw N S σ)
        (fun k u => if k ∈ S then markedGood (p k u)
          else if u.val < t then markedFailure (p k u) else 1)]
      apply Finset.prod_congr rfl
      intro k _
      by_cases hk : k ∈ S
      · simp [selectedClockLaw,hk]
      · simp only [selectedClockLaw,hk,↓reduceIte,markedFailure_eq_one_sub]
        exact uniform_prospective_failure N t (fun u => markedSuccess (p k u))

end SharpTerminalLeave

end

end OAI
