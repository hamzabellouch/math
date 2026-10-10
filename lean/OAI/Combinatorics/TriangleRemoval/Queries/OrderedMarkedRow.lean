import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.ProspectiveFailure

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

noncomputable def orderedMarkedRow {K : Type*} [DecidableEq K] {N : ℕ}
    (order : List K) (S : Finset K) (p : K → Fin N → PMF (Bool × Bool))
    (deadline : ℕ) (ω : K → Fin N) : List MarkedChild :=
  (order.map (rowChild S p deadline ω)).mergeSort
    (fun a b => decide (a.priority ≤ b.priority))

theorem orderedMarkedRow_sorted {K : Type*} [DecidableEq K] {N : ℕ}
    (order : List K) (S : Finset K) (p : K → Fin N → PMF (Bool × Bool))
    (deadline : ℕ) (ω : K → Fin N) :
    (orderedMarkedRow order S p deadline ω).Pairwise (fun a b => a.priority ≤ b.priority) := by
  unfold orderedMarkedRow
  simpa only [decide_eq_true_eq] using List.pairwise_mergeSort
    (le := fun a b : MarkedChild => decide (a.priority ≤ b.priority))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true,decide_eq_true_eq]; omega) _

theorem orderedMarkedRow_factor_product {K : Type*} [Fintype K] [DecidableEq K] {N : ℕ}
    (order : List K) (horder : order.Perm Finset.univ.toList)
    (S : Finset K) (p : K → Fin N → PMF (Bool × Bool))
    (deadline t : ℕ) (ω : K → Fin N) :
    ((orderedMarkedRow order S p deadline ω).map
      (chargedFactor (fun a => decide (a.priority < t)))).prod =
    ∏ k, chargedFactor (fun a => decide (a.priority < t)) (rowChild S p deadline ω k) := by
  unfold orderedMarkedRow
  rw [(List.mergeSort_perm _ _).map _ |>.prod_eq,List.map_map]
  rw [(horder.map _).prod_eq]
  exact Finset.prod_map_toList _ _

theorem orderedMarkedRow_pointwise {K : Type*} [Fintype K] [DecidableEq K] {N : ℕ}
    (order : List K) (horder : order.Perm Finset.univ.toList)
    (S : Finset K) (p : K → Fin N → PMF (Bool × Bool))
    (deadline t : ℕ) (htd : t ≤ deadline) (ω : K → Fin N)
    (hsel : ∀ k ∈ S, (ω k).val < deadline)
    (ht : ∃ k ∈ S, t ≤ (ω k).val) :
    markedGood (markedCheck (orderedMarkedRow order S p deadline ω)) ≤
      ∏ k, if k ∈ S then markedGood (p k (ω k))
        else if (ω k).val < t then markedFailure (p k (ω k)) else 1 := by
  have hw : ∃ a ∈ orderedMarkedRow order S p deadline ω,
      a.required = true ∧ t ≤ a.priority := by
    obtain ⟨k,hk,hkt⟩ := ht
    refine ⟨rowChild S p deadline ω k, ?_, ?_, hkt⟩
    · simp only [orderedMarkedRow,List.mem_mergeSort,List.mem_map]
      exact ⟨k,horder.mem_iff.mpr (by simp),rfl⟩
    · simpa only [rowChild,decide_eq_true_eq] using hk
  have hb := marked_visitation_priority _ t (orderedMarkedRow_sorted order S p deadline ω) hw
  rw [orderedMarkedRow_factor_product order horder] at hb
  convert hb using 1
  apply Finset.prod_congr rfl
  intro k _
  by_cases hk : k ∈ S
  · simp [chargedFactor,rowChild,hk,hsel k hk]
  · by_cases hkt : (ω k).val < t
    · have hkd : (ω k).val < deadline := lt_of_lt_of_le hkt htd
      simp [chargedFactor,rowChild,hk,hkt,hkd]
    · simp [chargedFactor,rowChild,hk,hkt]

theorem orderedMarkedRow_integrated {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (order : List K) (horder : order.Perm Finset.univ.toList)
    (S : Finset K) (σ : K → Fin N)
    (p : K → Fin N → PMF (Bool × Bool)) (deadline t : ℕ)
    (htd : t ≤ deadline) (hsel : ∀ k ∈ S, (σ k).val < deadline)
    (ht : ∃ k ∈ S, t ≤ (σ k).val) :
    pmfMean (productPMF (selectedClockLaw N S σ))
      (fun ω => markedGood (markedCheck (orderedMarkedRow order S p deadline ω))) ≤
    ∏ k, if k ∈ S then markedGood (p k (σ k)) else
      1 - (∑ u : Fin N, if u.val < t then markedSuccess (p k u) else 0) / (N : ℝ) := by
  calc
    _ ≤ pmfMean (productPMF (selectedClockLaw N S σ))
        (fun ω => ∏ k, if k ∈ S then markedGood (p k (ω k))
          else if (ω k).val < t then markedFailure (p k (ω k)) else 1) := by
      apply pmfMean_mono
      intro ω hω
      have he := selectedClockLaw_support N S σ ω hω
      apply orderedMarkedRow_pointwise order horder S p deadline t htd ω
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

theorem orderedMarkedRow_cavity_bound {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (order : List K) (horder : order.Perm Finset.univ.toList)
    (S : Finset K) (σ : K → Fin N)
    (p : K → Fin N → PMF (Bool × Bool)) (q : K → Fin N → ℝ)
    (deadline t : ℕ) (htd : t ≤ deadline) (hsel : ∀ k ∈ S, (σ k).val < deadline)
    (ht : ∃ k ∈ S, t ≤ (σ k).val) (hS : S.card ≤ 2)
    (hmarg : ∀ k ∉ S, ∀ u, markedSuccess (p k u) = q k u)
    (b : ℝ) (hfactor : ∀ k, (7 / 8 : ℝ) ≤ prospectiveFailure N t (q k))
    (hfull : ∏ k, prospectiveFailure N t (q k) ≤ (9 / 8 : ℝ) * b) :
    markedGood ((productPMF (selectedClockLaw N S σ)).bind
      (fun ω => markedCheck (orderedMarkedRow order S p deadline ω))) ≤
      (∏ k ∈ S, markedGood (p k (σ k))) * (2 * b) := by
  rw [markedGood_bind]
  have h := orderedMarkedRow_integrated N order horder S σ p deadline t htd hsel ht
  let f : K → ℝ := fun k => prospectiveFailure N t (q k)
  have he : (∏ k, if k ∈ S then markedGood (p k (σ k)) else
      1 - (∑ u : Fin N, if u.val < t then markedSuccess (p k u) else 0) / (N : ℝ)) =
      (∏ k ∈ S, markedGood (p k (σ k))) * (∏ k ∈ Finset.univ \ S, f k) := by
    have hp : (fun k => if k ∈ S then markedGood (p k (σ k)) else
        1 - (∑ u : Fin N, if u.val < t then markedSuccess (p k u) else 0) / (N : ℝ)) =
        (fun k => if k ∈ S then markedGood (p k (σ k)) else f k) := by
      funext k
      by_cases hk : k ∈ S
      · simp only [hk,↓reduceIte]
      · simp only [hk,↓reduceIte,f,prospectiveFailure,hmarg k hk]
    rw [hp,Finset.prod_ite]
    congr 1
    · congr 1
      ext k
      simp
    · congr 1
      ext k
      simp
  rw [he] at h
  have hf := offpattern_product_bound Finset.univ S (Finset.subset_univ S) hS f b
    (fun k _ => hfactor k) hfull
  exact h.trans (mul_le_mul_of_nonneg_left hf (Finset.prod_nonneg
    (fun k _ => markedGood_nonneg (p k (σ k)))))

end SharpTerminalLeave

end

end OAI
