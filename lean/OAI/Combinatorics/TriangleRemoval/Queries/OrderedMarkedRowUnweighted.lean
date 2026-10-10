import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.OrderedMarkedRow

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

theorem orderedMarkedRow_unweighted {K : Type*} [Fintype K] [DecidableEq K] {N : ℕ}
    (order : List K) (horder : order.Perm Finset.univ.toList)
    (S : Finset K) (p : K → Fin N → PMF (Bool × Bool)) (deadline : ℕ) (ω : K → Fin N) :
    markedGood (markedCheck (orderedMarkedRow order S p deadline ω)) ≤
      ∏ k ∈ S, if (ω k).val < deadline then markedGood (p k (ω k)) else 0 := by
  have hc : ChargesCovered (fun _ => false) (orderedMarkedRow order S p deadline ω) := by
    intro pre a post hh ha hb
    simp at hb
  have hb := marked_visitation_charged _ _ hc
  refine hb.trans_eq ?_
  unfold orderedMarkedRow
  rw [(List.mergeSort_perm _ _).map _ |>.prod_eq,List.map_map,(horder.map _).prod_eq,
    Finset.prod_map_toList]
  calc
    _ = ∏ k, if k ∈ S then
        (if (ω k).val < deadline then markedGood (p k (ω k)) else 0) else 1 := by
      apply Finset.prod_congr rfl
      intro k _
      by_cases hk : k ∈ S
      · by_cases hu : (ω k).val < deadline
        · simp [chargedFactor,rowChild,hk,hu]
        · simp [chargedFactor,rowChild,hk,hu,markedGood]
      · simp [chargedFactor,rowChild,hk]
    _ = _ := by
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one,mul_one]
      congr 1
      ext k
      simp

theorem orderedMarkedRow_forbidden {K : Type*} [Fintype K] [DecidableEq K] {N : ℕ}
    (order : List K) (horder : order.Perm Finset.univ.toList)
    (S : Finset K) (p : K → Fin N → PMF (Bool × Bool)) (deadline : ℕ) (ω : K → Fin N)
    (k : K) (hk : k ∈ S) (hu : deadline ≤ (ω k).val) :
    markedGood (markedCheck (orderedMarkedRow order S p deadline ω)) = 0 := by
  apply le_antisymm _ (markedGood_nonneg _)
  have hb := orderedMarkedRow_unweighted order horder S p deadline ω
  have hz : (∏ a ∈ S, if (ω a).val < deadline then markedGood (p a (ω a)) else 0) = 0 := by
    apply Finset.prod_eq_zero hk
    simp only [not_lt_of_ge hu,↓reduceIte]
  rwa [hz] at hb

theorem selectedClockLaw_singleton {K : Type*} [DecidableEq K]
    (N : ℕ) [NeZero N] (a : K) (u : Fin N) :
    selectedClockLaw N {a} (fun _ => u) =
      Function.update (fun _ : K => PMF.uniformOfFintype (Fin N)) a (PMF.pure u) := by
  funext k
  by_cases hk : k = a
  · subst k
    simp [selectedClockLaw]
  · simp [selectedClockLaw,hk]

theorem marked_row_single_path {K : Type*} [Fintype K] [DecidableEq K]
    (N : ℕ) [NeZero N] (order : List K) (horder : order.Perm Finset.univ.toList)
    (a : K) (p : K → Fin N → PMF (Bool × Bool)) (q : K → Fin N → ℝ)
    (deadline : ℕ) (b : ℕ → ℝ)
    (hmarg : ∀ k ≠ a, ∀ u, markedSuccess (p k u) = q k u)
    (hfactor : ∀ t < deadline, ∀ k, (7 / 8 : ℝ) ≤ prospectiveFailure N t (q k))
    (hfull : ∀ t < deadline, ∏ k, prospectiveFailure N t (q k) ≤ (9 / 8 : ℝ) * b t) :
    markedGood ((productPMF (fun _ : K => PMF.uniformOfFintype (Fin N))).bind
      (fun ω => markedCheck (orderedMarkedRow order {a} p deadline ω))) ≤
      (1 / (N : ℝ)) * ∑ u : Fin N,
        if u.val < deadline then markedGood (p a u) * (2 * b u.val) else 0 := by
  rw [productPMF_split (fun _ : K => PMF.uniformOfFintype (Fin N)) a,
    PMF.bind_bind,markedGood_bind]
  have hpoint : ∀ u : Fin N,
      markedGood ((productPMF (Function.update (fun _ : K => PMF.uniformOfFintype (Fin N))
        a (PMF.pure u))).bind
        (fun ω => markedCheck (orderedMarkedRow order {a} p deadline ω))) ≤
      if u.val < deadline then markedGood (p a u) * (2 * b u.val) else 0 := by
    intro u
    rw [← selectedClockLaw_singleton N a u]
    by_cases hu : u.val < deadline
    · simp only [hu,↓reduceIte]
      have hs : ∀ k ∈ ({a} : Finset K), ((fun _ => u) k).val < deadline := by
        intro k _
        exact hu
      have ht : ∃ k ∈ ({a} : Finset K), u.val ≤ ((fun _ => u) k).val := ⟨a,by simp,le_rfl⟩
      simpa only [Finset.prod_singleton] using orderedMarkedRow_cavity_bound N order horder {a}
        (fun _ => u) p q deadline u.val (Nat.le_of_lt hu) hs ht (by simp)
        (fun k hk v => hmarg k (by simpa only [Finset.mem_singleton] using hk) v)
        (b u.val) (hfactor u.val hu) (hfull u.val hu)
    · simp only [hu,↓reduceIte]
      rw [markedGood_bind]
      apply le_trans (pmfMean_mono _ (g := fun _ => 0) ?_) (by simp)
      intro ω hω
      have he := selectedClockLaw_support N {a} (fun _ => u) ω hω a (by simp)
      rw [orderedMarkedRow_forbidden order horder {a} p deadline ω a (by simp)
        (by simpa only [he] using Nat.le_of_not_gt hu)]
  calc
    _ ≤ pmfMean (PMF.uniformOfFintype (Fin N))
        (fun u => if u.val < deadline then markedGood (p a u) * (2 * b u.val) else 0) :=
      pmfMean_mono _ (fun u _ => hpoint u)
    _ = _ := by
      simp only [pmfMean,PMF.uniformOfFintype_apply,ENNReal.toReal_inv,
        ENNReal.toReal_natCast,Fintype.card_fin,one_div,Finset.mul_sum]

end SharpTerminalLeave

end

end OAI
