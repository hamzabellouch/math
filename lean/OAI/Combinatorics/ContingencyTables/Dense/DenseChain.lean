import OAI.Combinatorics.ContingencyTables.Dense.GridMinCut
import OAI.Combinatorics.ContingencyTables.Dense.GridCutFlow
import OAI.Combinatorics.ContingencyTables.Dense.GridMetropolis

namespace OAI

/-!
# Conditional Poincaré bound for the actual dense bin chain

Both published inputs are explicit: finite-box Prékopa interpolation and
finite-chain Cheeger. All margin, penalty, cut, and proposal obligations
for this chain follow from the dense completion geometry.
-/

namespace ContingencyTables.GridBoundary

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q K : ℕ}

def denseBinWeight (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (a : Grid (I := Fin q) K) : ℝ :=
  DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner a)

def denseBinChain (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hfree : Fintype.card (I × J) ≤ d)
    (e : I × J ≃ Fin q) (hK : 1 ≤ K) : FiniteChain (Grid (I := Fin q) K) := by
  have hq : q ≤ d := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin] at hc
    omega
  exact gridChain d hd hq hK (denseBinWeight R P d e) (fun a => DenseWeights.binWeight_pos _ _ _)

def denseCutConstant (d K : ℕ) : ℝ := binProposal d / (128 * (d : ℝ) * K)

private theorem corner_injective : Function.Injective (corner (I := Fin q) (K := K)) := by
  intro a b h
  funext j
  apply Subtype.ext
  exact congrFun h j

theorem denseBinChain_poincare (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q) (hK : 1 ≤ K)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin q) K)) :
    ∀ f : Grid (I := Fin q) K → ℝ,
      (denseBinChain R P d hd hfree e hK).variance f ≤
        (2 / (denseCutConstant d K) ^ 2) * (denseBinChain R P d hd hfree e hK).energy f := by
  classical
  let : DecidableEq (Grid (I := Fin q) K) := Classical.decEq _
  let : Nonempty (Grid (I := Fin q) K) := ⟨fun _ => ⟨0, by constructor <;> omega⟩⟩
  let w := denseBinWeight R P d e (K := K)
  have hw : ∀ a, 0 < w a := fun a => DenseWeights.binWeight_pos _ _ _
  have hq : q ≤ d := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_fin] at hc
    omega
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hK₀ : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hβ := (binProposal_bounds d hd).1
  have hκ : 0 < denseCutConstant d K := by unfold denseCutConstant; positivity
  apply MetropolisChain.poincare_of_weighted_cut w hw Neighbor neighbor_symm (binProposal d) hβ.le
    (2 * q) (fun a => by simpa using neighbor_degree a)
    ((binProposal_degree q d hd hq).trans (by norm_num)) hCheeger (denseCutConstant d K) hκ
  intro S
  change denseCutConstant d K * min (∑ a ∈ S, w a) (∑ a ∈ Sᶜ, w a) ≤
    binProposal d * (∑ a ∈ S, ∑ b ∈ Sᶜ, if Neighbor a b then min (w a) (w b) else 0)
  have hSw : 0 ≤ ∑ a ∈ S, w a := Finset.sum_nonneg (fun a _ => (hw a).le)
  have hScw : 0 ≤ ∑ a ∈ Sᶜ, w a := Finset.sum_nonneg (fun a _ => (hw a).le)
  by_cases hs : S.Nonempty
  · by_cases hsc : Sᶜ.Nonempty
    · let Q : (Fin q → ℤ) → Prop := fun z => ∃ a ∈ S, corner a = z
      have hQ (a : Grid (I := Fin q) K) : Q (corner a) ↔ a ∈ S := by
        constructor
        · rintro ⟨b, hb, he⟩
          exact corner_injective he ▸ hb
        · intro ha
          exact ⟨a, ha, rfl⟩
      have hne : Nonempty (Selected K Q) := by
        obtain ⟨a, ha⟩ := hs
        exact ⟨⟨a, (hQ a).mpr ha⟩⟩
      have hne' : Nonempty (Selected K (fun a => ¬ Q a)) := by
        obtain ⟨a, ha⟩ := hsc
        exact ⟨⟨a, fun h => (Finset.mem_compl.mp ha) ((hQ a).mp h)⟩⟩
      have hdense := denseGrid_min_cut R P d hd hR hP hRmax hPmax hfree e hPL hK Q hne hne'
      change (1 / (128 * (d : ℝ) * K)) *
        min (∑ a : Selected K Q, w a.val) (∑ a : Selected K (fun a => ¬ Q a), w a.val) ≤
          ∑ edge : CutEdge K Q, min (w edge.val.1) (w edge.val.2.1) at hdense
      have hsum : (∑ a : Selected K Q, w a.val) = ∑ a ∈ S, w a := by
        rw [selected_sum_eq_filter Q w]
        apply Finset.sum_congr ?_ (fun _ _ => rfl)
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hQ]
      have hsum' : (∑ a : Selected K (fun a => ¬ Q a), w a.val) = ∑ a ∈ Sᶜ, w a := by
        rw [selected_sum_eq_filter (fun a => ¬ Q a) w]
        apply Finset.sum_congr ?_ (fun _ _ => rfl)
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hQ, Finset.mem_compl]
      rw [hsum, hsum'] at hdense
      have hflow := cut_faces_le_neighbor_flow Q w (fun a => (hw a).le)
      have hflow' : (∑ edge : CutEdge K Q, min (w edge.val.1) (w edge.val.2.1)) ≤
          ∑ a ∈ S, ∑ b ∈ Sᶜ, if Neighbor a b then min (w a) (w b) else 0 := by
        convert hflow using 1
        apply Finset.sum_congr ?_ ?_
        · ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hQ]
        · intro a _
          apply Finset.sum_congr ?_ (fun _ _ => rfl)
          ext b
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hQ, Finset.mem_compl]
      have hbound := hdense.trans hflow'
      calc
        _ = binProposal d * ((1 / (128 * (d : ℝ) * K)) *
            min (∑ a ∈ S, w a) (∑ a ∈ Sᶜ, w a)) := by unfold denseCutConstant; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hbound hβ.le
    · have he : Sᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsc
      rw [he]
      simp only [Finset.sum_empty, min_eq_right hSw, mul_zero, Finset.sum_const_zero]
      exact le_rfl
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [he] at hScw ⊢
    simp only [Finset.sum_empty, min_eq_left hScw, mul_zero]
    exact le_rfl

end

end ContingencyTables.GridBoundary

end OAI
