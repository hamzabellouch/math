import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleCut
import OAI.Combinatorics.ContingencyTables.Dense.GridCutFlow
import OAI.Combinatorics.ContingencyTables.Dense.GridMetropolis

namespace OAI

/-! # The actual finite bin chain for the companion evaluator -/

namespace ContingencyTables.CompanionOracleDensity

open CommonBasesFPRAS GridBoundary CompanionFactorialApplication
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The dyadic proposal is valid already at `d = 1`, including the
zero-dimensional grid. -/
lemma proposal_bounds (d : ℕ) (hd : 1 ≤ d) :
    0 < binProposal d ∧ 1/(16*(d:ℝ)) ≤ binProposal d ∧
      binProposal d ≤ 1/(8*(d:ℝ)) := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hn : 1 < 8*d := by omega
  have hlo := Nat.le_pow_clog (by decide : 1 < 2) (8*d)
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn
  have hpos := Nat.clog_pos (by decide : 1 < 2) hn
  have hhi : 2^Nat.clog 2 (8*d) ≤ 16*d := by
    have he : 2^Nat.clog 2 (8*d) = 2^(Nat.clog 2 (8*d)).pred*2 := by
      conv_lhs => rw [←Nat.succ_pred_eq_of_pos hpos]
      exact pow_succ _ _
    rw [he]
    omega
  have hloR : 8*(d:ℝ) ≤ (2:ℝ)^Nat.clog 2 (8*d) := by exact_mod_cast hlo
  have hhiR : (2:ℝ)^Nat.clog 2 (8*d) ≤ 16*(d:ℝ) := by exact_mod_cast hhi
  refine ⟨by unfold binProposal; positivity,?_,?_⟩
  · exact one_div_le_one_div_of_le (by positivity) hhiR
  · exact one_div_le_one_div_of_le (by positivity) hloR

lemma proposal_degree (A : Instance I J) :
    ((2*dimension A:ℕ):ℝ)*binProposal A.d ≤ 1/4 := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  have he : (dimension A:ℝ) ≤ A.d := by exact_mod_cast ForestScaledPenalty.free_card_le A
  calc
    _ ≤ (2*(dimension A:ℝ))*(1/(8*(A.d:ℝ))) := by
      push_cast
      exact mul_le_mul_of_nonneg_left (proposal_bounds A.d A.hd).2.2 (by positivity)
    _ ≤ (2*(A.d:ℝ))*(1/(8*(A.d:ℝ))) := by gcongr
    _ = 1/4 := by field_simp; ring

def gridWeight (A : Instance I J) (C a : ℝ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℝ := V A C a z (realCorner v)

def oracleChain (A : Instance I J) (C a : ℝ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) : FiniteChain (Grid (I := Fin (dimension A)) K) := by
  letI : Nonempty (Grid (I := Fin (dimension A)) K) :=
    ⟨fun _ => ⟨0,by constructor <;> omega⟩⟩
  exact MetropolisChain.chain (gridWeight A C a z) (fun _ => DenseWeights.binWeight_pos _ _ _)
    Neighbor neighbor_symm (binProposal A.d) (proposal_bounds A.d A.hd).1.le
    (2*dimension A) (fun v => by simpa using neighbor_degree v)
    ((proposal_degree A).trans (by norm_num))

lemma oracleChain_pi (A : Instance I J) (C a : ℝ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) :
    (oracleChain A C a z hK).π v = gridWeight A C a z v/
      ∑ w : Grid (I := Fin (dimension A)) K,gridWeight A C a z w := rfl

def cutConstant (A : Instance I J) (K : ℕ) : ℝ := binProposal A.d/(128*(A.d:ℝ)*K)

private lemma corner_injective {q K : ℕ} :
    Function.Injective (corner (I := Fin q) (K := K)) := by
  intro a b h
  funext i
  exact Subtype.ext (congrFun h i)

/-- All geometric cut obligations are discharged for the literal forest
penalty. Only finite-box PL and finite-chain Cheeger remain conditional. -/
theorem oracleChain_poincare (A : Instance I J) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K)) :
    ∀ f, (oracleChain A C a z hK).variance f ≤
      (2/(cutConstant A K)^2)*(oracleChain A C a z hK).energy f := by
  classical
  let : DecidableEq (Grid (I := Fin (dimension A)) K) := Classical.decEq _
  let : Nonempty (Grid (I := Fin (dimension A)) K) :=
    ⟨fun _ => ⟨0,by constructor <;> omega⟩⟩
  let w := gridWeight A C a z (K := K)
  have hw : ∀ v,0 < w v := fun _ => DenseWeights.binWeight_pos _ _ _
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  have hKR : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hb := (proposal_bounds A.d A.hd).1
  have hk : 0 < cutConstant A K := by unfold cutConstant; positivity
  apply MetropolisChain.poincare_of_weighted_cut w hw Neighbor neighbor_symm
    (binProposal A.d) hb.le (2*dimension A) (fun v => by simpa using neighbor_degree v)
    ((proposal_degree A).trans (by norm_num)) hCheeger (cutConstant A K) hk
  intro S
  change cutConstant A K*min (∑ v ∈ S,w v) (∑ v ∈ Sᶜ,w v) ≤
    binProposal A.d*(∑ v ∈ S,∑ u ∈ Sᶜ,if Neighbor v u then min (w v) (w u) else 0)
  have hS : 0 ≤ ∑ v ∈ S,w v := Finset.sum_nonneg (fun _ _ => (hw _).le)
  have hSc : 0 ≤ ∑ v ∈ Sᶜ,w v := Finset.sum_nonneg (fun _ _ => (hw _).le)
  by_cases hs : S.Nonempty
  · by_cases hsc : Sᶜ.Nonempty
    · let Q : (Fin (dimension A) → ℤ) → Prop := fun x => ∃ v ∈ S,corner v=x
      have hQ (v : Grid (I := Fin (dimension A)) K) : Q (corner v) ↔ v∈S := by
        constructor
        · rintro ⟨u,hu,he⟩
          exact corner_injective he ▸ hu
        · intro hv
          exact ⟨v,hv,rfl⟩
      have hne : Nonempty (Selected K Q) := by
        obtain ⟨v,hv⟩ := hs
        exact ⟨⟨v,(hQ v).mpr hv⟩⟩
      have hne' : Nonempty (Selected K (fun x => ¬Q x)) := by
        obtain ⟨v,hv⟩ := hsc
        exact ⟨⟨v,fun h => (Finset.mem_compl.mp hv) ((hQ v).mp h)⟩⟩
      have hcut := weighted_min_cut A C a hC ha haH z K hK hPL Q hne hne'
      change (1/(128*(A.d:ℝ)*K))*
        min (∑ v : Selected K Q,w v.val) (∑ v : Selected K (fun x => ¬Q x),w v.val) ≤
          ∑ e : CutEdge K Q,min (w e.val.1) (w e.val.2.1) at hcut
      have hsum : (∑ v : Selected K Q,w v.val)=∑ v∈S,w v := by
        rw [selected_sum_eq_filter Q w]
        apply Finset.sum_congr ?_ (fun _ _ => rfl)
        ext v
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,hQ]
      have hsum' : (∑ v : Selected K (fun x => ¬Q x),w v.val)=∑ v∈Sᶜ,w v := by
        rw [selected_sum_eq_filter (fun x => ¬Q x) w]
        apply Finset.sum_congr ?_ (fun _ _ => rfl)
        ext v
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,hQ,Finset.mem_compl]
      rw [hsum,hsum'] at hcut
      have hflow := cut_faces_le_neighbor_flow Q w (fun v => (hw v).le)
      have hflow' : (∑ e : CutEdge K Q,min (w e.val.1) (w e.val.2.1)) ≤
          ∑ v∈S,∑ u∈Sᶜ,if Neighbor v u then min (w v) (w u) else 0 := by
        convert hflow using 1
        apply Finset.sum_congr ?_ ?_
        · ext v
          simp only [Finset.mem_filter,Finset.mem_univ,true_and,hQ]
        · intro v _
          apply Finset.sum_congr ?_ (fun _ _ => rfl)
          ext u
          simp only [Finset.mem_filter,Finset.mem_univ,true_and,hQ,Finset.mem_compl]
      calc
        _ = binProposal A.d*((1/(128*(A.d:ℝ)*K))*min (∑ v∈S,w v) (∑ v∈Sᶜ,w v)) := by
          unfold cutConstant
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcut.trans hflow') hb.le
    · have he : Sᶜ=∅ := Finset.not_nonempty_iff_eq_empty.mp hsc
      rw [he]
      simp only [Finset.sum_empty,min_eq_right hS,mul_zero,Finset.sum_const_zero]
      exact le_rfl
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [he] at hSc ⊢
    simp only [Finset.sum_empty,min_eq_left hSc,mul_zero]
    exact le_rfl

end

end ContingencyTables.CompanionOracleDensity

end OAI
