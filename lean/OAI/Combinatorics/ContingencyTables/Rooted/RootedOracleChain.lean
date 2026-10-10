import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleCut
import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleCorrection
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleChain

namespace OAI

/-! # The actual bin chain for the computed-root forest penalty

All cut geometry is proved from the selected-root density. The only
conditional inputs are the same finite-box Prékopa–Leindler inequality
and finite reversible-chain Cheeger theorem used by the original chain.
-/

namespace ContingencyTables.RootedOracleDensity

open CommonBasesFPRAS GridBoundary CompanionFactorialApplication
open CompanionOracleDensity (dimension height proposal_bounds proposal_degree cutConstant)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

def oracleChain (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) : FiniteChain (Grid (I := Fin (dimension A)) K) := by
  letI : Nonempty (Grid (I := Fin (dimension A)) K) :=
    ⟨fun _ => ⟨0,by constructor <;> omega⟩⟩
  exact MetropolisChain.chain (gridWeight A R C a z) (fun _ => DenseWeights.binWeight_pos _ _ _)
    Neighbor neighbor_symm (binProposal A.d) (proposal_bounds A.d A.hd).1.le
    (2*dimension A) (fun v => by simpa using neighbor_degree v)
    ((proposal_degree A).trans (by norm_num))

lemma oracleChain_pi (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) (v : Grid (I := Fin (dimension A)) K) :
    (oracleChain A R C a z hK).π v = gridWeight A R C a z v/
      ∑ w : Grid (I := Fin (dimension A)) K,gridWeight A R C a z w := rfl

private lemma corner_injective {q K : ℕ} :
    Function.Injective (corner (I := Fin q) (K := K)) := by
  intro a b h
  funext i
  exact Subtype.ext (congrFun h i)

/-- All geometric cut obligations are discharged for the literal forest
penalty. Only finite-box PL and finite-chain Cheeger remain conditional. -/
theorem oracleChain_poincare (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K)) :
    ∀ f, (oracleChain A R C a z hK).variance f ≤
      (2/(cutConstant A K)^2)*(oracleChain A R C a z hK).energy f := by
  classical
  let : DecidableEq (Grid (I := Fin (dimension A)) K) := Classical.decEq _
  let : Nonempty (Grid (I := Fin (dimension A)) K) :=
    ⟨fun _ => ⟨0,by constructor <;> omega⟩⟩
  let w := gridWeight A R C a z (K := K)
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
      have hcut := weighted_min_cut A R C a hC ha haH z K hK hPL Q hne hne'
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
end ContingencyTables.RootedOracleDensity

end OAI
