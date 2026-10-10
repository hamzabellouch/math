import OAI.Probability.SwitchChain.PairFiberSliceComparison
import OAI.Probability.SwitchChain.PairSwapInjectivity

namespace OAI

noncomputable section
namespace Problem315.PairFiber
open SlicePermutationAction

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem assignmentRelabel_injective_on_nontrivial (G : SimpleGraph V) (i j : V)
    (T : Assignment G i j) {σ τ : Equiv.Perm (singletonSet G i j)}
    (hσ : σ.IsSwap) (hτ : τ.IsSwap)
    (hneσ : assignmentRelabel G i j σ T ≠ T)
    (hneτ : assignmentRelabel G i j τ T ≠ T)
    (h : assignmentRelabel G i j σ T = assignmentRelabel G i j τ T) : σ = τ := by
  let e := assignmentSliceEquiv G i j
  apply map_swap_injective_on_nontrivial (e T).val hσ hτ
  · intro hh
    apply hneσ
    apply e.injective
    change e (e.symm (relabel σ (e T))) = e T
    rw [e.apply_symm_apply]
    exact Subtype.ext hh
  · intro hh
    apply hneτ
    apply e.injective
    change e (e.symm (relabel τ (e T))) = e T
    rw [e.apply_symm_apply]
    exact Subtype.ext hh
  · have hh := congrArg (fun U => (e U).val) h
    simpa only [assignmentRelabel, Equiv.apply_symm_apply, e, relabel] using hh

theorem exists_crossingProposal_of_key_leftSet_swap {n : ℕ} {d : Fin n → ℕ}
    (G H : GraphState n d) (i j u v : Fin n) (hij : i ≠ j)
    (hu : u ∈ singletonSet G.val i j) (hv : v ∈ singletonSet G.val i j)
    (hkey : key i j H.val = key i j G.val)
    (hleft : leftSet H.val i j =
      (leftSet G.val i j).map (Equiv.swap u v).toEmbedding)
    (hne : H ≠ G) :
    ∃ p : SwitchProposal n, validSwitch G.val p ∧
      ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p ∧
      proposalResult G.val p = H.val := by
  classical
  have hnot (hm : u ∈ leftSet G.val i j ↔ v ∈ leftSet G.val i j) : False := by
    apply hne
    apply Subtype.ext
    apply graph_eq_of_key_leftSet_eq hkey
    rw [hleft, map_swap_eq_self_of_mem_iff _ u v hm]
  by_cases hul : u ∈ leftSet G.val i j
  · by_cases hvl : v ∈ leftSet G.val i j
    · exact False.elim (hnot (by simp [hul, hvl]))
    · exact exists_crossingProposal_of_key_leftSet_exchange G H i j u v hij
        hul hv hvl hkey (hleft.trans (map_swap_eq_exchange _ u v hul hvl))
  · by_cases hvl : v ∈ leftSet G.val i j
    · apply exists_crossingProposal_of_key_leftSet_exchange G H i j v u hij
        hvl hu hul hkey
      rw [hleft, Equiv.swap_comm u v]
      exact map_swap_eq_exchange _ v u hvl hul
    · exact False.elim (hnot (by simp [hul, hvl]))

theorem assignmentRelabel_exists_crossingProposal {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (T : Assignment G.val i j) (σ : Equiv.Perm (singletonSet G.val i j))
    (hσ : σ.IsSwap) (hne : assignmentRelabel G.val i j σ T ≠ T) :
    let H := ((stateFiberEquiv G i j hij).symm T).val
    let K := ((stateFiberEquiv G i j hij).symm
      (assignmentRelabel G.val i j σ T)).val
    ∃ p : SwitchProposal n, validSwitch H.val p ∧
      ({i, j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p ∧
      proposalResult H.val p = K.val := by
  classical
  obtain ⟨x, y, _, rfl⟩ := hσ
  let H := ((stateFiberEquiv G i j hij).symm T).val
  let K := ((stateFiberEquiv G i j hij).symm
    (assignmentRelabel G.val i j (Equiv.swap x y) T)).val
  have hkH : key i j H.val = key i j G.val :=
    ((stateFiberEquiv G i j hij).symm T).property
  have hkK : key i j K.val = key i j G.val :=
    ((stateFiberEquiv G i j hij).symm _).property
  have hlH : leftSet H.val i j = T.val := leftSet_trade G.val i j hij T.val T.property.1
  have hlK : leftSet K.val i j =
      T.val.map (Equiv.swap x.val y.val).toEmbedding := by
    exact (leftSet_trade G.val i j hij
      (assignmentRelabel G.val i j (Equiv.swap x y) T).val
      (assignmentRelabel G.val i j (Equiv.swap x y) T).property.1).trans
        (assignmentRelabel_swap_val G.val i j x y T)
  apply exists_crossingProposal_of_key_leftSet_swap H K i j x.val y.val hij
  · rw [singletonSet_eq_of_key_eq hkH]
    exact x.property
  · rw [singletonSet_eq_of_key_eq hkH]
    exact y.property
  · exact hkK.trans hkH.symm
  · rw [hlK, hlH]
  · intro heq
    apply hne
    apply Subtype.ext
    have hh := congrArg (fun F : GraphState n d => leftSet F.val i j) heq
    rw [hlH] at hh
    exact (leftSet_trade G.val i j hij
      (assignmentRelabel G.val i j (Equiv.swap x y) T).val
      (assignmentRelabel G.val i j (Equiv.swap x y) T).property.1).symm.trans hh

end Problem315.PairFiber

end

end OAI
