import Mathlib
import OAI.Probability.LogConcave.JetEstimates.ReindexedMatrix
import OAI.Probability.LogConcave.JetEstimates.ForestTensor

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators
open TensorEnergy

lemma spatialTensor_of_arrayBound {d : ℕ} {S K : Type} [Fintype S] [DecidableEq S] [Fintype K]
    {g : Point d → (S → Fin d) → ℝ} (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (l : List K) (hl : l.Nodup) (hall : ∀k,k∈l) (y : Point d) {B : ℝ}
    (hb : AllSplitBound (arrayTensor (iteratedFDeriv ℝ (Fintype.card K) g y)) B) :
    AllSplitBound (spatialTensor (fun c z => g z c) l y) B := by
  let e := (Fintype.equivFin K).symm
  have hp : ((List.finRange (Fintype.card K)).map e).Perm l :=
    fullList_perm ((List.nodup_finRange _).map e.injective) hl
      (fun k => by simp only [List.mem_map]; exact ⟨e.symm k,by simp,e.apply_symm_apply k⟩) hall
  have hb' : AllSplitBound (spatialTensor (fun c z => g z c) (List.finRange (Fintype.card K)) y) B := by
    rw [spatialTensor_eq_arrayTensor hg y]
    exact hb.reindex (Equiv.sumComm S (Fin (Fintype.card K)))
  have hh := spatialTensor_allSplit_relabel (fun c z => g z c)
    (fun c => (ContinuousLinearMap.proj c : ((S → Fin d) → ℝ) →L[ℝ] ℝ).contDiff.comp hg) (Equiv.refl S) e
    (List.finRange (Fintype.card K)) l hp y B hb'
  simpa only [Function.comp_def,Equiv.refl_apply] using hh

lemma arrayBound_spatialContract {d j : ℕ} {S T : Type} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    [Nonempty S] [Nonempty T]
    {f : Point d → (S ⊕ Unit → Fin d) → ℝ} {g : Point d → (T ⊕ Unit → Fin d) → ℝ}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (hg : ContDiff ℝ (⊤:ℕ∞) g)
    (A B : ℕ → ℝ) (hA : ∀k,0≤A k) (hB : ∀k,0≤B k) (y : Point d)
    (ha : ∀k≤j,AllSplitBound (arrayTensor (iteratedFDeriv ℝ k f y)) (A k))
    (hb : ∀k≤j,AllSplitBound (arrayTensor (iteratedFDeriv ℝ k g y)) (B k)) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ j
      (fun z => singleContract (f z) (g z)) y))
      (∑s∈(Finset.univ : Finset (Fin j)).powerset,A s.card*B (j-s.card)) := by
  let : DecidableEq (Fin j) := Classical.decEq _
  have hfc (c) : ContDiff ℝ (⊤:ℕ∞) (fun z => f z c) :=
    (ContinuousLinearMap.proj c : ((S ⊕ Unit → Fin d) → ℝ) →L[ℝ] ℝ).contDiff.comp hf
  have hgc (c) : ContDiff ℝ (⊤:ℕ∞) (fun z => g z c) :=
    (ContinuousLinearMap.proj c : ((T ⊕ Unit → Fin d) → ℝ) →L[ℝ] ℝ).contDiff.comp hg
  have hc : ContDiff ℝ (⊤:ℕ∞) (fun z => singleContract (f z) (g z)) := by
    apply contDiff_pi.mpr
    intro c
    exact ContDiff.sum (fun z _ => (hfc _).mul (hgc _))
  have he := spatialTensor_singleContract (fun c z => f z c) (fun c z => g z c)
    hfc hgc (List.finRange j) (List.nodup_finRange j) y
  have hs : AllSplitBound (spatialTensor (fun c z => singleContract (f z) (g z) c) (List.finRange j) y)
      (∑s∈(Finset.univ : Finset (Fin j)).powerset,A s.card*B (j-s.card)) := by
    have he' : spatialTensor (fun c z => singleContract (f z) (g z) c) (List.finRange j) y=
        fun c => ∑s∈(Finset.univ : Finset (Fin j)).powerset,
          spatialContractTerm (fun k => k∈s) (fun c z => f z c) (fun c z => g z c) (List.finRange j) y c := by
      funext c
      have heq : (List.finRange j).toFinset=(Finset.univ : Finset (Fin j)) := by
        ext k
        simp
      simpa only [heq] using he c
    rw [he']
    apply AllSplitBound.sum
    · intro s _; exact mul_nonneg (hA _) (hB _)
    · intro s _
      have hn : s.card≤j := (Finset.card_le_univ s).trans_eq (Fintype.card_fin j)
      have hfs := spatialTensor_of_arrayBound (K:=s) (B:=A s.card) hf (selectList (fun k => k∈s) (List.finRange j))
        (selectList_nodup _ (List.nodup_finRange _)) (selectList_full _ (by simp)) y
        (by rw [Fintype.card_coe]; exact ha s.card hn)
      have hgs := spatialTensor_of_arrayBound (K:={k : Fin j // k∉s}) (B:=B (j-s.card)) hg (selectList (fun k => k∉s) (List.finRange j))
        (selectList_nodup _ (List.nodup_finRange _)) (selectList_full _ (by simp)) y
        (by rw [Fintype.card_subtype_compl,Fintype.card_coe,Fintype.card_fin]; exact hb (j-s.card) (Nat.sub_le j s.card))
      exact spatialContractTerm_allSplit (fun k => k∈s) hfs hgs
  rw [spatialTensor_eq_arrayTensor hc y] at hs
  have hh := hs.reindex (Equiv.sumComm (Fin j) (S ⊕ T))
  simpa only [Function.comp_def,Equiv.sumComm_apply,Sum.swap_swap] using hh
end LogConcaveSampling

end

end

end

end OAI
