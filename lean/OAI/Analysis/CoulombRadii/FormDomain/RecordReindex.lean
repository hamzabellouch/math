import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.SortedObservable

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

def H1Vector.reindex {m n : ℕ} (u : H1Vector n) (e : Fin m ≃ Fin n) : H1Vector m := by
  have h : m=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  exact u.permutation e.symm

lemma H1Vector.reindex_value {m n : ℕ} (u : H1Vector n) (e : Fin m ≃ Fin n)
    (s : Spins m) (x : Configuration m) :
    (u.reindex e).value s x=u.value (s ∘ e.symm) (reindexConfiguration e x) := by
  have h : m=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  rfl

lemma mass_reindex {m n : ℕ} (u : H1Vector n) (e : Fin m ≃ Fin n) :
    mass (u.reindex e)=mass u := by
  have h : m=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  exact mass_permutation _ _

lemma form_reindex {J m n : ℕ} (S : Nuclei J) (u : H1Vector n) (e : Fin m ≃ Fin n) :
    form S (u.reindex e)=form S u := by
  have h : m=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  exact form_permutation _ _ _

def recordAssoc (m q k : ℕ) : Fin ((m+q)+k) ≃ Fin (m+(q+k)) :=
  finSumFinEquiv.symm.trans (((finSumFinEquiv.symm.sumCongr (Equiv.refl _)).trans
    (Equiv.sumAssoc (Fin m) (Fin q) (Fin k))).trans
      ((Equiv.refl _).sumCongr finSumFinEquiv |>.trans finSumFinEquiv))

lemma recordAssoc_left (m q k : ℕ) (i : Fin m) :
    recordAssoc m q k (Fin.castAdd k (Fin.castAdd q i))=Fin.castAdd (q+k) i := by
  simp only [recordAssoc,Equiv.trans_apply,←finSumFinEquiv_apply_left,Equiv.symm_apply_apply,
    Equiv.sumCongr_apply,Sum.map_inl,Equiv.sumAssoc_apply_inl_inl,Equiv.refl_apply]

lemma recordAssoc_middle (m q k : ℕ) (i : Fin q) :
    recordAssoc m q k (Fin.castAdd k (Fin.natAdd m i))=Fin.natAdd m (Fin.castAdd k i) := by
  simp only [recordAssoc,Equiv.trans_apply,←finSumFinEquiv_apply_left,←finSumFinEquiv_apply_right,
    Equiv.symm_apply_apply,Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,
    Equiv.sumAssoc_apply_inl_inr]

lemma recordAssoc_right (m q k : ℕ) (i : Fin k) :
    recordAssoc m q k (Fin.natAdd (m+q) i)=Fin.natAdd m (Fin.natAdd q i) := by
  simp only [recordAssoc,Equiv.trans_apply,←finSumFinEquiv_apply_right,
    Equiv.symm_apply_apply,Equiv.sumCongr_apply,Sum.map_inr,
    Equiv.sumAssoc_apply_inr,Equiv.refl_apply]

lemma append_recordAssoc {m q k : ℕ} (s : Spins m) (t : Spins q) (r : Spins k) :
    (Fin.append (Fin.append s t) r) ∘ (recordAssoc m q k).symm=Fin.append s (Fin.append t r) := by
  funext i
  obtain ⟨j,rfl⟩ := (recordAssoc m q k).surjective i
  simp only [Function.comp_apply,Equiv.symm_apply_apply]
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · simp only [recordAssoc_left,Fin.append_left]
    · simp only [recordAssoc_middle,Fin.append_left,Fin.append_right]
  · simp only [recordAssoc_right,Fin.append_right]

lemma reindex_join_recordAssoc {m q k : ℕ} (x : Configuration m) (y : Configuration q)
    (z : Configuration k) :
    reindexConfiguration (recordAssoc m q k) (joinConfiguration (m+q) k (joinConfiguration m q (x,y),z))=
      joinConfiguration m (q+k) (x,joinConfiguration q k (y,z)) := by
  ext ⟨i,b⟩
  obtain ⟨j,rfl⟩ := (recordAssoc m q k).surjective i
  change joinConfiguration (m+q) k (joinConfiguration m q (x,y),z)
    ((recordAssoc m q k).symm (recordAssoc m q k j),b)=_
  rw [Equiv.symm_apply_apply]
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) l
    · rw [recordAssoc_left,joinConfiguration_left,joinConfiguration_left,joinConfiguration_left]
    · rw [recordAssoc_middle,joinConfiguration_left,joinConfiguration_right,
        joinConfiguration_right,joinConfiguration_left]
  · rw [recordAssoc_right,joinConfiguration_right,joinConfiguration_right,joinConfiguration_right]

lemma reindexConfiguration_continuous {m n : ℕ} (e : Fin m ≃ Fin n) :
    Continuous (reindexConfiguration e) := by
  have h : m=n := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst n
  exact (permuteIsometry e.symm).continuous

end Coulomb
end

end
end

end OAI
