import OAI.NumberTheory.Jacobsthal.Partitions.ActualSafeBoxMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ActualWordSelection
open FinitePathGeometry PrimeHistories SourceStopPredicate
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinMaps
open ErdosCofactorChoices ErdosSubsetWord

attribute [local instance] Classical.propDecidable

noncomputable def wordSelection {n : ℕ} (lab : ℕ → Fin n) (ps : List ℕ) (b : Fin n) : Finset ℕ :=
  ps.toFinset.filter (fun p => lab p=b)

noncomputable def wordMultiplicity {n : ℕ} (lab : ℕ → Fin n) (ps : List ℕ) (b : Fin n) : ℕ :=
  (wordSelection lab ps b).card

theorem wordSelection_mem {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (ps : List ℕ) (hsource : ∀ p ∈ ps,p ∈ sourcePrimeSet w top) :
    wordSelection (label (zero_lt_one.trans hw) htop hxi) ps ∈ selections (globalBins w top xi)
      (wordMultiplicity (label (zero_lt_one.trans hw) htop hxi) ps) := by
  apply (mem_selections _ _ _).mpr
  intro b
  refine ⟨?_,rfl⟩
  intro p hp
  obtain ⟨hp,hb⟩ := Finset.mem_filter.mp hp
  have hh := source_list_boxed (zero_lt_one.trans hw) htop hxi ps hsource p (List.mem_toFinset.mp hp)
  simpa only [globalBins,hb] using hh

theorem wordSelection_recovers {n : ℕ} (lab : ℕ → Fin n) (ps : List ℕ)
    (hd : ps.Pairwise (· > ·)) : descendingWord (wordSelection lab ps)=ps := by
  apply (descendingWord_strict _).eq_of_mem_iff hd
  intro p
  simp only [mem_descendingWord,wordSelection,Finset.mem_filter,List.mem_toFinset]
  constructor
  · rintro ⟨b,hp,_hb⟩
    exact hp
  · intro hp
    exact ⟨lab p,hp,rfl⟩

theorem wordMultiplicity_count {n : ℕ} (lab : ℕ → Fin n) (ps : List ℕ)
    (hn : ps.Nodup) (b : Fin n) : wordMultiplicity lab ps b=(ps.map lab).count b := by
  have he : ps.toFinset.filter (fun p => lab p=b) = (ps.filter (fun p => lab p==b)).toFinset := by
    ext p
    simp
  rw [wordMultiplicity,wordSelection,he]
  rw [List.toFinset_card_of_nodup (hn.filter _)]
  rw [List.count,List.countP_map,List.countP_eq_length_filter]
  rfl
end NumberTheoryLean.ActualWordSelection


end Erdos970

end OAI
