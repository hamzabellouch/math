import OAI.NumberTheory.Jacobsthal.Paths.ActualWordSelection

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.SortedLabelRepetition
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition
open ErdosSubsetWord


theorem repeated_label_has_adjacent {α : Type*} {n : ℕ} (f : α → Fin n) (b : Fin n)
    (ps : List α) (hord : (ps.map f).Pairwise (· ≥ ·)) (hcount : 2 ≤ (ps.map f).count b) :
    ∃ pre p q tail,ps=pre++p::q::tail ∧ f p=b ∧ f q=b := by
  induction ps with
  | nil => simp at hcount
  | cons p ps ih =>
    simp only [List.map_cons] at hord hcount
    have htail := (List.pairwise_cons.mp hord).2
    by_cases hp : f p=b
    · have hc : 0 < (ps.map f).count b := by simpa [hp] using hcount
      have hb := List.count_pos_iff.mp hc
      cases ps with
      | nil => simp at hb
      | cons q tail =>
        have hqle : f q ≤ b := by
          have hh := (List.pairwise_cons.mp hord).1 (f q) (by simp)
          simpa only [hp] using hh
        obtain ⟨u,hu,hub⟩ := List.mem_map.mp hb
        have hqge : b ≤ f q := by
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hub.symm.le
          · have hh := (List.pairwise_cons.mp htail).1 (f u) (List.mem_map.mpr ⟨u,hu,rfl⟩)
            rwa [hub] at hh
        exact ⟨[],p,q,tail,rfl,hp,le_antisymm hqle hqge⟩
    · have hc : 2 ≤ (ps.map f).count b := by simpa [hp,Ne.symm hp] using hcount
      obtain ⟨pre,q,r,tail,he,hq,hr⟩ := ih htail hc
      exact ⟨p::pre,q,r,tail,by simp only [List.cons_append,he],hq,hr⟩

theorem source_word_labels_ordered {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (ps : List ℕ) (hd : ps.Pairwise (· > ·)) (hsrc : ∀ p ∈ ps,p ∈ sourcePrimeSet w top) :
    (ps.map (label (zero_lt_one.trans hw) htop hxi)).Pairwise (· ≥ ·) := by
  rw [List.pairwise_map]
  apply hd.imp_of_mem
  intro p q hp hq hpq
  exact global_label_mono hw htop hxi (hsrc p hp) (hsrc q hq) hpq.le

theorem source_repeated_label_adjacent {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (ps : List ℕ) (hd : ps.Pairwise (· > ·)) (hsrc : ∀ p ∈ ps,p ∈ sourcePrimeSet w top)
    (b : Fin (binCount w top xi)) (hcount : 2 ≤ (ps.map (label (zero_lt_one.trans hw) htop hxi)).count b) :
    ∃ pre p q tail,ps=pre++p::q::tail ∧
      label (zero_lt_one.trans hw) htop hxi p=b ∧ label (zero_lt_one.trans hw) htop hxi q=b :=
  repeated_label_has_adjacent _ b ps (source_word_labels_ordered hw htop hxi ps hd hsrc) hcount
end NumberTheoryLean.SortedLabelRepetition


end Erdos970

end OAI
