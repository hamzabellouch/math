import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.MergeCross

namespace OAI

namespace MetricKMedianRecovery.PhaseCountCrossing
open PhaseSequence PhaseMergeRefinement PhaseMergeCompletion PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Success (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (q n k : ℕ) : Prop :=
  ∃ H : List X, Good loc F B Q v ((1+v^2)^q) lam eta H ∧
    Attains loc F B (Q ∪ H.toFinset) v lam (q+1) n k

def Common (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (q n k : ℕ) : Prop :=
  ∃ H : List X, Good loc F B Q v ((1+v^2)^q) lam eta H ∧
    ∃ a b : ℕ, Sandwich k a b ∧
      Attains loc F B (Q ∪ H.toFinset) v lam (q+1) n a ∧
      Attains loc F B (Q ∪ H.toFinset) v lam (q+1) n b

def Sensitive (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (q n k : ℕ) : Prop :=
  ∃ H G : List X, Good loc F B Q v ((1+v^2)^q) lam eta H ∧
    Good loc F B Q v ((1+v^2)^q) lam eta G ∧ LengthEdit loc F B H G ∧
    ∃ a b : ℕ, Sandwich k a b ∧
      Attains loc F B (Q ∪ H.toFinset) v lam (q+1) n a ∧
      Attains loc F B (Q ∪ G.toFinset) v lam (q+1) n b

def Outcome (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (q n k : ℕ) : Prop :=
  Success loc F B Q v lam eta q n k ∨ Common loc F B Q v lam eta q n k ∨
    Sensitive loc F B Q v lam eta q n k

theorem coincident_crossing (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q n k a b : ℕ) (H G : List X) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (hG : Good loc F B Q v ((1+v^2)^q) lam eta G)
    (hco : Coincident loc F Q H G) (hs : Sandwich k a b)
    (ha : Attains loc F B (Q ∪ H.toFinset) v lam (q+1) n a)
    (hb : Attains loc F B (Q ∪ G.toFinset) v lam (q+1) n b) :
    Success loc F B Q v lam eta q n k ∨ Common loc F B Q v lam eta q n k := by
  obtain ⟨i,f,R,hi,hfF,hiR,hfR,hHq,hGq,hd⟩ := hco
  have hfQ : f ∈ Q ∪ G.toFinset := hGq ▸ Finset.mem_insert_self f R
  have hf : f ∈ B := (Finset.mem_union.mp ((Finset.union_subset hQ hG.1.1.opened_subset) hfQ)).resolve_left hfF
  obtain ⟨c,hc,hac⟩ := attains_twin i f R hi hf hdis hiR hfR hHq hGq hd ht hlam ha
  by_cases hck : c = k
  · exact Or.inl ⟨G,hG,hck ▸ hc⟩
  · refine Or.inr ⟨G,hG,c,b,?_,hc,hb⟩
    rcases hs with ⟨hak,hkb⟩ | ⟨hbk,hka⟩
    · exact Or.inl ⟨by omega,hkb⟩
    · exact Or.inr ⟨hbk,by omega⟩

theorem edit_crossing (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q n k a b : ℕ) (H G : List X) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    (hH : Good loc F B Q v ((1+v^2)^q) lam eta H)
    (hG : Good loc F B Q v ((1+v^2)^q) lam eta G)
    (he : Edit loc F B Q H G) (hs : Sandwich k a b)
    (ha : Attains loc F B (Q ∪ H.toFinset) v lam (q+1) n a)
    (hb : Attains loc F B (Q ∪ G.toFinset) v lam (q+1) n b) :
    Outcome loc F B Q v lam eta q n k := by
  cases he with
  | freeAppend H i f hi hf hd =>
    exact Or.inr (Or.inr ⟨H,H++[f],hH,hG,LengthEdit.freeAppend H i f hi hf hd,a,b,hs,ha,hb⟩)
  | paidDelete C T i hi =>
    exact Or.inr (Or.inr ⟨C++i::T,C++T,hH,hG,LengthEdit.paidDelete C T i hi,a,b,hs,ha,hb⟩)
  | coincident hc =>
    rcases coincident_crossing loc F B Q v lam eta q n k a b H G hQ hdis ht hlam hG hc hs ha hb with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem chain_crossing (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q n k : ℕ) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (ht : 0 ≤ 1-3*v) (hlam : 0 < lam)
    {m : ℕ} {H G : List X} (hchain : Chain loc F B Q v ((1+v^2)^q) lam eta m H G)
    {a b : ℕ} (hs : Sandwich k a b)
    (ha : Attains loc F B (Q ∪ H.toFinset) v lam (q+1) n a)
    (hb : Attains loc F B (Q ∪ G.toFinset) v lam (q+1) n b) :
    Outcome loc F B Q v lam eta q n k := by
  induction hchain generalizing a b with
  | nil hH => exact Or.inr (Or.inl ⟨_,hH,a,b,hs,ha,hb⟩)
  | @cons m H J G hH he htchain ih =>
    have hJ := htchain.first_good
    obtain ⟨c,hc⟩ := attains_exists loc F B (Q ∪ J.toFinset) v lam (q+1) n
      (Finset.union_subset hQ hJ.1.1.opened_subset)
    by_cases hck : c = k
    · exact Or.inl ⟨J,hJ,hck ▸ hc⟩
    · have hcases : Sandwich k a c ∨ Sandwich k c b := by
        rcases hs with hs | hs <;> unfold Sandwich <;> omega
      rcases hcases with hac | hcb
      · rcases he with he | he
        · exact edit_crossing loc F B Q v lam eta q n k a c H J hQ hdis ht hlam hH hJ he hac ha hc
        · exact edit_crossing loc F B Q v lam eta q n k c a J H hQ hdis ht hlam hJ hH he hac.symm hc ha
      · exact ih hcb hc hb

end MetricKMedianRecovery.PhaseCountCrossing
namespace MetricKMedianRecovery.PhaseMergeCompletion
open PhaseHistoryTransfer PhaseMergeSurgery
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma Attains.mono_free {loc : D → X} {F B B' Q : Finset X} {v lam : ℝ} {q n c : ℕ}
    (h : Attains loc F B Q v lam q n c) (hB : B ⊆ B') : Attains loc F B' Q v lam q n c := by
  obtain ⟨T,hT,hh,hr,hc⟩ := h
  refine ⟨T,hT,?_,hr,hc⟩
  clear hT hr hc
  induction hh with
  | nil => exact History.nil _ _
  | cons hhead htail ih => exact History.cons ⟨prefix_free_mono hhead.1 hB,hhead.2⟩ ih

end MetricKMedianRecovery.PhaseMergeCompletion

end OAI
