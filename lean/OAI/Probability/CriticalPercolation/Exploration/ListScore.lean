import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.Score
import OAI.Probability.CriticalPercolation.GraphGeometry.EraseBond

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E]

noncomputable def listScore (p : ℝ) (F : Set E → Prop) (ω : Set E) :
    List E → (E → Prop → ℝ) → ℝ
  | [], _ => 0
  | e::es, w => (if openPivot F e ω then (1-p)*delta w F e else 0) +
      listScore p F ω es (pin w e (ω e))

lemma score_eq_listScore (T : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) :
    T.score p F w ω = listScore p F ω (T.reads (fun e => decide (ω e))) w := by
  induction T generalizing w with
  | done r => rfl
  | ask e l r hl hr =>
    by_cases he : ω e
    · simp only [score,he,↓reduceIte,reads,decide_true,listScore,hr]
    · simp only [score,he,↓reduceIte,reads,decide_false,Bool.false_eq_true,listScore,hl]

lemma score_eq_of_reads_eq (T T' : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E)
    (h : T.reads (fun e => decide (ω e)) = T'.reads (fun e => decide (ω e))) :
    T.score p F w ω = T'.score p F w ω := by
  rw [score_eq_listScore,score_eq_listScore,h]

end CriticalPercolation.SearchTree

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem young_phase_score_bound (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (f : E) (a s t : V) (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (fuel : ℕ) (st : State V E)
    (hf : f ∈ st.read) (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (fresh : Fresh w p st.read) :
    let H := G.eraseBond f a
    let T := compile G order B fuel st (push G order s)
    expect w (fun ω => if H.joinedPair a s t ω then T.score p (H.wiredEvent a s t) w ω else 0) ≤
      prob w (H.joinedPair a s t) := by
  dsimp only
  apply le_trans (SearchTree.phase_score_bound (G.eraseBond f a) a s t has hat hst hp
    _ w hw hn ?_) (potential_le w hn _ _)
  apply compile_phaseAdmissible_in G (G.eraseBond f a) order B s hp fuel st _ w fresh
  · intro d hd ω _
    have hds : d.1 = s := (of_decide_eq_true (List.mem_filter.mp hd).2).1
    rw [hds]
  · intro e he
    apply (G.eraseBond_ends_ne f a _).symm
    exact fun hef => he (hef ▸ hf)

end CriticalPercolation.LazyDFS

end
end

end OAI
