import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.CompileContactPrefixCongr
import OAI.Probability.CriticalPercolation.Entropy.BinaryMarks

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph SearchTree BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

def switched (n : ℕ) (h : History E n) (ω : Set E) (S : Finset ℕ) : Set E :=
  {e | ω e ∨ ∃ i ∈ S, nodeMark n h i = some e}

lemma switched_mono (n : ℕ) (h : History E n) (ω : Set E) (S : Finset ℕ) :
    ω ⊆ switched n h ω S := fun _ he => Or.inl he

lemma switched_insert (n : ℕ) (h : History E n) (ω : Set E) (S : Finset ℕ)
    (i : ℕ) (e : E) (hm : nodeMark n h i = some e) :
    switched n h ω (insert i S) = Function.update (switched n h ω S) e True := by
  apply Set.ext
  intro f
  change (ω f ∨ ∃ j ∈ insert i S, nodeMark n h j = some f) ↔
    (Function.update (switched n h ω S : E → Prop) e True) f
  by_cases hfe : f=e
  · subst f
    erw [Function.update_self]
    simp only [iff_true]
    exact Or.inr ⟨i,Finset.mem_insert_self _ _,hm⟩
  · erw [Function.update_of_ne hfe]
    constructor
    · rintro (ho|⟨j,hj,hjm⟩)
      · exact Or.inl ho
      · rcases Finset.mem_insert.mp hj with rfl|hj
        · exact (hfe (Option.some.inj (hjm.symm.trans hm))).elim
        · exact Or.inr ⟨j,hj,hjm⟩
    · rintro (ho|⟨j,hj,hjm⟩)
      · exact Or.inl ho
      · exact Or.inr ⟨j,Finset.mem_insert_of_mem hj,hjm⟩

def targets (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (i : ℕ) : Set V :=
  {v | ∃ j < i, (node d x n h j).1=v}

lemma canonical_misses_targets (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (i : ℕ) (hin : i < n+2) (hc : Canonical G (anchors d x n h) ω i) :
    ¬∃ b ∈ targets d x n h i, (G.openGraph ω).Reachable (node d x n h i).1 b := by
  rintro ⟨b,⟨j,hji,hjb⟩,hr⟩
  exact hc j _ _ hji (node_getElem? d x n h j (hji.trans hin))
    (node_getElem? d x n h i hin) (hjb ▸ hr.symm)

section Contact
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma earlier_not_incident (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i j : ℕ) (hin : i < n+2) (hji : j < i) (hj : 2 ≤ j)
    (hc : Canonical G (anchors d x n h) ω i) (e : E) (hm : nodeMark n h j = some e) :
    ¬∃ v ∈ G.ends e, (G.openGraph ω).Reachable (node d x n h i).1 v := by
  obtain ⟨_,u,v,hev,hu,hv⟩ := node_mark_geometry G order d x p w r₀ n h ω hr j hj
    (hji.trans hin) e hm
  rintro ⟨z,hz,hiz⟩
  rw [hev,Sym2.mem_iff] at hz
  have hp := nodeParent_lt G d x ω n h j hj
  rcases hz with rfl|rfl
  · exact hc j _ _ hji (node_getElem? d x n h j (hji.trans hin))
      (node_getElem? d x n h i hin) (hu.trans hiz.symm)
  · exact hc _ _ _ (hp.trans hji) (node_getElem? d x n h _ ((hp.trans hji).trans hin))
      (node_getElem? d x n h i hin) (hv.trans hiz.symm)

lemma switched_earlier_incidence (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hin : i < n+2) (hc : Canonical G (anchors d x n h) ω i)
    (S : Finset ℕ) (hS : ∀ j ∈ S, 2 ≤ j ∧ j < i) :
    ∀ e, (∃ v ∈ G.ends e, (G.openGraph ω).Reachable (node d x n h i).1 v) →
      (ω e ↔ switched n h ω S e) := by
  intro e he
  constructor
  · exact Or.inl
  · rintro (ho|⟨j,hj,hjm⟩)
    · exact ho
    · exact (earlier_not_incident G order d x p w r₀ n h ω hr i j hin (hS j hj).2
        (hS j hj).1 hc e hjm he).elim

theorem switched_contact_reconstruction (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2)
    (hc : Canonical G (anchors d x n h) ω i) (e : E) (hm : nodeMark n h i = some e)
    (S : Finset ℕ) (hS : ∀ j ∈ S, 2 ≤ j ∧ j < i) (offset : ℝ) :
    let B := targets d x n h i
    let a := (node d x n h i).1
    let F := fun σ : Set E => ∃ b ∈ B, (G.openGraph σ).Reachable a b
    let T := LazyDFS.search G order a B
    T.queryDelta F w (Function.update ω e True) e =
      T.queryDelta F w (switched n h ω (insert i S)) e ∧
    T.prefixScore p F w (Function.update ω e True) e =
      T.prefixScore p F w (switched n h ω (insert i S)) e ∧
    T.reverseGuess p F w (Function.update ω e True) offset e =
      T.reverseGuess p F w (switched n h ω (insert i S)) offset e := by
  dsimp only
  rw [switched_insert n h ω S i e hm]
  obtain ⟨hclosed,u,v,hev,hu,hv⟩ := node_mark_geometry G order d x p w r₀ n h ω hr i hi hin e hm
  have hb : (node d x n h (nodeParent G d x ω n h i)).1 ∈ targets d x n h i :=
    ⟨_,nodeParent_lt G d x ω n h i hi,rfl⟩
  have hup (σ : Set E) :
      @Function.update E (fun _ => Prop) (fun a b => Classical.propDecidable (a=b)) σ e True =
        Function.update σ e True := by
    exact congrArg (fun d' : DecidableEq E =>
      @Function.update E (fun _ => Prop) d' σ e True) (Subsingleton.elim _ _)
  simpa only [hup] using LazyDFS.search_contact_reconstruction G order ω (switched n h ω S) _ _ u v e
    hev hclosed (canonical_misses_targets G d x n h ω i hin hc) hu
    ⟨_,hb,hv.symm⟩ ⟨_,hb,hv.symm.mono (G.openGraph_mono (switched_mono n h ω S))⟩
    (switched_earlier_incidence G order d x p w r₀ n h ω hr i hin hc S hS) p w offset

end Contact
end CriticalPercolation.BinaryLaw
end
end

end OAI
