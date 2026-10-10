import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.FiniteKernels
import OAI.Combinatorics.RamseyFive.Streams.SelectedExtraction

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped Classical BigOperators
open FiniteEntropy
noncomputable section
variable {α β γ Ω κ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype Ω] [Fintype κ]

def sourceSequence {n : ℕ} (reverse : Bool) (view : β→α) (x : Fin n→β) : Fin n→α :=
  fun i=>view (x (if reverse then i.rev else i))

def reverseEmbedding {n l : ℕ} (e : Fin l↪o Fin n) : Fin l↪o Fin n where
  toFun i:=(e i.rev).rev
  inj' := Fin.rev_injective.comp (e.injective.comp Fin.rev_injective)
  map_rel_iff' := by
    intro i j
    change (e i.rev).rev≤(e j.rev).rev ↔ i≤j
    rw [Fin.rev_le_rev,e.le_iff_le,Fin.rev_le_rev]

lemma sourceSequence_occurs {n l : ℕ} (reverse : Bool) (view : β→α)
    (x : Fin n→β) (y : Fin l→β) (h : x∈occurrences y) :
    sourceSequence reverse view x∈occurrences (sourceSequence reverse view y) := by
  obtain ⟨e,he⟩:=(mem_occurrences_iff x y).mp h
  apply (mem_occurrences_iff _ _).mpr
  cases reverse
  · exact ⟨e,fun i=>congrArg view (he i)⟩
  · refine ⟨reverseEmbedding e,fun i=>?_⟩
    change view (x ((e i.rev).rev).rev)=view (y i.rev)
    rw [Fin.rev_rev,he]

structure SelectedStream (N n : ℕ) (admissible : (Fin N→α)→Prop) where
  law : Law Ω
  stream : Ω→Fin N→α
  tuple : Ω→Fin n→β
  reverse : Bool
  view : β→α
  selected : ∀ a,0<law a→stream a∈occurrences (sourceSequence reverse view (tuple a))
  good : ∀ a,0<law a→admissible (stream a)
  density : ℝ
  density_nonneg : 0≤density
  density_bound : ∀ s,map law stream s≤density/(Fintype.card α:ℝ)^N

namespace SelectedStream
variable {N n : ℕ} {admissible : (Fin N→α)→Prop}

def augment (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) (q : Ω→Law κ) :
    SelectedStream (Ω:=Ω×κ) (β:=β) N n admissible where
  law := adaptiveLaw S.law q
  stream := fun z=>S.stream z.1
  tuple := fun z=>S.tuple z.1
  reverse := S.reverse
  view := S.view
  selected := by
    intro z hz
    have hp : 0<S.law z.1 := by
      change 0<S.law z.1*q z.1 z.2 at hz
      exact (mul_pos_iff.mp hz).resolve_right (fun h=>(S.law.nonneg _).not_gt h.1) |>.1
    exact S.selected _ hp
  good := by
    intro z hz
    have hp : 0<S.law z.1 := by
      change 0<S.law z.1*q z.1 z.2 at hz
      exact (mul_pos_iff.mp hz).resolve_right (fun h=>(S.law.nonneg _).not_gt h.1) |>.1
    exact S.good _ hp
  density := S.density
  density_nonneg := S.density_nonneg
  density_bound := by intro s; rw [adaptive_stream]; exact S.density_bound s

def restrict (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (E : Finset Ω) (hE : 0<eventMass S.law E) :
    SelectedStream (Ω:=Ω) (β:=β) N n admissible where
  law := conditionOn S.law E hE
  stream := S.stream
  tuple := S.tuple
  reverse := S.reverse
  view := S.view
  selected := fun a ha=>S.selected a (conditionOn_positive S.law E hE a ha).2
  good := fun a ha=>S.good a (conditionOn_positive S.law E hE a ha).2
  density := S.density/eventMass S.law E
  density_nonneg := div_nonneg S.density_nonneg hE.le
  density_bound := by
    intro s
    apply (map_conditionOn_le S.law E hE S.stream s).trans
    have hh:=div_le_div_of_nonneg_right (S.density_bound s) hE.le
    convert hh using 1; ring

def extract {l : ℕ} (hl : l≤n) (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (positions : Ω→Finset (Fin n)) : SelectedStream (Ω:=Ω) (β:=β) N l admissible where
  law := S.law
  stream := S.stream
  tuple := fun a=>retainedTuple hl (S.tuple a) (positions a)
  reverse := S.reverse
  view := S.view
  selected := by
    intro a ha
    exact occurrences_trans _ _ _ (S.selected a ha)
      (sourceSequence_occurs S.reverse S.view _ _ (retainedTuple_occurs hl _ _))
  good := S.good
  density := S.density
  density_nonneg := S.density_nonneg
  density_bound := S.density_bound

def changeOrientation (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (swap : β→γ) (back : γ→β) (hinv : Function.LeftInverse back swap) :
    SelectedStream (Ω:=Ω) (β:=γ) N n admissible where
  law := S.law
  stream := S.stream
  tuple := fun a i=>swap (S.tuple a i.rev)
  reverse := !S.reverse
  view := S.view ∘ back
  selected := by
    intro a ha
    have hh : sourceSequence (!S.reverse) (S.view ∘ back)
      (fun i=>swap (S.tuple a i.rev))=sourceSequence S.reverse S.view (S.tuple a) := by
      funext i
      cases h:S.reverse <;> simp only [sourceSequence,Bool.not_false,Bool.not_true,
        Bool.false_eq_true,ite_false,ite_true,Fin.rev_rev,Function.comp_apply] <;>
        exact congrArg S.view (hinv _)
    rw [hh]
    exact S.selected a ha
  good := S.good
  density := S.density
  density_nonneg := S.density_nonneg
  density_bound := S.density_bound

theorem entropy_lower [Nonempty α] (hn : n≤N)
    (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) :
    -Real.log (2*S.density*(N.choose n:ℝ)/(Fintype.card α:ℝ)^n)≤
      entropy (map S.law S.tuple) := by
  have hh:=selected_entropy hn (pair S.law S.stream
    (fun a=>sourceSequence S.reverse S.view (S.tuple a))) S.density S.density_nonneg
    (by simpa only [first_pair] using S.density_bound) id (by
      intro s f hp
      obtain ⟨a,ha,he⟩:=map_positive S.law
        (fun a=>(S.stream a,sourceSequence S.reverse S.view (S.tuple a))) (s,f) hp
      cases he
      exact Or.inl (S.selected a ha))
  simp only [second_pair] at hh
  have he:=entropy_map_le (map S.law S.tuple) (sourceSequence S.reverse S.view)
  rw [map_comp] at he
  exact hh.trans he

end SelectedStream
end
end SharpRamseyFive.SelectedTuple

end OAI
