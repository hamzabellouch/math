import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinarySupport
import OAI.Probability.CriticalPercolation.Exploration.AncestryForest

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

noncomputable def nodeParent (d : ℕ) (x : ℕ → V) (ω : Set E) :
    (n : ℕ) → History E n → ℕ → ℕ
  | 0, _, i => if i=1 then 1 else 0
  | n+1, h, i => if i=n+2 then
      let j := parent G (anchors d x n h.1) (x (nextIndex d n h.1)) ω h.2.2
      if j<n+2 then j else 0
    else nodeParent d x ω n h.1 i

lemma nodeParent_lt (d : ℕ) (x : ℕ → V) (ω : Set E) (n : ℕ) (h : History E n)
    (i : ℕ) (hi : 2 ≤ i) : nodeParent G d x ω n h i < i := by
  induction n with
  | zero => simp only [nodeParent,ite_eq_right (by omega : i≠1)]; omega
  | succ n ih =>
    by_cases he : i = n+2
    · subst i
      simp only [nodeParent,ite_true]
      split_ifs with hp
      · exact hp
      · omega
    · rw [nodeParent,ite_eq_right he]
      exact ih h.1

noncomputable def historyForest (d : ℕ) (x : ℕ → V) (ω : Set E)
    (n : ℕ) (h : History E n) : Forest :=
  ⟨nodeParent G d x ω n h, nodeParent_lt G d x ω n h⟩

lemma nodeParent_old (d : ℕ) (x : ℕ → V) (ω : Set E) (n : ℕ) (h : History E (n+1))
    (i : ℕ) (hi : i < n+2) : nodeParent G d x ω (n+1) h i = nodeParent G d x ω n h.1 i := by
  rw [nodeParent,ite_eq_right (by omega : i≠n+2)]

def node (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (i : ℕ) : V × Bool :=
  (anchors d x n h)[i]?.getD (x 0,true)

lemma node_old (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E (n+1))
    (i : ℕ) (hi : i < n+2) : node d x (n+1) h i = node d x n h.1 i := by
  change ((anchors d x n h.1 ++ [_])[i]?).getD _ = _
  rw [List.getElem?_append_left (by simpa only [anchors_length] using hi)]
  rfl

lemma node_current (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E (n+1)) :
    node d x (n+1) h (n+2) = (x (nextIndex d n h.1),h.2.1) := by
  unfold node anchors
  rw [List.getElem?_append_right (by simp [anchors_length])]
  simp only [anchors_length,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]

lemma node_getElem? (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (i : ℕ) (hi : i < n+2) :
    (anchors d x n h)[i]? = some (node d x n h i) := by
  have hil : i<(anchors d x n h).length := by simpa only [anchors_length] using hi
  simp only [node,List.getElem?_eq_getElem hil,Option.getD_some]

lemma node_mem (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (i : ℕ) (hi : i < n+2) :
    node d x n h i ∈ anchors d x n h := List.mem_of_getElem? (node_getElem? d x n h i hi)

lemma node_bases (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) :
    node d x n h 0 = (x 0,true) ∧ node d x n h 1 = (x d,false) := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    rw [node_old d x n h 0 (by omega),node_old d x n h 1 (by omega)]
    exact ih h.1

section Support
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma nodeParent_current (n : ℕ) (h : History E (n+1)) (ω : E → Prop)
    (hr : density G order d x p w r₀ (n+1) h ω ≠ 0) :
    nodeParent G d x ω (n+1) h (n+2) =
      parent G (anchors d x n h.1) (x (nextIndex d n h.1)) ω h.2.2 := by
  have hk := (density_step_support G order d x p w r₀ n h ω hr).2.1
  have hp := parent_lt_of_exists G _ _ ω _
    (kernel_parent_exists G order d x n h.1 _ p w ω _ hk)
  rw [anchors_length] at hp
  simp only [nodeParent,ite_true,ite_eq_left hp]

lemma node_colour_parent (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0) (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2) :
    (node d x n h i).2 = (node d x n h (nodeParent G d x ω n h i)).2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨hprev,hk,hs⟩ := density_step_support G order d x p w r₀ n h ω hr
    by_cases he : i=n+2
    · subst i
      rw [node_current,nodeParent_current G order d x p w r₀ n h ω hr]
      have hp := parent_lt_of_exists G _ _ ω _
        (kernel_parent_exists G order d x n h.1 _ p w ω _ hk)
      rw [anchors_length] at hp
      rw [node_old d x n h _ hp]
      rw [← hs]
      simp only [side,node_getElem? d x n h.1 _ hp,Option.getD_some]
    · have hio : i < n+2 := by omega
      rw [node_old d x n h i hio,nodeParent_old G d x ω n h i hio,
        node_old d x n h _ ((nodeParent_lt G d x ω n h.1 i hi).trans hio)]
      exact ih h.1 hprev hio

lemma node_root_colour (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0) (i : ℕ) (hin : i < n+2) :
    (node d x n h i).2 = if (historyForest G d x ω n h).root i = 0 then true else false := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hi : i < 2
    · rw [Forest.root_base _ hi]
      have hb := node_bases d x n h
      interval_cases i <;> simp only [hb.1,hb.2,ite_true,one_ne_zero,ite_false]
    · have hi2 : 2 ≤ i := by omega
      rw [Forest.root_step _ hi2]
      rw [node_colour_parent G order d x p w r₀ n h ω hr i hi2 hin]
      exact ih _ (nodeParent_lt G d x ω n h i hi2)
        ((nodeParent_lt G d x ω n h i hi2).trans hin)

end Support

def Canonical (L : List (V × Bool)) (ω : Set E) (i : ℕ) : Prop :=
  ∀ j z t, j < i → L[j]? = some z → L[i]? = some t →
    ¬(G.openGraph ω).Reachable z.1 t.1

lemma parent_canonical (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E)
    (hex : ∃ i, parentPredicate G L a ω m i) : Canonical G L ω (parent G L a ω m) := by
  intro j z t hj hz ht hr
  have hs := firstIndex_spec hex
  obtain ⟨v,hv,hpred⟩ := hs
  have hvt : v=t := Option.some.inj (hv.symm.trans ht)
  subst v
  have hP : parentPredicate G L a ω m j := by
    refine ⟨z,hz,?_⟩
    cases m with
    | none => exact hpred.trans hr.symm
    | some e =>
      obtain ⟨u,hu,htu⟩ := hpred
      exact ⟨u,hu,hr.trans htu⟩
  have hle := firstIndex_le hP
  exact (Nat.not_le_of_gt hj) hle

lemma canonical_append (L M : List (V × Bool)) (ω : Set E) (i : ℕ) (hi : i < L.length)
    (hC : Canonical G L ω i) : Canonical G (L++M) ω i := by
  intro j z t hj hz ht
  rw [List.getElem?_append_left (hj.trans hi)] at hz
  rw [List.getElem?_append_left hi] at ht
  exact hC j z t hj hz ht

lemma canonical_distinct (L : List (V × Bool)) (ω : Set E) (i j : ℕ)
    (hi : Canonical G L ω i) (hj : Canonical G L ω j)
    (z t : V × Bool) (hz : L[i]? = some z) (ht : L[j]? = some t)
    (hr : (G.openGraph ω).Reachable z.1 t.1) : i=j := by
  rcases lt_trichotomy i j with hij|hij|hij
  · exact (hj i z t hij hz ht hr).elim
  · exact hij
  · exact (hi j t z hij ht hz hr.symm).elim

section CanonicalSupport
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma nodeParent_canonical (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2) :
    Canonical G (anchors d x n h) ω (nodeParent G d x ω n h i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨hprev,hk,hs⟩ := density_step_support G order d x p w r₀ n h ω hr
    by_cases he : i = n+2
    · subst i
      rw [nodeParent_current G order d x p w r₀ n h ω hr]
      have hex := kernel_parent_exists G order d x n h.1 _ p w ω _ hk
      apply canonical_append
      · exact parent_lt_of_exists G _ _ ω _ hex
      · exact parent_canonical G _ _ ω _ hex
    · have hio : i < n+2 := by omega
      rw [nodeParent_old G d x ω n h i hio]
      apply canonical_append
      · rw [anchors_length]
        exact (nodeParent_lt G d x ω n h.1 i hi).trans hio
      · exact ih h.1 hprev hio

lemma lineage_canonical (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (j : ℕ) (hjn : j < n+2) (hj : Canonical G (anchors d x n h) ω j)
    (i : ℕ) (hi : i ∈ (historyForest G d x ω n h).lineage j) :
    Canonical G (anchors d x n h) ω i := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj2 : j < 2
    · have he : i=j := by simpa only [Forest.lineage_base _ hj2,List.mem_singleton] using hi
      exact he ▸ hj
    · have hj2' : 2 ≤ j := by omega
      rw [Forest.lineage_step _ hj2',List.mem_cons] at hi
      rcases hi with rfl|hi
      · exact hj
      · exact ih _ (nodeParent_lt G d x ω n h j hj2')
          ((nodeParent_lt G d x ω n h j hj2').trans hjn)
          (nodeParent_canonical G order d x p w r₀ n h ω hr j hj2' hjn) hi

end CanonicalSupport

noncomputable def owner (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) : ℕ := parent G (anchors d x n h) a ω none

lemma owner_exists (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    ∃ i, parentPredicate G (anchors d x n h) a ω none i := by
  obtain ⟨b,hb⟩ := ha
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hb
  exact ⟨i,(a,b),hi,.refl _⟩

lemma owner_lt (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    owner G d x n h ω a < n+2 := by
  have hp := parent_lt_of_exists G _ _ ω none (owner_exists G d x n h ω a ha)
  simpa only [anchors_length,owner] using hp

lemma owner_canonical (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    Canonical G (anchors d x n h) ω (owner G d x n h ω a) :=
  parent_canonical G _ _ ω none (owner_exists G d x n h ω a ha)

lemma owner_reachable (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    (G.openGraph ω).Reachable a (node d x n h (owner G d x n h ω a)).1 := by
  obtain ⟨z,hz,hr⟩ := firstIndex_spec (owner_exists G d x n h ω a ha)
  have he : z = node d x n h (owner G d x n h ω a) := Option.some.inj
    (hz.symm.trans (node_getElem? d x n h _ (owner_lt G d x n h ω a ha)))
  exact he ▸ hr

lemma owner_colour (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (b : Bool) (ha : (a,b) ∈ anchors d x n h)
    (hL : Consistent G (anchors d x n h) ω) :
    (node d x n h (owner G d x n h ω a)).2 = b :=
  (hL (a,b) ha _ (node_mem d x n h _ (owner_lt G d x n h ω a ⟨b,ha⟩))
    (owner_reachable G d x n h ω a ⟨b,ha⟩)).symm

section Owners
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

lemma terminal_roots (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
    (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0) :
    (historyForest G d x ω n h).root (owner G d x n h ω (x (interval d n h).1)) = 0 ∧
    (historyForest G d x ω n h).root (owner G d x n h ω (x (interval d n h).2)) = 1 := by
  have hL := density_consistent G order d x p w s n h ω hr
  have he := endpoint_labels d x n h
  have hl := owner_colour G d x n h ω _ true he.1 hL
  have hr' := owner_colour G d x n h ω _ false he.2 hL
  rw [node_root_colour G order d x p w _ n h ω hr _
    (owner_lt G d x n h ω _ ⟨true,he.1⟩)] at hl
  rw [node_root_colour G order d x p w _ n h ω hr _
    (owner_lt G d x n h ω _ ⟨false,he.2⟩)] at hr'
  constructor
  · by_contra hz
    simp only [ite_eq_right hz] at hl
    cases hl
  · have hn := (historyForest G d x ω n h).root_lt_two
      (owner G d x n h ω (x (interval d n h).2))
    have hz : (historyForest G d x ω n h).root
        (owner G d x n h ω (x (interval d n h).2)) ≠ 0 := by
      intro hz
      simp only [ite_eq_left hz] at hr'
      cases hr'
    omega

end Owners

end CriticalPercolation.BinaryLaw
end
end

end OAI
