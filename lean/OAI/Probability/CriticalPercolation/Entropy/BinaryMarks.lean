import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.QueryGeometry
import OAI.Probability.CriticalPercolation.Entropy.BinaryForest

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

def nodeMark : (n : ℕ) → History E n → ℕ → Option E
  | 0, _, _ => none
  | n+1, h, i => if i = n+2 then h.2.2 else nodeMark n h.1 i

lemma nodeMark_old (n : ℕ) (h : History E (n+1)) (i : ℕ) (hi : i < n+2) :
    nodeMark (n+1) h i = nodeMark n h.1 i := by
  rw [nodeMark,ite_eq_right (by omega : i ≠ n+2)]

lemma nodeMark_current (n : ℕ) (h : History E (n+1)) : nodeMark (n+1) h (n+2) = h.2.2 := by
  simp only [nodeMark,ite_true]

lemma canonical_append_iff (L M : List (V × Bool)) (ω : Set E) (i : ℕ) (hi : i < L.length) :
    Canonical G (L++M) ω i ↔ Canonical G L ω i := by
  constructor
  · intro hc j z t hj hz ht
    apply hc j z t hj
    · rw [List.getElem?_append_left (hj.trans hi)]
      exact hz
    · rw [List.getElem?_append_left hi]
      exact ht
  · exact canonical_append G L M ω i hi

section Marks
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma current_mark_geometry (n : ℕ) (h : History E (n+1)) (ω : E → Prop) (e : E)
    (hr : density G order d x p w r₀ (n+1) h ω ≠ 0) (hm : h.2.2 = some e) :
    ¬ω e ∧ ∃ u v, G.ends e = s(u,v) ∧
      (G.openGraph ω).Reachable (node d x (n+1) h (n+2)).1 u ∧
      (G.openGraph ω).Reachable (node d x (n+1) h
        (nodeParent G d x ω (n+1) h (n+2))).1 v := by
  have hk := (density_step_support G order d x p w r₀ n h ω hr).2.1
  rw [hm] at hk
  obtain ⟨ha,hclosed,u,v,hev,hau,hv⟩ := kernel_contact_geometry G order _ _ p w ω e hk
  have hex := kernel_parent_exists G order d x n h.1 _ p w ω (some e) hk
  have hp := parent_lt_of_exists G _ _ ω _ hex
  rw [anchors_length] at hp
  rw [node_current,nodeParent_current G order d x p w r₀ n h ω hr,hm,
    node_old d x n h _ hp]
  obtain ⟨z,hz,hpred⟩ := firstIndex_spec hex
  have hnode : z = node d x n h.1 (parent G (anchors d x n h.1)
      (x (nextIndex d n h.1)) ω (some e)) :=
    Option.some.inj (hz.symm.trans (node_getElem? d x n h.1 _ hp))
  rw [hnode] at hpred
  obtain ⟨t,ht,hpt⟩ := hpred
  have htv : t=v := by
    rw [hev,Sym2.mem_iff] at ht
    rcases ht with rfl|rfl
    · have hmemp := node_mem d x n h.1 _ hp
      exact (ha ⟨_,⟨_,hmemp⟩,hpt.trans hau.symm⟩).elim
    · rfl
  exact ⟨hclosed,u,v,hev,hau,htv ▸ hpt⟩

lemma current_canonical_iff (n : ℕ) (h : History E (n+1)) (ω : E → Prop)
    (hr : density G order d x p w r₀ (n+1) h ω ≠ 0) :
    Canonical G (anchors d x (n+1) h) ω (n+2) ↔ h.2.2 ≠ none := by
  have hk := (density_step_support G order d x p w r₀ n h ω hr).2.1
  have hex := kernel_parent_exists G order d x n h.1 _ p w ω _ hk
  have hp := parent_lt_of_exists G _ _ ω _ hex
  rw [anchors_length] at hp
  constructor
  · intro hc hm
    obtain ⟨z,hz,hpred⟩ := firstIndex_spec hex
    have ht := node_getElem? d x (n+1) h (n+2) (by omega)
    rw [node_current] at ht
    have hpz : (anchors d x (n+1) h)[parent G (anchors d x n h.1)
        (x (nextIndex d n h.1)) ω h.2.2]? = some z := by
      change ((anchors d x n h.1 ++ [_])[_]?) = some z
      rw [List.getElem?_append_left (by simpa only [anchors_length] using hp)]
      exact hz
    rw [hm] at hpred
    exact hc _ z _ hp hpz ht hpred.symm
  · intro hm
    obtain ⟨e,he⟩ := Option.ne_none_iff_exists'.mp hm
    have hk' := hk
    rw [he] at hk'
    have ha := (kernel_contact_geometry G order _ _ p w ω e hk').1
    intro j z t hj hz ht hrzt
    have ht' := node_getElem? d x (n+1) h (n+2) (by omega)
    rw [node_current] at ht'
    have heqt : t = (x (nextIndex d n h.1),h.2.1) := Option.some.inj (ht.symm.trans ht')
    subst t
    change (anchors d x n h.1 ++ [_])[j]? = some z at hz
    rw [List.getElem?_append_left (by simpa only [anchors_length] using hj)] at hz
    exact ha ⟨z.1,⟨z.2,List.mem_of_getElem? hz⟩,hrzt⟩

lemma canonical_iff_nonhold (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2) :
    Canonical G (anchors d x n h) ω i ↔ nodeMark n h i ≠ none := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n+2
    · subst i
      rw [nodeMark_current]
      exact current_canonical_iff G order d x p w r₀ n h ω hr
    · have hio : i < n+2 := by omega
      rw [nodeMark_old n h i hio]
      change Canonical G (anchors d x n h.1 ++ [_]) ω i ↔ _
      rw [canonical_append_iff G _ _ ω i (by simpa only [anchors_length] using hio)]
      exact ih h.1 (density_step_support G order d x p w r₀ n h ω hr).1 hio

lemma node_mark_geometry (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2) (e : E) (hm : nodeMark n h i = some e) :
    ¬ω e ∧ ∃ u v, G.ends e = s(u,v) ∧
      (G.openGraph ω).Reachable (node d x n h i).1 u ∧
      (G.openGraph ω).Reachable (node d x n h (nodeParent G d x ω n h i)).1 v := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n+2
    · subst i
      rw [nodeMark_current] at hm
      exact current_mark_geometry G order d x p w r₀ n h ω e hr hm
    · have hio : i < n+2 := by omega
      rw [nodeMark_old n h i hio] at hm
      rw [node_old d x n h i hio,nodeParent_old G d x ω n h i hio,
        node_old d x n h _ ((nodeParent_lt G d x ω n h.1 i hi).trans hio)]
      exact ih h.1 (density_step_support G order d x p w r₀ n h ω hr).1 hio hm

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma canonical_node_reachable_eq (n : ℕ) (h : History E n) (ω : Set E)
    (i j : ℕ) (hin : i < n+2) (hjn : j < n+2)
    (hi : Canonical G (anchors d x n h) ω i) (hj : Canonical G (anchors d x n h) ω j)
    (hr : (G.openGraph ω).Reachable (node d x n h i).1 (node d x n h j).1) : i=j :=
  canonical_distinct G _ ω i j hi hj _ _ (node_getElem? d x n h i hin)
    (node_getElem? d x n h j hjn) hr

lemma selected_marks_injective (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i j : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j) (hin : i < n+2) (hjn : j < n+2)
    (e : E) (he : nodeMark n h i = some e) (he' : nodeMark n h j = some e) : i=j := by
  have hic := (canonical_iff_nonhold G order d x p w r₀ n h ω hr i hi hin).mpr
    (by rw [he]; exact Option.some_ne_none e)
  have hjc := (canonical_iff_nonhold G order d x p w r₀ n h ω hr j hj hjn).mpr
    (by rw [he']; exact Option.some_ne_none e)
  have hip := nodeParent_canonical G order d x p w r₀ n h ω hr i hi hin
  have hjp := nodeParent_canonical G order d x p w r₀ n h ω hr j hj hjn
  have hiplt := nodeParent_lt G d x ω n h i hi
  have hjplt := nodeParent_lt G d x ω n h j hj
  obtain ⟨_,u,v,hev,hu,hv⟩ := node_mark_geometry G order d x p w r₀ n h ω hr i hi hin e he
  obtain ⟨_,u',v',hev',hu',hv'⟩ := node_mark_geometry G order d x p w r₀ n h ω hr j hj hjn e he'
  rcases Sym2.eq_iff.mp (hev.symm.trans hev') with ⟨huu,hvv⟩|⟨huv,hvu⟩
  · apply canonical_node_reachable_eq G d x n h ω i j hin hjn hic hjc
    exact hu.trans (huu ▸ hu'.symm)
  · have h1 : i = nodeParent G d x ω n h j :=
      canonical_node_reachable_eq G d x n h ω i _ hin (hjplt.trans hjn) hic hjp
        (hu.trans (huv ▸ hv'.symm))
    have h2 : j = nodeParent G d x ω n h i :=
      canonical_node_reachable_eq G d x n h ω j _ hjn (hiplt.trans hin) hjc hip
        (hu'.trans (hvu.symm ▸ hv.symm))
    omega

end Marks

noncomputable def activeNodes (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) : Finset ℕ :=
  (historyForest G d x ω n h).active (owner G d x n h ω (x (interval d n h).1))
    (owner G d x n h ω (x (interval d n h).2))

lemma active_lt (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (ω : Set E)
    (i : ℕ) (hi : i ∈ activeNodes G d x n h ω) : i < n+2 := by
  have he := endpoint_labels d x n h
  have hi' := (Forest.mem_active (historyForest G d x ω n h)).mp hi
  rcases hi'.1 with hi|hi
  · exact ((historyForest G d x ω n h).mem_lineage_le hi).trans_lt
      (owner_lt G d x n h ω _ ⟨true,he.1⟩)
  · exact ((historyForest G d x ω n h).mem_lineage_le hi).trans_lt
      (owner_lt G d x n h ω _ ⟨false,he.2⟩)

section Active
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma active_canonical (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : i ∈ activeNodes G d x n h ω) :
    Canonical G (anchors d x n h) ω i := by
  have he := endpoint_labels d x n h
  have hi' := (Forest.mem_active (historyForest G d x ω n h)).mp hi
  rcases hi'.1 with hi|hi
  · exact lineage_canonical G order d x p w r₀ n h ω hr _
      (owner_lt G d x n h ω _ ⟨true,he.1⟩)
      (owner_canonical G d x n h ω _ ⟨true,he.1⟩) i hi
  · exact lineage_canonical G order d x p w r₀ n h ω hr _
      (owner_lt G d x n h ω _ ⟨false,he.2⟩)
      (owner_canonical G d x n h ω _ ⟨false,he.2⟩) i hi

lemma active_nonhold (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : i ∈ activeNodes G d x n h ω) : nodeMark n h i ≠ none := by
  have hi2 := (Forest.mem_active _).mp hi |>.2
  exact (canonical_iff_nonhold G order d x p w r₀ n h ω hr i hi2
    (active_lt G d x n h ω i hi)).mp (active_canonical G order d x p w r₀ n h ω hr i hi)

end Active
end CriticalPercolation.BinaryLaw
end
end

end OAI
