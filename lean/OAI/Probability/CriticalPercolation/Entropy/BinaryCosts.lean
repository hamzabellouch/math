import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinaryPrefix
import OAI.Probability.CriticalPercolation.Entropy.BinaryRaw
import OAI.Probability.CriticalPercolation.Entropy.BinaryPairs

namespace OAI

section
section
namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y : Type*}

noncomputable def representative (f : X → Y) (x₀ : X) (y : Y) : X :=
  if h : ∃ x, f x = y then h.choose else x₀

lemma representative_run (f : X → Y) (x₀ x : X) :
    f (representative f x₀ (f x)) = f x := by
  unfold representative
  rw [dite_eq_left ⟨x,rfl⟩]
  exact (show ∃ y, f y = f x from ⟨x,rfl⟩).choose_spec
end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct ExactExposure ClusterDeletion

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E)

lemma markWeight_eq_raw_of_admissible (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) (p : ℝ) (w : E → Prop → ℝ)
    (ω : E → Bool) (e : E) (ha : Admissible G B a b ω e) :
    markWeight G order B a b p w ω e =
      G.rawContact order B a p w (G.clusterObject (configuration ω) B) (configuration ω) (some e) := by
  obtain ⟨hmiss,u,v,hev,hu,hv⟩ := ha
  have hau : a ∉ roots (G.openGraph (configuration ω)) B := by
    rintro ⟨z,hz,hza⟩
    exact hmiss ⟨z,hz,hza.symm⟩
  have hcut : e ∈ G.cutEdges (roots (G.openGraph (configuration ω)) B) := by
    refine ⟨u,v,hev,?_,b,hb,hv⟩
    rintro ⟨z,hz,hzu⟩
    exact hmiss ⟨z,hz,hu.trans hzu.symm⟩
  have ha' : Admissible G B a b ω e := ⟨hmiss,u,v,hev,hu,hv⟩
  simp [markWeight,rawContact,clusterObject,contactWeight,ha',hau,hcut]

lemma markWeight_le_raw (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (ω : E → Bool) (e : E) :
    markWeight G order B a b p w ω e ≤
      G.rawContact order B a p w (G.clusterObject (configuration ω) B) (configuration ω) (some e) := by
  by_cases ha : Admissible G B a b ω e
  · exact (G.markWeight_eq_raw_of_admissible order B a b hb p w ω e ha).le
  · rw [markWeight,ite_eq_right ha]
    exact G.rawContact_nonneg order B a hp w h0 h1 _ _ _

lemma rawContact_ne_zero_of_kernel (order : List (LazyDFS.Dart V E))
    (B : Set V) (a : V) (p : ℝ) (w : E → Prop → ℝ)
    (C : ClusterObject V E) (ω : E → Prop) (m : Option E)
    (hk : G.contactKernel order B a p w C ω m ≠ 0) :
    G.rawContact order B a p w C ω m ≠ 0 := by
  unfold contactKernel rawContact at *
  split_ifs at *
  · exact one_ne_zero
  · exact hk
  · cases m with
    | none => exact hk
    | some e => exact (div_ne_zero_iff.mp hk).1
end CriticalPercolation.BondGraph

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E : Type*}

lemma descriptorParent_lt (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n)
    (i : ℕ) (hi : 0 < i) : descriptorParent (E := E) d x n D i < i := by
  unfold descriptorParent
  exact (Finset.sup_lt_iff hi).mpr (fun j hj => Finset.mem_range.mp (Finset.mem_filter.mp hj).1)

lemma scheduledAnchor_node (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) :
    scheduledAnchor (E := E) d x n (fun j => (D j).1) i.val =
      (descriptorNode (E := E) d x n D (i.val+2)).1 :=
  (current_prefix_anchor d x n _ i.val i.isLt).symm

lemma scheduledTargets_nodes (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) :
    scheduledTargets (E := E) d x n (fun j => (D j).1) i.val =
      {v | ∃ j < i.val+2, (descriptorNode (E := E) d x n D j).1=v} :=
  (targets_prefix d x n _ i.val i.isLt.le).symm

lemma scheduled_parent_mem (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) :
    (descriptorNode (E := E) d x n D (descriptorParent (E := E) d x n D (i.val+2))).1 ∈
      scheduledTargets (E := E) d x n (fun j => (D j).1) i.val := by
  rw [scheduledTargets_nodes]
  exact ⟨_,descriptorParent_lt d x n D _ (by omega),rfl⟩

variable [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

lemma supported_active_admissible (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0)
    (i : ActiveIndex n D) :
    ∃ e, m i.val = some e ∧ Admissible G
      (scheduledTargets (E := E) d x n (fun j => (D j).1) i.val.val)
      (activeLeft (E := E) d x n D i) (activeRight (E := E) d x n D i) ω e := by
  obtain ⟨hD,hr⟩ := conditionedMass_support G order d x p w s n D (ω,m) hz
  let h := fromWords (E := E) n (fun j => (D j).1) m
  have hi : i.val.val+2 ∈ activeNodes G d x n h (configuration ω) := by
    rw [activeNodes_eq_descriptor G d x n h _ D hD]
    exact Finset.mem_image.mpr ⟨i.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.property⟩,rfl⟩
  have hn := active_nonhold G order d x p w _ n h _ hr _ hi
  obtain ⟨e,he⟩ := Option.ne_none_iff_exists'.mp hn
  refine ⟨e,?_,?_⟩
  · have hm := marks_nodeMark n h i.val
    rw [marks_fromWords] at hm
    exact hm.trans he
  · have hc := active_canonical G order d x p w _ n h _ hr _ hi
    have hmiss := canonical_misses_targets G d x n h _ _ (by have := i.val.isLt; omega) hc
    obtain ⟨_,u,v,hev,hu,hv⟩ := node_mark_geometry G order d x p w _ n h _ hr _ (by omega)
      (by have := i.val.isLt; omega) e he
    have hl : (node d x n h (i.val.val+2)).1 = activeLeft (E := E) d x n D i :=
      congrArg Prod.fst (node_eq_descriptor G d x n h _ D hD _)
    have hr' : (node d x n h (nodeParent G d x (configuration ω) n h (i.val.val+2))).1 =
        activeRight (E := E) d x n D i := by
      rw [active_parent_eq_descriptor G order d x p w s n h _ hr D hD _ hi]
      exact congrArg Prod.fst (node_eq_descriptor G d x n h _ D hD _)
    have ht : targets d x n h (i.val.val+2) =
        scheduledTargets (E := E) d x n (fun j => (D j).1) i.val.val := by
      rw [targets_prefix d x n h _ i.val.isLt.le,scheduledTargets_eq d x n _ m _ i.val.isLt.le]
    rw [hl,ht] at hmiss
    exact ⟨hmiss,u,v,hev,hl ▸ hu,hr' ▸ hv⟩

lemma supported_schedule_ne_zero (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n) :
    scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) ≠ 0 := by
  obtain ⟨_,hr⟩ := conditionedMass_support G order d x p w s n D (ω,m) hz
  let h := fromWords (E := E) n (fun j => (D j).1) m
  have hp := density_prefix_support G order d x p w _ n h _ hr (i.val+1) i.isLt
  have hk := (density_step_support G order d x p w _ i.val (historyPrefix n h (i.val+1)) _ hp).2.1
  have hm : (historyPrefix n h (i.val+1)).2.2 = m i := by
    rw [← nodeMark_current,nodeMark_prefix n h (i.val+1) i.isLt (i.val+2) (by omega)]
    rw [← marks_nodeMark,marks_fromWords]
  rw [prefix_succ_fst n h i.val i.isLt,hm] at hk
  unfold scheduleWeight
  rw [scheduledTargets_eq d x n _ m i.val i.isLt.le,scheduledAnchor_eq d x n _ m i.val i.isLt.le]
  exact G.rawContact_ne_zero_of_kernel order _ _ p w _ _ _ hk

end CriticalPercolation.BinaryLaw
end
end

end OAI
