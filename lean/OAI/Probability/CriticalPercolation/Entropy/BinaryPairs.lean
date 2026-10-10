import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.BinaryParents

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E I : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Fintype I]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (h : History E n) (ω : E → Bool)

theorem active_cluster_users_le
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h (configuration ω) ≠ 0)
    (idx : I → ℕ) (hinj : Function.Injective idx)
    (hidx : ∀ i, idx i ∈ activeNodes G d x n h (configuration ω)) (v : V) :
    (clusterUsers G (fun i => (node d x n h (idx i)).1)
      (fun i => (node d x n h (nodeParent G d x (configuration ω) n h (idx i))).1) ω v).card ≤ 2 := by
  classical
  let F := historyForest G d x (configuration ω) n h
  let S := activeNodes G d x n h (configuration ω)
  let users := clusterUsers G (fun i => (node d x n h (idx i)).1)
      (fun i => (node d x n h (F.parent (idx i))).1) ω v
  have hb (i : I) : 2 ≤ idx i ∧ idx i<n+2 :=
    ⟨(Forest.mem_active _).mp (hidx i) |>.2,active_lt G d x n h _ _ (hidx i)⟩
  have hcan (i : I) : Canonical G (anchors d x n h) (configuration ω) (idx i) :=
    active_canonical G order d x p w _ n h _ hr _ (hidx i)
  have hpcan (i : I) : Canonical G (anchors d x n h) (configuration ω) (F.parent (idx i)) :=
    nodeParent_canonical G order d x p w _ n h _ hr _ (hb i).1 (hb i).2
  have hpbound (i : I) : F.parent (idx i)<n+2 := (F.parent_lt _ (hb i).1).trans (hb i).2
  by_cases hu : users.Nonempty
  · obtain ⟨i,hi⟩ := hu
    have hi' := hi
    simp only [users,clusterUsers,Finset.mem_filter,Finset.mem_univ,true_and] at hi'
    obtain ⟨j,hj,hjc,hjv⟩ : ∃ j<n+2, Canonical G (anchors d x n h) (configuration ω) j ∧
        (G.openGraph (configuration ω)).Reachable (node d x n h j).1 v := by
      rcases hi' with hi'|hi'
      · exact ⟨idx i,(hb i).2,hcan i,hi'⟩
      · exact ⟨F.parent (idx i),hpbound i,hpcan i,hi'⟩
    have hm : Set.MapsTo idx (↑users : Set I) (↑(S.filter fun k => k=j ∨ F.parent k=j) : Set ℕ) := by
      intro k hk
      refine Finset.mem_filter.mpr ⟨hidx k,?_⟩
      simp only [users,clusterUsers,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and] at hk
      rcases hk with hk|hk
      · exact Or.inl (canonical_node_reachable_eq G d x n h (configuration ω) _ j
          (hb k).2 hj (hcan k) hjc (hk.trans hjv.symm))
      · exact Or.inr (canonical_node_reachable_eq G d x n h (configuration ω) _ j
          (hpbound k) hj (hpcan k) hjc (hk.trans hjv.symm))
    have hc : users.card ≤ (S.filter fun k => k=j ∨ F.parent k=j).card :=
      Finset.card_le_card_of_injOn idx hm hinj.injOn
    have ht := terminal_roots G order d x p w s n h (configuration ω) hr
    have hne : F.root (owner G d x n h (configuration ω) (x (interval d n h).1)) ≠
        F.root (owner G d x n h (configuration ω) (x (interval d n h).2)) := by
      change (historyForest G d x (configuration ω) n h).root _ ≠ _
      rw [ht.1,ht.2]
      omega
    exact hc.trans (F.active_pair_multiplicity hne j)
  · have he : users=∅ := Finset.not_nonempty_iff_eq_empty.mp hu
    change users.card ≤ 2
    rw [he,Finset.card_empty]
    omega

abbrev ActiveIndex (n : ℕ) (D : FixedDescriptor n) := {i : Fin n // (D i).2.2 = true}

def activeLeft (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : ActiveIndex n D) : V :=
  (descriptorNode (E := E) d x n D (i.val.val+2)).1

def activeRight (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : ActiveIndex n D) : V :=
  (descriptorNode (E := E) d x n D (descriptorParent (E := E) d x n D (i.val.val+2))).1

omit [Fintype I] in
lemma fixed_cluster_users_le (D : FixedDescriptor n) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (v : V) :
    (clusterUsers G (activeLeft (E := E) d x n D) (activeRight (E := E) d x n D) ω v).card ≤ 2 := by
  classical
  obtain ⟨hD,hr⟩ := conditionedMass_support G order d x p w s n D (ω,m) hz
  let h := fromWords (E := E) n (fun j => (D j).1) m
  have hi (i : ActiveIndex n D) : i.val.val+2 ∈ activeNodes G d x n h (configuration ω) := by
    rw [activeNodes_eq_descriptor G d x n h _ D hD]
    exact Finset.mem_image.mpr ⟨i.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.property⟩,rfl⟩
  have hinj : Function.Injective (fun i : ActiveIndex n D => i.val.val+2) := by
    intro i j he
    apply Subtype.ext
    apply Fin.ext
    dsimp only at he
    omega
  have he := active_cluster_users_le G order d x p w s n h ω hr _ hinj hi v
  have hleft (i : ActiveIndex n D) : (node d x n h (i.val.val+2)).1 = activeLeft (E := E) d x n D i :=
    congrArg Prod.fst (node_eq_descriptor G d x n h _ D hD _)
  have hright (i : ActiveIndex n D) :
      (node d x n h (nodeParent G d x (configuration ω) n h (i.val.val+2))).1 =
      activeRight (E := E) d x n D i := by
    rw [active_parent_eq_descriptor G order d x p w s n h _ hr D hD _ (hi i)]
    exact congrArg Prod.fst (node_eq_descriptor G d x n h _ D hD _)
  simp_rw [hleft,hright] at he
  exact he

noncomputable section Entropy
local instance pairsClassicalFinDecidable (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

omit [Fintype I] in
lemma configurationMass_support (D : FixedDescriptor n) (η : E → Bool)
    (hη : 0 < pushMass Prod.fst (conditionedMass G order d x p w s n D) η) :
    ∃ m, 0 < conditionedMass G order d x p w s n D (η,m) := by
  by_contra! hn
  have hz : pushMass Prod.fst (conditionedMass G order d x p w s n D) η ≤ 0 := by
    unfold pushMass
    apply Finset.sum_nonpos
    intro z _
    split_ifs with he
    · rcases z with ⟨η',m⟩
      dsimp only at he
      subst η'
      exact hn m
    · rfl
  linarith

omit [Fintype I] in

theorem conditioned_pair_entropy (D : FixedDescriptor n)
    (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    let P := pushMass Prod.fst (conditionedMass G order d x p w s n D)
    (∑ i : ActiveIndex n D,
      divergence (pushMass (pair G (activeLeft (E := E) d x n D i)
        (activeRight (E := E) d x n D i)).bare.run P)
      ((pair G (activeLeft (E := E) d x n D i) (activeRight (E := E) d x n D i)).bare.reference p)) ≤
      16/(2*p*(1-p)) * divergence P (FiniteProduct.density (QueryTree.bitWeight p)) := by
  cases Subsingleton.elim (inferInstance : DecidableEq V) (Classical.decEq V)
  cases Subsingleton.elim (inferInstance : DecidableEq E) (Classical.decEq E)
  dsimp only
  let Q := conditionedMass G order d x p w s n D
  have hQ : ∀ z, 0 ≤ Q z := conditionedMass_nonneg G order d x p w s n hp h0 h1 hδ D hD
  have hQ1 : ∑ z, Q z = 1 := by
    have he := conditionedMass_normalized G order d x p w s n D hD
    refine Eq.trans ?_ he
    apply Finset.sum_congr
    · ext z; simp only [Finset.mem_univ]
    · intro z _; rfl
  apply pair_entropy hp G (activeLeft (E := E) d x n D) (activeRight (E := E) d x n D)
    (pushMass Prod.fst Q) (pushMass_nonneg _ _ hQ) (by rw [pushMass_sum,hQ1])
  intro η hη v
  obtain ⟨m,hm⟩ := configurationMass_support G order d x p w s n D η hη
  exact fixed_cluster_users_le G order d x p w s n η D m hm.ne' v

end Entropy
end CriticalPercolation.BinaryLaw
end
end

end OAI
