import OAI.Probability.DilutedSpin.QTopologyBound

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

namespace SplitMap
variable {n : ℕ} {k l : ℕ+} {C : Fin k → PrescribedTree n} {D : Fin l → PrescribedTree n}

def ofChildren (e : Fin k → Fin l) (he : Function.Injective e)
    (f : ∀ i, SplitMap (C i) (D (e i))) : SplitMap (.node k C) (.node l D) where
  leaf a := ⟨e a.1,(f a.1).leaf a.2⟩
  split a b := by
    obtain ⟨i,a⟩ := a
    obtain ⟨j,b⟩ := b
    by_cases hij : i=j
    · subst j
      rw [splitDepth_same_child,splitDepth_same_child,(f i).split]
    · rw [splitDepth_diff_child _ _ _ (fun h => hij (he h)),splitDepth_diff_child _ _ _ hij]

lemma leaves_le {n : ℕ} {S T : PrescribedTree n} (f : SplitMap S T) : S.leaves ≤ T.leaves := by
  simpa only [card_leaf] using Fintype.card_le_of_injective f.leaf f.injective

end SplitMap

/-- Every nonempty set of leaf positions has its literal induced leveled tree.
Singleton unary stretches are kept; a SplitMap retains the exact pair splits. -/
theorem exists_subset_tree {n : ℕ} (T : PrescribedTree n) (A : Finset T.Leaf) (hA : A.Nonempty) :
    ∃ (U : PrescribedTree n) (f : SplitMap U T), ∀ b, (∃ a, f.leaf a=b) ↔ b∈A := by
  classical
  induction T with
  | leaf =>
    refine ⟨.leaf,⟨id,fun _ _ => rfl⟩,?_⟩
    intro b
    have hb : b∈A := by obtain ⟨a,ha⟩ := hA; cases a; cases b; exact ha
    exact iff_of_true ⟨b,rfl⟩ hb
  | @node n k C ih =>
    let B (i : Fin k) : Finset (C i).Leaf := Finset.univ.filter (fun b => (⟨i,b⟩ : (PrescribedTree.node k C).Leaf)∈A)
    let I := {i : Fin k // (B i).Nonempty}
    have hn : Nonempty I := by
      obtain ⟨⟨i,b⟩,hb⟩ := hA
      refine ⟨⟨i,⟨b,?_⟩⟩⟩
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hb
    let : Nonempty I := hn
    let l : ℕ+ := ⟨Fintype.card I,Fintype.card_pos⟩
    let e : Fin l ≃ I := (Fintype.equivFin I).symm
    choose U f hf using fun i : I => ih i.val (B i.val) i.property
    let g : SplitMap (.node l (fun j => U (e j))) (.node k C) :=
      SplitMap.ofChildren (fun j => (e j).val)
        (fun i j h => e.injective (Subtype.ext h)) (fun j => f (e j))
    refine ⟨.node l (fun j => U (e j)),g,?_⟩
    rintro ⟨i,b⟩
    constructor
    · rintro ⟨⟨j,a⟩,ha⟩
      have hh : (⟨(e j).val,(f (e j)).leaf a⟩ : (PrescribedTree.node k C).Leaf)∈A := by
        exact (Finset.mem_filter.mp ((hf (e j) _).mp ⟨a,rfl⟩)).2
      exact ha ▸ hh
    · intro hb
      have hbi : b∈B i := by
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hb
      let t : I := ⟨i,⟨b,hbi⟩⟩
      obtain ⟨a,ha⟩ := (hf t b).mpr hbi
      have hh : ∃ a' : (U (e (e.symm t))).Leaf,
          (⟨(e (e.symm t)).val,(f (e (e.symm t))).leaf a'⟩ : (PrescribedTree.node k C).Leaf)=⟨i,b⟩ := by
        rw [Equiv.apply_symm_apply]
        exact ⟨a,congrArg (fun z : (C i).Leaf => (⟨i,z⟩ : (PrescribedTree.node k C).Leaf)) ha⟩
      obtain ⟨a',ha'⟩ := hh
      exact ⟨⟨e.symm t,a'⟩,ha'⟩

end DilutedSpinGlass.PrescribedTree

end

end OAI
