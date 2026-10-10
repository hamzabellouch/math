import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiniteBad

namespace OAI

/-! Hypothetical outside parameters zero and one become, respectively, a
required edge and a fresh common neighbor in a finite labelled state. -/

namespace CycleClique.Construction
variable {n : ℕ}

def addedEdgeGraph (H : SimpleGraph (Fin n)) (i j : Fin n) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧ (H.Adj a b ∨ (a = i ∧ b = j) ∨ (a = j ∧ b = i))
  symm := ⟨by
    intro a b h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h.symm)
    · exact Or.inr (Or.inl h.symm)⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (i j : Fin n) :
    DecidableRel (addedEdgeGraph H i j).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

def freshGraph (H : SimpleGraph (Fin n)) (i j : Fin n) : SimpleGraph (Fin (n + 1)) where
  Adj := Fin.cases (Fin.cases False (fun b => b = i ∨ b = j))
    (fun a => Fin.cases (a = i ∨ a = j) (fun b => H.Adj a b))
  symm := ⟨by
    intro a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
    · exact id
    · exact id
    · exact id
    · exact fun h => h.symm⟩
  loopless := ⟨by
    intro a
    refine Fin.cases ?_ (fun a => ?_) a
    · exact id
    · exact H.loopless.irrefl a⟩

instance (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (i j : Fin n) :
    DecidableRel (freshGraph H i j).Adj := by
  intro a b
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
    dsimp only [freshGraph, Fin.cases_zero, Fin.cases_succ] <;> infer_instance

def freshMatrix (M : ForbiddenMatrix n) : ForbiddenMatrix (n + 1) :=
  Fin.cases (fun _ => ∅) (fun a => Fin.cases ∅ (fun b => M a b))

variable {V : Type*} {G : SimpleGraph V} {H : SimpleGraph (Fin n)}

def addedEdgeHom (f : H →g G) {i j : Fin n} (hij : G.Adj (f i) (f j)) :
    addedEdgeGraph H i j →g G where
  toFun := f
  map_rel' := by
    intro a b h
    rcases h.2 with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact f.map_adj h
    · exact hij
    · exact hij.symm

def freshHom (f : H →g G) {i j : Fin n} (z : V)
    (hiz : G.Adj (f i) z) (hjz : G.Adj (f j) z) : freshGraph H i j →g G where
  toFun := Fin.cases z f
  map_rel' := by
    intro a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
    · exact False.elim
    · intro h; rcases h with rfl | rfl; exact hiz.symm; exact hjz.symm
    · intro h; rcases h with rfl | rfl; exact hiz; exact hjz
    · exact f.map_adj

theorem freshHom_injective [DecidableEq V] (f : H →g G) (hf : Function.Injective f)
    {X : Finset V} (hfX : ∀ i, f i ∈ X) {i j : Fin n} {z : V}
    (hz : z ∉ X) (hiz : G.Adj (f i) z) (hjz : G.Adj (f j) z) :
    Function.Injective (freshHom f z hiz hjz) := by
  intro a b
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
  · exact fun _ => rfl
  · intro h
    change z = f b at h
    exact False.elim (hz (h.symm ▸ hfX b))
  · intro h
    change f a = z at h
    exact False.elim (hz (h ▸ hfX a))
  · intro h; exact congrArg Fin.succ (hf h)

theorem freshHom_mem [DecidableEq V] (f : H →g G) {X : Finset V}
    (hfX : ∀ i, f i ∈ X) {i j : Fin n} {z : V}
    (hiz : G.Adj (f i) z) (hjz : G.Adj (f j) z) :
    ∀ a, freshHom f z hiz hjz a ∈ insert z X := by
  intro a
  refine Fin.cases ?_ (fun a => ?_) a
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hfX a)

theorem freshMatrix_sound [DecidableEq V] (f : H →g G) {X : Finset V}
    {M : ForbiddenMatrix n} (hM : M.Sound G X f) {i j : Fin n} {z : V}
    (hiz : G.Adj (f i) z) (hjz : G.Adj (f j) z) :
    (freshMatrix M).Sound G (insert z X) (freshHom f z hiz hjz) := by
  have hbig := hM.enlarge_ground (Finset.subset_insert z X)
  intro a b
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
  · intro d hd; exact False.elim (Finset.notMem_empty d hd)
  · intro d hd; exact False.elim (Finset.notMem_empty d hd)
  · intro d hd; exact False.elim (Finset.notMem_empty d hd)
  · exact hbig a b

end CycleClique.Construction

end OAI
