import OAI.Analysis.ForestSpace.Coordinates

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Words

/-- Finite words, ordered by extension, including the empty root. -/
structure Word where
  letters : List ℕ
  deriving DecidableEq

namespace Word
@[ext] theorem ext {a b : Word} (h : a.letters = b.letters) : a = b := by
  cases a; cases b; cases h; rfl
instance : Countable Word := Function.Injective.countable (f := letters) (fun _ _ => ext)
instance : Infinite Word := Infinite.of_injective (fun n : ℕ => Word.mk [n]) (by
  intro i j h
  simpa using congrArg letters h)
instance : PartialOrder Word where
  le a b := a.letters <+: b.letters
  le_refl _ := List.prefix_rfl
  le_trans _ _ _ := List.IsPrefix.trans
  le_antisymm a b hab hba := by
    have h := hab.eq_of_length (Nat.le_antisymm hab.length_le hba.length_le)
    cases a; cases b; cases h; rfl

@[simp] theorem le_def (a b : Word) : a ≤ b ↔ a.letters <+: b.letters := Iff.rfl
 theorem forestOrder : ForestOrder Word := by
  intro a b c hac hbc
  rcases le_total a.letters.length b.letters.length with h | h
  · exact Or.inl (List.prefix_of_prefix_length_le hac hbc h)
  · exact Or.inr (List.prefix_of_prefix_length_le hbc hac h)

 theorem finiteAncestors (v : Word) : (Set.Iic v).Finite := by
  apply (v.letters.inits.toFinset.finite_toSet.image Word.mk).subset
  intro w hw
  exact ⟨w.letters,by simpa only [Finset.mem_coe,List.mem_toFinset,List.mem_inits] using (show w.letters <+: v.letters from hw),rfl⟩

def root : Word := ⟨[]⟩
def child (s : Word) (j : ℕ) : Word := ⟨s.letters++[j]⟩

 theorem le_child (s : Word) (j : ℕ) : s ≤ child s j := List.prefix_append _ _
 theorem child_not_le (s : Word) (j : ℕ) : ¬child s j ≤ s := by
  intro h
  have hh := h.length_le
  simp only [child,List.length_append,List.length_singleton] at hh
  omega

 theorem child_injective (s : Word) : Function.Injective (child s) := by
  intro i j h
  have hh := congrArg letters h
  simpa [child] using hh

 theorem le_child_iff (s w : Word) (j : ℕ) :
    w ≤ child s j ↔ w = child s j ∨ w ≤ s := by
  constructor
  · intro h
    by_cases hlen : w.letters.length ≤ s.letters.length
    · exact Or.inr (List.prefix_of_prefix_length_le h (le_child s j) hlen)
    · left
      apply ext
      apply h.eq_of_length
      have hh := h.length_le
      simp only [child,List.length_append,List.length_singleton] at hh ⊢
      omega
  · rintro (rfl | h)
    · exact le_rfl
    · exact h.trans (le_child s j)

 theorem ancestor_finset_child (s : Word) (j : ℕ) :
    (finiteAncestors (child s j)).toFinset = insert (child s j) (finiteAncestors s).toFinset := by
  ext w
  simp only [Set.Finite.mem_toFinset, Set.mem_Iic, Finset.mem_insert]
  exact le_child_iff s w j

 theorem path_child (s : Word) (j : ℕ) :
    pathVector (child s j) (finiteAncestors _) - pathVector s (finiteAncestors _) = eX (child s j) := by
  unfold pathVector
  rw [ancestor_finset_child,Finset.sum_insert]
  · abel
  · simpa using child_not_le s j

 theorem weakNull_path_children (s : Word) :
    WeakNull (fun j => pathVector (child s j) (finiteAncestors _) -
      pathVector s (finiteAncestors _)) := by
  simpa only [path_child] using weakNull_coordinates (child s) (child_injective s)

end Word

/-- The James-tree coordinate completion has zero AUC modulus at exactly the
comparison scale for every equivalent norm; reflexivity is not assumed. -/
 theorem word_auc_modulus_zero {α β : ℝ} (R : EquivalentNorm (X Word) α β) :
    aucModulus (X Word) R.N (α/(2*β)) = 0 := by
  apply R.bounded_trees_auc_zero not_finiteDimensional_X
    (fun _ s => pathVector (Word.mk s) (Word.finiteAncestors _))
  · intro h hh s hs
    exact norm_pathVector Word.forestOrder _ _
  · intro h hh s hs j
    have he := Word.path_child (Word.mk s) j
    change pathVector (Word.mk (s++[j])) _ - pathVector (Word.mk s) _ = _ at he
    rw [he,norm_eX]
  · intro h hh s hs
    exact Word.weakNull_path_children (Word.mk s)

end Words

section FiniteHeightForest

/-- A disjoint forest: one copy of `Nat^{≤h}` for every `h≥1`. -/
structure Vertex where
  height : ℕ
  positive : 1 ≤ height
  word : Word
  bounded : word.letters.length ≤ height
  deriving DecidableEq

namespace Vertex
@[ext] theorem ext {a b : Vertex} (hh : a.height = b.height) (hw : a.word = b.word) : a = b := by
  cases a; cases b; cases hh; cases hw; rfl
instance : Countable Vertex := Function.Injective.countable
  (f := fun v : Vertex => (v.height,v.word)) (by
    intro a b h
    exact ext (congrArg Prod.fst h) (congrArg Prod.snd h))
instance : PartialOrder Vertex where
  le a b := a.height = b.height ∧ a.word ≤ b.word
  le_refl _ := ⟨rfl,le_rfl⟩
  le_trans a b c hab hbc := ⟨hab.1.trans hbc.1,hab.2.trans hbc.2⟩
  le_antisymm a b hab hba := by
    obtain ⟨hh, hw⟩ := hab
    have he := le_antisymm hw hba.2
    cases a; cases b; cases hh; cases he; rfl
@[simp] theorem le_def (a b : Vertex) : a ≤ b ↔ a.height = b.height ∧ a.word ≤ b.word := Iff.rfl
 theorem forestOrder : ForestOrder Vertex := by
  intro a b c hac hbc
  rcases Word.forestOrder a.word b.word c.word hac.2 hbc.2 with h | h
  · exact Or.inl ⟨hac.1.trans hbc.1.symm,h⟩
  · exact Or.inr ⟨hbc.1.trans hac.1.symm,h⟩

 theorem finiteAncestors (v : Vertex) : (Set.Iic v).Finite := by
  apply Set.Finite.of_finite_image (f := fun w : Vertex => w.word)
    ((Word.finiteAncestors v.word).subset ?_) ?_
  · rintro _ ⟨w,hw,rfl⟩
    exact hw.2
  · intro a ha b hb he
    exact ext (ha.1.trans hb.1.symm) he

def node (h : ℕ) (hh : 1 ≤ h) (s : List ℕ) (hs : s.length ≤ h) : Vertex :=
  ⟨h,hh,Word.mk s,hs⟩

def child (v : Vertex) (hv : v.word.letters.length < v.height) (j : ℕ) : Vertex :=
  ⟨v.height,v.positive,Word.child v.word j,by
    simp only [Word.child,List.length_append,List.length_singleton]
    omega⟩

 theorem child_injective (v : Vertex) (hv : v.word.letters.length < v.height) :
    Function.Injective (child v hv) := by
  intro i j h
  exact Word.child_injective v.word (congrArg word h)

instance : Infinite Vertex := Infinite.of_injective
  (child (node 1 le_rfl [] (by simp)) (by simp [node]))
  (child_injective _ _)

 theorem child_not_le (v : Vertex) (hv : v.word.letters.length < v.height) (j : ℕ) :
    ¬ child v hv j ≤ v := fun h => Word.child_not_le v.word j h.2

 theorem le_child_iff (v w : Vertex) (hv : v.word.letters.length < v.height) (j : ℕ) :
    w ≤ child v hv j ↔ w = child v hv j ∨ w ≤ v := by
  constructor
  · intro hw
    rcases (Word.le_child_iff v.word w.word j).mp hw.2 with h | h
    · exact Or.inl (ext hw.1 h)
    · exact Or.inr ⟨hw.1,h⟩
  · rintro (rfl | h)
    · exact le_rfl
    · exact ⟨h.1,h.2.trans (Word.le_child v.word j)⟩

 theorem ancestor_finset_child (v : Vertex) (hv : v.word.letters.length < v.height) (j : ℕ) :
    (finiteAncestors (child v hv j)).toFinset = insert (child v hv j) (finiteAncestors v).toFinset := by
  ext w
  simp only [Set.Finite.mem_toFinset,Set.mem_Iic,Finset.mem_insert]
  exact le_child_iff v w hv j

 theorem path_child (v : Vertex) (hv : v.word.letters.length < v.height) (j : ℕ) :
    pathVector (child v hv j) (finiteAncestors _) - pathVector v (finiteAncestors _) = eX (child v hv j) := by
  unfold pathVector
  rw [ancestor_finset_child,Finset.sum_insert]
  · abel
  · simpa using child_not_le v hv j

/-- A total extension of the path vector; the off-tree values are never used. -/
noncomputable def treePath (h : ℕ) (s : List ℕ) : X Vertex :=
  if hh : 1 ≤ h then if hs : s.length ≤ h then
    pathVector (node h hh s hs) (finiteAncestors _) else 0 else 0

 theorem norm_treePath (h : ℕ) (hh : 1 ≤ h) (s : List ℕ) (hs : s.length ≤ h) :
    ‖treePath h s‖ = 1 := by
  simp only [treePath,dite_eq_left hh,dite_eq_left hs]
  exact norm_pathVector forestOrder _ _

 theorem treePath_child (h : ℕ) (hh : 1 ≤ h) (s : List ℕ) (hs : s.length < h) (j : ℕ) :
    treePath h (s++[j]) - treePath h s =
      eX (child (node h hh s (by omega)) hs j) := by
  have hs' : (s++[j]).length ≤ h := by simp; omega
  simpa only [treePath,dite_eq_left hh,dite_eq_left hs',dite_eq_left (Nat.le_of_lt hs),node,child,Word.child] using
    path_child (node h hh s (Nat.le_of_lt hs)) hs j

end Vertex

 theorem finite_forest_auc_modulus_zero {α β : ℝ} (R : EquivalentNorm (X Vertex) α β) :
    aucModulus (X Vertex) R.N (α/(2*β)) = 0 := by
  apply R.bounded_trees_auc_zero not_finiteDimensional_X Vertex.treePath
  · exact Vertex.norm_treePath
  · intro h hh s hs j
    rw [Vertex.treePath_child h hh s hs j,norm_eX]
  · intro h hh s hs
    simpa only [Vertex.treePath_child h hh s hs] using
      weakNull_coordinates _ (Vertex.child_injective (Vertex.node h hh s (Nat.le_of_lt hs)) hs)

end FiniteHeightForest

end

end ForestSpace

end OAI
