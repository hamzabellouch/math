import OAI.Computability.MatchingCount.ParamRoutine

namespace OAI

section

namespace BinaryMatching.Raw
open Finset
abbrev Matrix (α : Type) := List (List α)
abbrev Cut := List Bool
abbrev Paths := List (Option (List ℕ))

def nth {α : Type} [Inhabited α] (l : List α) (i : ℕ) : α := l[i]?.getD default
def get {α : Type} [Inhabited α] (a : Matrix α) (i j : ℕ) : α := nth (nth a i) j
def tab {α : Type} (n : ℕ) (f : ℕ → α) : List α := (List.range n).map f
def matrix {α : Type} (n : ℕ) (f : ℕ → ℕ → α) : Matrix α := tab n (fun i => tab n (f i))
def view {α : Type} [Inhabited α] (n : ℕ) (a : Matrix α) : Fin n → Fin n → α :=
  fun i j => get a i.val j.val
def mem (S : Cut) (i : ℕ) : Bool := nth S i
def empty (n : ℕ) : Cut := List.replicate n false
def full (n : ℕ) : Cut := List.replicate n true
def inter (n : ℕ) (S T : Cut) : Cut := tab n (fun i => mem S i && mem T i)
def compl (n : ℕ) (S : Cut) : Cut := tab n (fun i => !mem S i)
def cardinal (S : Cut) : ℕ := (S.filter id).length

def vectorRep {n : ℕ} {α : Type} (f : Fin n → α) : List α := List.ofFn f
def matrixRep {n : ℕ} {α : Type} (f : Fin n → Fin n → α) : Matrix α :=
  vectorRep (fun i => vectorRep (f i))
def cutRep {n : ℕ} (S : Finset (Fin n)) : Cut := vectorRep (fun i => decide (i∈S))
def pathRep {n : ℕ} (p : ResidualSearch.Table n) : Paths :=
  vectorRep (fun i => (p i).map (List.map Fin.val))

lemma tab_eq_ofFn {α : Type} (n : ℕ) (f : ℕ → α) :
    tab n f=List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp [tab]
  · intro i hi hi'
    simp [tab]

lemma range_eq_fin (n : ℕ) : List.range n=(List.finRange n).map Fin.val := by
  have h := tab_eq_ofFn n id
  simpa [tab,List.finRange,List.map_ofFn,Function.comp_def] using h

@[simp] lemma at_rep {n : ℕ} {α : Type} [Inhabited α] (f : Fin n → α) (i : Fin n) :
    nth (vectorRep f) i.val=f i := by simp [nth,vectorRep,i.isLt]

@[simp] lemma get_rep {n : ℕ} {α : Type} [Inhabited α] (f : Fin n → Fin n → α) (i j : Fin n) :
    get (matrixRep f) i.val j.val=f i j := by simp [get,matrixRep]

@[simp] lemma mem_rep {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    mem (cutRep S) i.val=decide (i∈S) := by simp [mem,cutRep]

lemma tab_eq_rep {n : ℕ} {α : Type} (g : ℕ → α) (f : Fin n → α)
    (h : ∀ i,g i.val=f i) : tab n g=vectorRep f := by
  rw [tab_eq_ofFn]; congr 1; funext i; exact h i
lemma matrix_eq_rep {n : ℕ} {α : Type} (g : ℕ → ℕ → α) (f : Fin n → Fin n → α)
    (h : ∀ i j,g i.val j.val=f i j) : matrix n g=matrixRep f := by
  apply tab_eq_rep
  intro i
  exact tab_eq_rep _ _ (h i)

lemma empty_rep (n : ℕ) : empty n=cutRep (∅:Finset (Fin n)) := by
  simp [empty,cutRep,vectorRep]
lemma full_rep (n : ℕ) : full n=cutRep (univ:Finset (Fin n)) := by
  simp [full,cutRep,vectorRep]
lemma inter_rep {n : ℕ} (S T : Finset (Fin n)) :
    inter n (cutRep S) (cutRep T)=cutRep (S∩T) := by
  apply tab_eq_rep
  intro i
  simp
lemma compl_rep {n : ℕ} (S : Finset (Fin n)) : compl n (cutRep S)=cutRep Sᶜ := by
  apply tab_eq_rep
  intro i
  simp only [mem_rep,Finset.mem_compl,decide_not]
lemma cardinal_rep {n : ℕ} (S : Finset (Fin n)) : cardinal (cutRep S)=S.card := by
  unfold cardinal cutRep vectorRep
  have hh : List.ofFn (fun i : Fin n => decide (i∈S))=
    (List.finRange n).map (fun i => decide (i∈S)) := by
      simp [List.finRange,List.map_ofFn,Function.comp_def]
  rw [hh]
  rw [List.filter_map]
  simp only [List.length_map]
  rw [←List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  simp

lemma sum_tab {α : Type} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    (tab n f).sum=∑ i : Fin n,f i.val := by rw [tab_eq_ofFn,List.sum_ofFn]

end BinaryMatching.Raw
end

end OAI
