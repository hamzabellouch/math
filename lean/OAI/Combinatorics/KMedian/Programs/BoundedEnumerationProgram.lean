import Mathlib
import OAI.Combinatorics.KMedian.Reduction.RationalThreshold
import OAI.Combinatorics.KMedian.Programs.UnitRepresentativeProgram

namespace OAI


                                                 
section
namespace MetricKMedian.Reduction.Enumeration
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
def words {α : Type} : ℕ → List α → List (List α)
  | 0,_ => [[]]
  | c+1,xs => []::xs.flatMap (fun a => (words c xs).map (List.cons a))
@[fun_prop] theorem words_poly {α : Type} [Coding α] [Inhabited α] (c : ℕ) : Poly (@words α c) := by
  induction c with
  | zero => exact const [[]]
  | succ c ih =>
    change Poly (fun xs : List α => []::xs.flatMap (fun a => (words c xs).map (List.cons a)))
    have h : Poly (fun xs : List α => xs.flatMap (fun a => (words c xs).map (List.cons a))) := by
      apply list_flatMap
      · apply list_map
        · exact comp list_cons (pair (comp snd fst) snd)
        · exact comp ih fst
      · fun_prop
    have hh := comp (list_cons (α := List α)) (pair (const ([] : List α) : Poly (fun _ : List α => ([] : List α))) h)
    exact hh

 theorem mem_words {α : Type} (xs : List α) (c : ℕ) (ys : List α) :
    ys∈words c xs ↔ ys.length≤c ∧ ∀a∈ys,a∈xs := by
  induction c generalizing ys with
  | zero => simp only [words,List.mem_singleton,List.length_eq_zero_iff,Nat.le_zero]; constructor
            · rintro rfl; simp
            · rintro ⟨rfl,_⟩; rfl
  | succ c ih =>
    cases ys with
    | nil => simp [words]
    | cons a ys =>
      simp only [words,List.mem_cons,List.cons_ne_nil,false_or,List.mem_flatMap,List.mem_map,List.cons.injEq]
      constructor
      · rintro ⟨b,hb,z,hz,he,hz'⟩
        subst b
        subst z
        obtain ⟨hl,hm⟩ := (ih ys).mp hz
        exact ⟨by simp only [List.length_cons]; omega,by simpa only [List.mem_cons,forall_eq_or_imp] using And.intro hb hm⟩
      · rintro ⟨hl,hm⟩
        refine ⟨a,hm a (by simp),ys,(ih ys).mpr ⟨by simp only [List.length_cons] at hl; omega,?_⟩,rfl,rfl⟩
        intro b hb
        exact hm b (by simp [hb])
 theorem choices_eq {α : Type} [LinearOrder α] (T : Finset α) (c : ℕ) :
    ((words c (T.sort (·≤·))).map List.toFinset).toFinset=deletionChoices T c := by
  ext D
  simp only [List.mem_toFinset,List.mem_map,mem_deletionChoices]
  constructor
  · rintro ⟨ys,hy,rfl⟩
    obtain ⟨hl,hm⟩ := (mem_words _ _ _).mp hy
    exact ⟨fun a ha => (mem_sort _).mp (hm a (List.mem_toFinset.mp ha)),(List.toFinset_card_le _).trans hl⟩
  · rintro ⟨hsub,hcard⟩
    refine ⟨D.sort (·≤·),(mem_words _ _ _).mpr ⟨by simpa using hcard,?_⟩,by simp⟩
    intro a ha
    exact (mem_sort _).mpr (hsub ((mem_sort _).mp ha))
def maskWord (x : Row × List ℕ) : Row := (indices x.1).map (fun i => (x.2.map (fun a => decide (a=i))).any id)
@[fun_prop] theorem maskWord_poly : Poly maskWord := by
  unfold maskWord
  apply list_map
  · apply comp bool_any
    apply list_map <;> fun_prop
  · fun_prop
 theorem maskWord_view {n : ℕ} (T : Finset (Fin n)) (ys : List (Fin n)) :
    maskWord (setView T,ys.map Fin.val)=setView ys.toFinset := by
  simp only [maskWord,indices,setView,List.length_ofFn,RoundingList.range_finRange,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_def,List.map_map,List.any_eq_true,List.mem_map,id_eq,decide_eq_true_eq,List.mem_toFinset]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,he⟩
    exact (Fin.ext (of_decide_eq_true he)) ▸ ha
  · intro hi
    exact ⟨true,⟨i,hi,by simp⟩,rfl⟩
 theorem words_map {α β : Type} (f : α → β) (c : ℕ) (xs : List α) :
    words c (xs.map f)=(words c xs).map (List.map f) := by
  induction c with
  | zero => rfl
  | succ c ih => simp only [words,List.flatMap_map,List.map_cons,List.map_nil,List.map_flatMap,ih,List.map_map,Function.comp_def]

def choicesRaw (c : ℕ) (T : Row) : Table :=
  (words c (Preparation.RationalUnitInput.Program.ranks T)).map (fun ys => maskWord (T,ys))
@[fun_prop] theorem choicesRaw_poly (c : ℕ) : Poly (choicesRaw c) := by unfold choicesRaw; apply list_map <;> fun_prop
 theorem choicesRaw_view {n : ℕ} (T : Finset (Fin n)) (c : ℕ) : choicesRaw c (setView T)=
    ((words c (List.ofFn (T.orderEmbOfFin rfl))).map List.toFinset).map setView := by
  unfold choicesRaw
  rw [Preparation.RationalUnitInput.Program.ranks_view]
  have hr : List.ofFn (fun a => (T.orderEmbOfFin rfl a).val)=(List.ofFn (T.orderEmbOfFin rfl)).map Fin.val := by simp only [List.map_ofFn,Function.comp_def]
  rw [hr,words_map,List.map_map,List.map_map]
  apply List.map_congr_left
  intro ys _
  exact maskWord_view T ys
end MetricKMedian.Reduction.Enumeration
end

end OAI
