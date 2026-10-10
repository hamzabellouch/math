import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.ContourSites

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.Boundary

def wordDir {n : ℕ} (w : Fin n → Dir) (i : ℕ) : Dir :=
  if h : i<n then w ⟨i,h⟩ else if h₀ : 0<n then w ⟨0,h₀⟩ else 0

def wordEdge {n : ℕ} (p : Grid) (w : Fin n → Dir) (i : ℕ) : Edge :=
  (p+∑ j∈Finset.range i, step (wordDir w j),wordDir w i)

lemma wordEdge_chain {n : ℕ} (p : Grid) (w : Fin n → Dir) (i : ℕ) :
    head (wordEdge p w i)=tail (wordEdge p w (i+1)) := by
  simp [wordEdge,head,tail,Finset.sum_range_succ,add_assoc]

lemma wordEdge_zero {n : ℕ} (p : Grid) (w : Fin n → Dir) :
    (wordEdge p w 0).1=p := by simp [wordEdge]

lemma wordEdge_reconstruct {n : ℕ} (hn : 0<n) (e : ℕ → Edge)
    (hchain : ∀ i, head (e i)=tail (e (i+1))) (hclose : e n=e 0) :
    ∀ i≤n, wordEdge (e 0).1 (fun j : Fin n => (e j).2) i=e i := by
  let w : Fin n → Dir := fun j => (e j).2
  have hd (i : ℕ) (hi : i<n) : wordDir w i=(e i).2 := by simp [wordDir,hi,w]
  have hv : ∀ i≤n, (wordEdge (e 0).1 w i).1=(e i).1 := by
    intro i hi
    induction i with
    | zero => exact wordEdge_zero _ _
    | succ i ih =>
      have hh : i<n := by omega
      have ih' := ih (by omega)
      have hc := wordEdge_chain (e 0).1 w i
      change (wordEdge (e 0).1 w i).1+step (wordDir w i)=
        (wordEdge (e 0).1 w (i+1)).1 at hc
      rw [← hc,ih',hd i hh]
      exact hchain i
  intro i hi
  apply Prod.ext (hv i hi)
  change wordDir w i=(e i).2
  by_cases hlt : i<n
  · exact hd i hlt
  · have hie : i=n := by omega
    subst i
    simp [wordDir,hn,hclose,w]

lemma card_words (n : ℕ) : Fintype.card (Fin n → Dir)=4^n := by
  simp [Dir]

def wordValid {n : ℕ} (p : Grid) (w : Fin n → Dir) : Prop :=
  wordEdge p w n=wordEdge p w 0 ∧ Set.InjOn (wordEdge p w) (Set.Iio n)

lemma wordValid_reconstruct {n : ℕ} (hn : 0<n) (e : ℕ → Edge)
    (hchain : ∀ i, head (e i)=tail (e (i+1))) (hclose : e n=e 0)
    (hinj : Set.InjOn e (Set.Iio n)) :
    wordValid (e 0).1 (fun j : Fin n => (e j).2) := by
  have hr := wordEdge_reconstruct hn e hchain hclose
  refine ⟨?_,?_⟩
  · rw [hr n le_rfl,hr 0 (Nat.zero_le n),hclose]
  · intro i hi j hj he
    rw [hr i hi.le,hr j hj.le] at he
    exact hinj hi hj he

lemma outsideSites_congr {n : ℕ} {e f : ℕ → Edge}
    (h : ∀ i<n, e i=f i) : outsideSites e n=outsideSites f n := by
  have hf : forwardIndices e n=forwardIndices f n := by
    apply Finset.filter_congr
    intro i hi
    rw [h i (Finset.mem_range.mp hi)]
  unfold outsideSites
  rw [hf]
  apply Finset.image_congr
  intro i hi
  dsimp only
  rw [h i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)]

theorem finite_good_contour (S : Set Grid) (hS : S.Finite) (hroot : (0,0)∈S)
    (hquad : ∀ v∈S, 0≤v.1 ∧ 0≤v.2) :
    ∃ n : ℕ, ∃ w : Fin (n+1) → Dir,
      wordValid (0,1) w ∧
      (∀ z∈outsideSites (wordEdge (0,1) w) (n+1),
        z∉S ∧ ∃ y∈S, z=y+(1,0) ∨ z=y+(0,1)) := by
  obtain ⟨l,hl,e,h0,hend,hmem,hchain,hinj⟩ := squareBoundary_closed_trail hS
    ((0,1),3) (west_root_edge_mem S hroot hquad)
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
  have he : e (n+1)=e 0 := hend.trans h0.symm
  have hp : (e 0).1=(0,1) := congrArg Prod.fst h0
  refine ⟨n,(fun j : Fin (n+1) => (e j).2),?_,?_⟩
  · simpa only [hp] using wordValid_reconstruct hl e hchain he hinj
  · have hr := wordEdge_reconstruct hl e hchain he
    rw [hp] at hr
    rw [outsideSites_congr (fun i hi => hr i hi.le)]
    exact outsideSites_failed_children S e (n+1) hmem

end CriticalPercolation.Boundary
end
end
end

end OAI
