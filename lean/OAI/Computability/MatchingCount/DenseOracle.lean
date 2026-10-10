import OAI.Computability.MatchingCount.BinaryAlgorithm

namespace OAI

section

namespace BinaryMatching.DenseOracle
open Finset UnitFlow CutAlgebra OddCutParity
variable {n : ℕ}

abbrev Matrix (n : ℕ) (α : Type) := Vector (Vector α n) n

def make {α : Type} (f : Fin n → Fin n → α) : Matrix n α :=
  Vector.ofFn (fun i => Vector.ofFn (f i))

def view {α : Type} (a : Matrix n α) : Fin n → Fin n → α := fun i j => a[i][j]

@[simp] lemma view_make {α : Type} (f : Fin n → Fin n → α) : view (make f)=f := by
  funext i j; simp [view,make]

abbrev Paths (n : ℕ) := Vector (Option (List (Fin n))) n

def pathView (p : Paths n) : ResidualSearch.Table n := fun v => p[v]

def pathInitial (a : Fin n) : Paths n := Vector.ofFn (ResidualSearch.initial a)

def pathStep (c : Matrix n ℕ) (b : Matrix n ℤ) (p : Paths n) : Paths n :=
  Vector.ofFn (ResidualSearch.step (UnitMincut.residual (view c) (view b)) (pathView p))

def search (c : Matrix n ℕ) (b : Matrix n ℤ) (a : Fin n) : ℕ → Paths n
  | 0 => pathInitial a
  | k+1 => pathStep c b (search c b a k)

lemma pathView_ofFn (p : ResidualSearch.Table n) : pathView (Vector.ofFn p)=p := by
  funext v; simp [pathView]

lemma search_view (c : Matrix n ℕ) (b : Matrix n ℤ) (a : Fin n) (k : ℕ) :
    pathView (search c b a k)=ResidualSearch.search (UnitMincut.residual (view c) (view b)) a k := by
  induction k with
  | zero => exact pathView_ofFn _
  | succ k ih => simp only [search,pathStep,pathView_ofFn,ih,ResidualSearch.search]

def augment (c : Matrix n ℕ) (a z : Fin n) (b : Matrix n ℤ) : Matrix n ℤ :=
  match (search c b a n)[z] with
  | none => b
  | some p => make (fun i j => view b i j+pathFlow p i j)

def iterate (c : Matrix n ℕ) (a z : Fin n) : ℕ → Matrix n ℤ
  | 0 => make (fun _ _ => 0)
  | k+1 => augment c a z (iterate c a z k)

lemma augment_view (c : Matrix n ℕ) (a z : Fin n) (b : Matrix n ℤ) :
    view (augment c a z b)=UnitMincut.augment (view c) a z (view b) := by
  have hs := congrFun (search_view c b a n) z
  change (search c b a n)[z]=_ at hs
  simp only [augment,hs,UnitMincut.augment]
  cases h : ResidualSearch.search (UnitMincut.residual (view c) (view b)) a n z <;>
    simp only [view_make]

lemma iterate_view (c : Matrix n ℕ) (a z : Fin n) (k : ℕ) :
    view (iterate c a z k)=UnitMincut.iterate (view c) a z k := by
  induction k with
  | zero => exact view_make _
  | succ k ih => simp only [iterate,augment_view,ih,UnitMincut.iterate]

def mincut (c : Matrix n ℕ) (a z : Fin n) : Finset (Fin n) :=
  let b := iterate c a z (UnitMincut.sourceCapacity (view c) a)
  ResidualSearch.reached (pathView (search c b a n))

lemma mincut_eq (c : Matrix n ℕ) (a z : Fin n) : mincut c a z=UnitMincut.mincut (view c) a z := by
  unfold mincut UnitMincut.mincut
  dsimp only
  rw [search_view]
  have h := iterate_view c a z (UnitMincut.sourceCapacity (view c) a)
  rw [h]

def terminalCut (c : Matrix n ℕ) (U : Finset (Fin n)) : Finset (Fin n) :=
  let cuts := (((List.finRange n).product (List.finRange n)).filter
    (fun az => decide (az.1∈U ∧ az.2∈U ∧ az.1≠az.2))).map
    (fun az => mincut c az.1 az.2)
  ((cuts.argmin (cutCapacity (view c))).getD ∅)

lemma terminalCut_eq (c : Matrix n ℕ) (U : Finset (Fin n)) :
    terminalCut c U=TerminalMincut.terminalCut (view c) U := by
  simp only [terminalCut,mincut_eq,TerminalMincut.terminalCut,TerminalMincut.pairCuts]

def contract (c : Matrix n ℕ) (f : Fin n → Fin n) : Matrix n ℕ := make (push (view c) f)

@[simp] lemma contract_view (c : Matrix n ℕ) (f : Fin n → Fin n) :
    view (contract c f)=push (view c) f := view_make _

def recurse : ℕ → Matrix n ℕ → Finset (Fin n) → Finset (Fin n)
  | 0,_,_ => ∅
  | k+1,c,U =>
    let A := terminalCut c U
    if OddSide U A then A else
      match OddMincut.outside A, OddMincut.outside Aᶜ with
      | some r,some q =>
        let f := contractMap A r
        let g := contractMap Aᶜ q
        let X := recurse k (contract c f) (A∩U)
        let Y := recurse k (contract c g) (Aᶜ∩U)
        OddMincut.cheaper (view c) (lift f X) (lift g Y)
      | _,_ => ∅

lemma recurse_eq (k : ℕ) (c : Matrix n ℕ) (U : Finset (Fin n)) :
    recurse k c U=OddMincut.recurse k (view c) U := by
  induction k generalizing c U with
  | zero => rfl
  | succ k ih =>
    simp only [recurse,terminalCut_eq,OddMincut.recurse]
    split
    · rfl
    · cases h₁ : OddMincut.outside (TerminalMincut.terminalCut (view c) U) <;>
        cases h₂ : OddMincut.outside (TerminalMincut.terminalCut (view c) U)ᶜ <;>
        simp only [ih,contract_view]

def oddCut (c : Matrix n ℕ) (U : Finset (Fin n)) : Finset (Fin n) := recurse U.card c U

lemma oddCut_eq (c : Matrix n ℕ) (U : Finset (Fin n)) :
    oddCut c U=OddMincut.oddCut (view c) U := recurse_eq _ _ _

 theorem oddCut_correct (c : Matrix n ℕ) (hc : ∀ i j, view c i j=view c j i)
    (U : Finset (Fin n)) (he : Even U.card) (hU : 2≤U.card) :
    OddSide U (oddCut c U) ∧
      ∀ S, OddSide U S → cutCapacity (view c) (oddCut c U) ≤ cutCapacity (view c) S := by
  rw [oddCut_eq]
  exact OddMincut.oddCut_correct _ hc _ he hU

end BinaryMatching.DenseOracle
end

end OAI
