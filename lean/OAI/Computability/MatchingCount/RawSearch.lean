import OAI.Computability.MatchingCount.RawOptimizerData

namespace OAI

section

namespace BinaryMatching.Raw
open Finset

def residual (c : Matrix ℕ) (b : Matrix ℤ) (i j : ℕ) : Bool :=
  decide (get b i j < ((get c i j : ℕ):ℤ))
def initial (n a : ℕ) : Paths := tab n (fun v => if v=a then some [a] else none)
def predecessor (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (p : Paths) (v : ℕ) : Option ℕ :=
  (List.range n).find? (fun u => residual c b u v && (nth p u).isSome)
def pathStep (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (p : Paths) : Paths :=
  tab n (fun v => match nth p v with
    | some l => some l
    | none => match predecessor n c b p v with
      | none => none
      | some u => (nth p u).map (fun l => v::l))
def search (n : ℕ) (c : Matrix ℕ) (b : Matrix ℤ) (a k : ℕ) : Paths :=
  (pathStep n c b)^[k] (initial n a)
def reached (n : ℕ) (p : Paths) : Cut := tab n (fun v => (nth p v).isSome)

@[simp] lemma nth_pathRep {n : ℕ} (p : ResidualSearch.Table n) (v : Fin n) :
    nth (pathRep p) v.val=(p v).map (List.map Fin.val) := by simp [pathRep]

lemma residual_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (b : UnitFlow.Matrix (Fin n)) (i j : Fin n) :
    residual (matrixRep c) (matrixRep b) i.val j.val=decide (UnitMincut.residual c b i j) := by
  simp only [residual,UnitMincut.residual,get_rep]
  rfl

lemma initial_rep {n : ℕ} (a : Fin n) : initial n a.val=pathRep (ResidualSearch.initial a) := by
  apply tab_eq_rep
  intro v
  simp only [ResidualSearch.initial]
  by_cases hv : v=a
  · simp [hv]
  · have hval : v.val≠a.val := fun h => hv (Fin.ext h)
    simp [hv,hval]

lemma predecessor_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (b : UnitFlow.Matrix (Fin n))
    (p : ResidualSearch.Table n) (v : Fin n) :
    predecessor n (matrixRep c) (matrixRep b) (pathRep p) v.val=
      (ResidualSearch.predecessor (UnitMincut.residual c b) p v).map Fin.val := by
  unfold predecessor ResidualSearch.predecessor
  rw [range_eq_fin,List.find?_map]
  congr 1
  congr 1
  funext u
  simp only [Function.comp_apply,residual_rep,nth_pathRep,Option.isSome_map]

lemma pathStep_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (b : UnitFlow.Matrix (Fin n))
    (p : ResidualSearch.Table n) :
    pathStep n (matrixRep c) (matrixRep b) (pathRep p)=
      pathRep (ResidualSearch.step (UnitMincut.residual c b) p) := by
  apply tab_eq_rep
  intro v
  rw [nth_pathRep]
  simp only [ResidualSearch.step]
  cases hp : p v with
  | some l => rfl
  | none =>
    simp only [Option.map_none,predecessor_rep]
    cases hu : ResidualSearch.predecessor (UnitMincut.residual c b) p v with
    | none => rfl
    | some u =>
      simp only [Option.map_some,nth_pathRep,Option.map_map]
      rfl

lemma search_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (b : UnitFlow.Matrix (Fin n))
    (a : Fin n) (k : ℕ) : search n (matrixRep c) (matrixRep b) a.val k=
      pathRep (ResidualSearch.search (UnitMincut.residual c b) a k) := by
  induction k with
  | zero => exact initial_rep a
  | succ k ih =>
    simp only [search,Function.iterate_succ_apply'] at *
    rw [ih,pathStep_rep]
    rfl

lemma reached_rep {n : ℕ} (p : ResidualSearch.Table n) :
    reached n (pathRep p)=cutRep (ResidualSearch.reached p) := by
  apply tab_eq_rep
  intro v
  simp only [nth_pathRep,Option.isSome_map,ResidualSearch.mem_reached]
  cases p v <;> rfl

def pathFlow (p : List ℕ) (i j : ℕ) : ℤ :=
  ((p.zip p.tail).map (fun vu =>
    (if i=vu.2 ∧ j=vu.1 then 1 else 0)-(if i=vu.1 ∧ j=vu.2 then 1 else 0))).sum

lemma pathFlow_rep {n : ℕ} (p : List (Fin n)) (i j : Fin n) :
    pathFlow (p.map Fin.val) i.val j.val=UnitFlow.pathFlow p i j := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow,UnitFlow.pathFlow]
  | singleton v => simp [pathFlow,UnitFlow.pathFlow]
  | cons_cons v u p _ ih =>
    have hv : (i.val=v.val)↔i=v := Fin.ext_iff.symm
    have hu : (i.val=u.val)↔i=u := Fin.ext_iff.symm
    have jv : (j.val=v.val)↔j=v := Fin.ext_iff.symm
    have ju : (j.val=u.val)↔j=u := Fin.ext_iff.symm
    simp only [pathFlow,List.map_cons,List.tail_cons,List.zip_cons_cons,List.sum_cons,
      UnitFlow.pathFlow,UnitFlow.arc,hv,hu,jv,ju] at *
    rw [ih]
    omega
end BinaryMatching.Raw
end

end OAI
