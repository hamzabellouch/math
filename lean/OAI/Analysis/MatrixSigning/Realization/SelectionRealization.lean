import Mathlib
import OAI.Analysis.MatrixSigning.Potential.ChooseCoordinate
import OAI.Analysis.MatrixSigning.Realization.FaceArrayRealization
import OAI.Analysis.MatrixSigning.Realization.PencilCompileRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α β : Type*}

abbrev scoredCode (ea : α → Word) := prodCode ea ratCode
def betterData (p : (α×ℚ)×(α×ℚ)) : α×ℚ :=
  if p.2.2 < p.1.2 then p.2 else p.1
def better (ea : α → Word) : Realizes (prodCode (scoredCode ea) (scoredCode ea)) (scoredCode ea) betterData :=
  let old := first (scoredCode ea) (scoredCode ea)
  let new := second (scoredCode ea) (scoredCode ea)
  let comparison := ((old.then (second ea ratCode)).le (new.then (second ea ratCode))).ite
    (constant (prodCode (scoredCode ea) (scoredCode ea)) boolCode false)
    (constant (prodCode (scoredCode ea) (scoredCode ea)) boolCode true)
  (comparison.ite new old).congr (by
    intro input
    by_cases hcompare : input.1.2 ≤ input.2.2
    · simp [betterData,hcompare,not_lt_of_ge hcompare]
    · simp [betterData,hcompare,lt_of_not_ge hcompare])

def selectScored (ea : α → Word) := (better ea).fold
lemma selectScored_data (score : α → ℚ) (e : α → β) (xs : List α) (a : α) :
    (xs.map (fun x => (e x,score x))).foldl (fun s x => betterData (s,x)) (e a,score a)=
      (e (Descent.select score a xs),score (Descent.select score a xs)) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.foldl_cons,Descent.select,betterData]
    split_ifs <;> exact ih _

lemma select_map (f : α → β) (score : β → ℚ) (xs : List α) (a : α) :
    Descent.select score (f a) (xs.map f)=f (Descent.select (score ∘ f) a xs) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,Descent.select,Function.comp_apply]
    split_ifs <;> exact ih _

def chooseCoordinateData (xs : List ℚ) : ℕ :=
  Descent.select (fun i => -|xs.getD i 0|) 0 (List.range xs.length)
def chooseCoordinate : Realizes vectorCode natCode chooseCoordinateData :=
  let xs := first vectorCode natCode
  let i := second vectorCode natCode
  let score := (((i.both xs).then (getD ratCode 0)).abs).neg
  let all := (((identity vectorCode).both ((lengthList ratCode).then range)).then (i.both score).mapCtx)
  let initialScore := ((constant vectorCode natCode 0).both (identity vectorCode)).then (getD ratCode 0)
  let init := (constant vectorCode natCode 0).both initialScore.abs.neg
  (((init.both all).then (selectScored natCode)).then (first natCode ratCode)).congr (by
    intro xs
    change ((List.map (fun i => (i,-|xs.getD i 0|)) (List.range xs.length)).foldl
      (fun s x => betterData (s,x)) (0,-|xs.getD 0 0|)).1=_
    exact congrArg Prod.fst (selectScored_data (fun i => -|xs.getD i 0|) id (List.range xs.length) 0))
lemma chooseCoordinate_data {n : ℕ} [NeZero n] (g : Fin n → ℚ) :
    chooseCoordinateData (List.ofFn g)=(Difference.chooseCoordinate g).val := by
  unfold chooseCoordinateData Difference.chooseCoordinate
  rw [List.length_ofFn,range_finRange]
  change Descent.select (fun i => -|(List.ofFn g).getD i 0|) (0 : Fin n).val
    ((List.finRange n).map Fin.val)=_
  rw [select_map]
  have hs : ((fun i => -|(List.ofFn g).getD i 0|) ∘ Fin.val)=(fun i : Fin n => -|g i|) := by
    funext i
    exact congrArg (fun q : ℚ => -|q|) (getD_ofFn g i 0)
  rw [hs]

def gradientDirectionData (xs : List ℚ) : List ℚ :=
  (basisData (xs.length,chooseCoordinateData xs)).map
    (fun q => (if 0≤xs.getD (chooseCoordinateData xs) 0 then (-1:ℚ) else 1)*q)
def gradientDirection : Realizes vectorCode vectorCode gradientDirectionData :=
  let x := ((chooseCoordinate.both (identity vectorCode)).then (getD ratCode 0))
  let s := (((constant vectorCode ratCode 0).le x).ite
    (constant vectorCode ratCode (-1)) (constant vectorCode ratCode 1))
  let b := (((lengthList ratCode).both chooseCoordinate).then basisVector)
  ((s.both b).then vectorScale).congr (by intro xs;simp only [gradientDirectionData,decide_eq_true_eq,id_eq])
lemma gradientDirection_data {n : ℕ} [NeZero n] (g : Fin n → ℚ) :
    gradientDirectionData (List.ofFn g)=List.ofFn (Difference.rationalGradientDirection g) := by
  unfold gradientDirectionData
  rw [List.length_ofFn,chooseCoordinate_data,basis_data,getD_ofFn]
  simp only [List.map_ofFn,Function.comp_def,Difference.rationalGradientDirection]
  rfl

end CurrentKS.Realization

end

end OAI
