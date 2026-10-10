import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialArrays
import OAI.Analysis.MatrixSigning.Complexity.PolynomialLists
import OAI.Analysis.MatrixSigning.Realization.SearchRealization
import OAI.Analysis.MatrixSigning.Realization.FilterRealization
import OAI.Analysis.MatrixSigning.Realization.ScheduleRealization
import OAI.Analysis.MatrixSigning.Realization.DependentRealization
import OAI.Analysis.MatrixSigning.Realization.SelectionRealization

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

lemma flatten_code_le (ea : α → Word) (xs : List (List α)) :
    (listCode ea xs.flatten).length≤(listCode (listCode ea) xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatten_cons,listCode_append,List.length_append,listCode_cons,prodCode_length]
      omega
instance size_appendList (ea : α → Word) : FoldSize (appendList ea) := by
  refine ⟨⟨2*X,?_⟩⟩
  intro s xs ys zs h
  rw [fold_append_flatten,listCode_append,List.length_append]
  have hs := le_prodCode_left (ea:=listCode ea) (eb:=listCode (listCode ea)) (s,xs)
  have hy := (flatten_code_le ea ys).trans ((prefix_code_length (listCode ea) xs ys zs h).trans (le_prodCode_right (ea:=listCode ea) (s,xs)))
  change _≤2*(prodCode (listCode ea) (listCode (listCode ea)) (s,xs)).length
  dsimp only at hs hy
  omega
instance poly_flattenList (ea : α → Word) : PolyTime (flattenList ea) := by unfold flattenList;infer_instance
instance poly_joinList (ea : α → Word) : PolyTime (joinList ea) := by unfold joinList;infer_instance
instance poly_singleton (ea : α → Word) : PolyTime (singleton ea) := by unfold singleton;apply poly_then
instance poly_flatMap {f : α → List β} (r : Realizes ea (listCode eb) f) [PolyTime r] :
    PolyTime r.flatMap := by unfold Realizes.flatMap;infer_instance
instance poly_filterCtx {p : γ×α → Bool} (r : Realizes (prodCode ec ea) boolCode p) [PolyTime r] :
    PolyTime r.filterCtx := by unfold Realizes.filterCtx;infer_instance

instance poly_binarySucc : PolyTime binarySucc := ⟨⟨2*X+6,fun _ => le_rfl⟩⟩
lemma binaryNat_length_le (n : ℕ) : (binaryNatCode n).length≤n := by
  change KS.W01.natPayloadLength n≤n
  rw [KS.W01.natPayloadLength_eq_size]
  exact Nat.size_le.mpr Nat.lt_two_pow_self
instance size_binarySucc : IterateSize binarySucc := by
  refine ⟨⟨2*X+2,?_⟩⟩
  intro x n
  rw [Nat.succ_iterate]
  change KS.W01.natPayloadLength (x+n)≤2*(KS.W01.natPayloadLength x+n)+2
  rw [KS.W01.natPayloadLength_eq_size,KS.W01.natPayloadLength_eq_size]
  have hx : x<2^(x.size+n) := (Nat.lt_size_self x).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hn : n<2^(x.size+n) := (Nat.lt_two_pow_self (n:=n)).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have ht : (x+n).size≤x.size+n+1 := Nat.size_le.mpr (by rw [pow_succ];omega)
  omega
instance poly_natToBinary : PolyTime natToBinary := by unfold natToBinary;infer_instance

lemma psd_raw_poly : ∃ p : NaturalPolynomial,∀a,PSDCleanRoutine.ticks a≤p.eval (PSDCleanRoutine.input a).length := by
  refine ⟨5*X+3*NaturalPolynomial.constant PSDControllerPolynomial.coefficient*(X+1)^58+6,?_⟩
  intro a
  have h := PSDCleanRoutine.ticks_le a
  have hd : (Computability.encodeNat a.1).length≤(PSDCleanRoutine.input a).length := by
    simp only [PSDCleanRoutine.input,List.length_append,KS.W01.length_frame];omega
  have hm : (KS.W08.denseMatrixTape a.2).length≤(PSDCleanRoutine.input a).length := by
    simp only [PSDCleanRoutine.input,List.length_append];omega
  unfold PSDCleanRoutine.controllerTicks KS.W29.polynomialFuel at h
  have hp := Nat.mul_le_mul_left PSDControllerPolynomial.coefficient (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 58)
  change _≤5*(PSDCleanRoutine.input a).length+3*PSDControllerPolynomial.coefficient*((PSDCleanRoutine.input a).length+1)^58+6
  rw [Nat.mul_assoc]
  omega
instance poly_psdStored : PolyTime psdStored := by
  unfold psdStored
  refine @poly_congr _ _ _ _ _ _ _ _ ?_
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · refine @poly_changeOutput _ _ _ _ _ _ _ _ _ _ ?_
    refine @poly_reindex _ _ _ _ _ _ _ _ _ _ ?_
    refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · apply poly_then
    · apply poly_then
  · exact ⟨psd_raw_poly⟩

instance poly_natLE : PolyTime natLE := by unfold natLE;infer_instance
instance poly_natEq : PolyTime natEq := by unfold natEq;infer_instance
instance poly_matrixEntry : PolyTime matrixEntry := by unfold matrixEntry;infer_instance
instance poly_matrixTabulate {f : (α×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode ea natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime r.matrixTabulate := by unfold Realizes.matrixTabulate;apply poly_then
instance poly_identityEntry : PolyTime identityEntry := by unfold identityEntry;infer_instance
instance poly_identityMatrix : PolyTime identityMatrix := by unfold identityMatrix;apply poly_then
instance poly_transposeMatrix : PolyTime transposeMatrix := by unfold transposeMatrix;apply poly_then
instance poly_matrixMul : PolyTime matrixMul := by unfold matrixMul;apply poly_then
instance poly_fromBlocks : PolyTime fromBlocks := by unfold fromBlocks;apply poly_then
instance poly_tabulateFin {n : α → ℕ} {f : (Σ a,Fin (n a)) → β}
    (r : Realizes (finFamilyCode ea n) eb f) (rn : Realizes ea natCode n) [PolyTime r] [PolyTime rn] :
    PolyTime (r.tabulateFin rn) := by unfold Realizes.tabulateFin;infer_instance
instance poly_familyFirst {n : α → ℕ} : PolyTime (familyFirst (ea:=ea) (n:=n)) := by unfold familyFirst;apply poly_reindex
instance poly_familyIndex {n : α → ℕ} : PolyTime (familyIndex (ea:=ea) (n:=n)) := by unfold familyIndex;apply poly_reindex

instance poly_pow {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] (k : ℕ) : PolyTime (r.pow k) := by
  induction k with
  | zero => unfold Realizes.pow;infer_instance
  | succ k ih => unfold Realizes.pow;infer_instance
instance poly_min {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.min s) := by unfold Realizes.min;infer_instance
instance poly_max {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.max s) := by unfold Realizes.max;infer_instance
instance poly_inv {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] : PolyTime r.inv := by unfold Realizes.inv;infer_instance
instance poly_lt {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.lt s) := by unfold Realizes.lt;infer_instance
instance poly_eq {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.eq s) := by unfold Realizes.eq;infer_instance

instance poly_better (ea : α → Word) : PolyTime (better ea) := by unfold better;infer_instance
lemma fold_select_code (f : α×α → α) (h : ∀a b,f (a,b)=a ∨ f (a,b)=b)
    (s : α) (xs : List α) (L : ℕ) (hs : (ea s).length≤L) (hx : ∀x∈xs,(ea x).length≤L) :
    (ea (xs.foldl (fun a b => f (a,b)) s)).length≤L := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih =>
    apply ih
    · dsimp only
      rcases h s x with e|e <;> rw [e]
      · exact hs
      · exact hx x (by simp)
    · intro y hy;exact hx y (by simp [hy])
lemma size_selection {f : α×α → α} (r : Realizes (prodCode ea ea) ea f)
    (h : ∀a b,f (a,b)=a ∨ f (a,b)=b) : FoldSize r := by
  refine ⟨⟨X,?_⟩⟩
  intro s xs ys zs he
  apply fold_select_code f h s ys _ (le_prodCode_left (s,xs))
  intro x hx
  exact (mem_length_le_code ys hx).trans ((prefix_code_length ea xs ys zs he).trans (le_prodCode_right (s,xs)))
instance size_better (ea : α → Word) : FoldSize (better ea) :=
  size_selection _ (fun _ _ => by unfold betterData;split_ifs <;> simp)
instance poly_selectScored (ea : α → Word) : PolyTime (selectScored ea) := by unfold selectScored;infer_instance
instance poly_chooseCoordinate : PolyTime chooseCoordinate := by unfold chooseCoordinate;infer_instance

end CurrentKS.Realization

end OAI
