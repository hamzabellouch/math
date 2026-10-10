import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialExplicit
import OAI.Analysis.MatrixSigning.Complexity.PolynomialMatrixFold
import OAI.Analysis.MatrixSigning.Realization.FaceQueryRealization
import OAI.Combinatorics.ThinTrees.BasePacking

namespace OAI

/-! Matrix realization. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word}

lemma runsPoly_fold_of_poly {f : α×β → α}
    (r : Realizes (prodCode ea eb) ea f) [PolyTime r] (a : ι → α×List β)
    (ha : IsPoly L (fun i => (prodCode ea (listCode eb) (a i)).length))
    (hs : ∃q : NaturalPolynomial,∀i ys zs,(a i).2=ys++zs →
      (ea (ys.foldl (fun s x => f (s,x)) (a i).1)).length≤q.eval (L i)) :
    RunsPoly L r.fold a := by
  obtain ⟨p,hp⟩ := ha
  obtain ⟨q,hq⟩ := hs
  obtain ⟨t,ht⟩ := PolyTime.bound (r:=r)
  refine ⟨⟨p,hp⟩,⟨5*q+2*p+p*(3*p+10*q+t.comp (2*q+1+p)+12)+7,?_⟩⟩
  intro i
  let E := p.eval (L i)
  let S := q.eval (L i)
  have he : (listCode eb (a i).2).length≤E := (le_prodCode_right (a i)).trans (hp i)
  have hn := (list_length_le_code eb (a i).2).trans he
  have h0 := hq i [] (a i).2 rfl
  have hN := hq i (a i).2 [] (by simp)
  have hc : ∀s x,(ea s).length≤S → (eb x).length≤E → r.cost (s,x)≤t.eval (2*S+1+E) := by
    intro s x hs hx
    apply (ht (s,x)).trans (t.eval_mono ?_)
    rw [prodCode_length]
    dsimp only
    omega
  have hscan := fold_scan_bound (ea:=ea) (eb:=eb) (fun s x => f (s,x)) r.cost (a i).1
    (a i).2 S E (t.eval (2*S+1+E)) (hq i)
    (fun x hx => (mem_length_le_code (a i).2 hx).trans he) hc
  have hscan' := hscan.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  change FoldRoutine.ticks ea eb (fun s x => f (s,x)) r.cost (a i).1 (a i).2≤_
  simp only [FoldRoutine.ticks]
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,
    NaturalPolynomial.eval_comp]
  change _≤5*S+2*E+E*(3*E+10*S+t.eval (2*S+1+E)+12)+7
  change (ea (a i).1).length≤S at h0
  change (ea ((a i).2.foldl (fun s x => f (s,x)) (a i).1)).length≤S at hN
  change (FramedMapRoutine.tape eb (a i).2).length≤E at he
  omega

abbrev matrixView : Realizes matrixObjectCode (prodCode natCode matrixCode)
    (fun a => (a.1,matrixData a.2)) :=
  (identity (prodCode natCode matrixCode)).reindex matrixObjectCode
    (fun a => (a.1,matrixData a.2)) (fun _ => rfl)
private instance poly_matrixView : PolyTime matrixView := by
  unfold matrixView
  apply poly_reindex

abbrev matrixDim := matrixView.then (first natCode matrixCode)
abbrev matrixEntries := matrixView.then (second natCode matrixCode)

lemma matrix_entry_data {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℚ) (i : Fin n) (j : Fin m) :
    ((matrixData A).getD i.val []).getD j.val 0=A i j := by
  rw [show matrixData A=List.ofFn (fun i => List.ofFn (A i)) from rfl,
    getD_ofFn,getD_ofFn]

lemma matrixCode_parts_bound {n m b : ℕ} (A : Matrix (Fin n) (Fin m) ℚ)
    (h : ∀i j,QParts b (A i j)) :
    (matrixCode (matrixData A)).length≤n*(2*(m*(2*(4*b+7)+1))+1) := by
  apply (listCode_length_bound (matrixData A) (m*(2*(4*b+7)+1)) ?_).trans_eq
    (by rw [show (matrixData A).length=n from List.length_ofFn])
  intro row hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  apply (listCode_length_bound (List.ofFn (A i)) (4*b+7) ?_).trans_eq
    (by rw [List.length_ofFn])
  intro q hq
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
  exact (h i j).length

lemma matrixObject_dim_le (a : MatrixObject) : a.1≤(matrixObjectCode a).length :=
  by simpa only [prodCode, matrixObjectCode, natCode,List.length_replicate] using
    (le_prodCode_left (ea:=natCode) (eb:=matrixCode) (a.1,matrixData a.2))

lemma matrixObject_parts (a : MatrixObject) :
    ∀i j,QParts (matrixObjectCode a).length (a.2 i j) := by
  intro i j
  apply (qparts_length _).mono
  exact ((mem_length_le_code (List.ofFn (a.2 i)) (List.mem_ofFn.mpr ⟨j,rfl⟩)).trans
    (mem_length_le_code (matrixData a.2) (List.mem_ofFn.mpr ⟨i,rfl⟩))).trans
      (le_prodCode_right (a.1,matrixData a.2))

lemma matrixObject_parts_bound (a : MatrixObject) {b N : ℕ}
    (hn : a.1≤N) (h : ∀i j,QParts b (a.2 i j)) :
    (matrixObjectCode a).length≤2*N+1+N*(2*(N*(2*(4*b+7)+1))+1) := by
  have hb := matrixCode_parts_bound a.2 h
  have hm := Nat.mul_le_mul hn (Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (2*(4*b+7)+1) hn)) 1)
  simp only [matrixObjectCode,prodCode_length,natCode,List.length_replicate]
  change 2*a.1+1+(matrixCode (matrixData a.2)).length≤_
  omega

def schurData (a : MatrixObject) : MatrixObject :=
  match a with
  | ⟨0,A⟩ => ⟨0,A⟩
  | ⟨n+1,A⟩ => ⟨n,KS.W17.schurTail A⟩

abbrev entryCode := prodCode (prodCode matrixObjectCode natCode) natCode
abbrev entryBase := (first (prodCode matrixObjectCode natCode) natCode).then
  (first matrixObjectCode natCode)
abbrev entryI := (first (prodCode matrixObjectCode natCode) natCode).then
  (second matrixObjectCode natCode)
abbrev entryJ := second (prodCode matrixObjectCode natCode) natCode

def schurEntry : Realizes entryCode ratCode
    (fun p =>
      let A := matrixData p.1.1.2
      (A.getD (p.1.2+1) []).getD (p.2+1) 0 -
        (A.getD (p.1.2+1) []).getD 0 0 * (A.getD 0 []).getD (p.2+1) 0 /
          (A.getD 0 []).getD 0 0) :=
  let A := entryBase.then matrixEntries
  let i := entryI.then natSucc
  let j := entryJ.then natSucc
  let z := constant entryCode natCode 0
  let e {f g : (MatrixObject×ℕ)×ℕ → ℕ}
      (k : Realizes entryCode natCode f) (l : Realizes entryCode natCode g) :=
    (A.both (k.both l)).then matrixEntry
  (e i j).sub (((e i z).mul (e z j)).div (e z z))
instance poly_schurEntry : PolyTime schurEntry := by unfold schurEntry; apply poly_sub

def schur : Realizes matrixObjectCode matrixObjectCode schurData :=
  let d := matrixDim.then natPred
  let B := (((identity matrixObjectCode).both d).both d).then schurEntry.matrixTabulate
  (d.both B).changeOutput matrixObjectCode schurData (by
    intro a
    rcases a with ⟨n,A⟩
    cases n with
    | zero => simp [matrixObjectCode,schurData,matrixData]
    | succ n =>
      change prodCode natCode matrixCode (n,
        (List.range n).map (fun i => (List.range n).map (fun j => _)))=_
      simp only [range_map_fin, id_eq]
      have he : (List.ofFn fun (i : Fin n) => List.ofFn fun (j : Fin n) =>
          ((matrixData A).getD (i.val+1) []).getD (j.val+1) 0 -
            ((matrixData A).getD (i.val+1) []).getD 0 0 *
            ((matrixData A).getD 0 []).getD (j.val+1) 0 /
            ((matrixData A).getD 0 []).getD 0 0)=matrixData (KS.W17.schurTail A) := by
        change List.ofFn _=List.ofFn _
        apply congrArg List.ofFn
        funext i
        apply congrArg List.ofFn
        funext j
        change ((matrixData A).getD i.succ.val []).getD j.succ.val 0 -
          ((matrixData A).getD i.succ.val []).getD (0 : Fin (n+1)).val 0 *
          ((matrixData A).getD (0 : Fin (n+1)).val []).getD j.succ.val 0 /
          ((matrixData A).getD (0 : Fin (n+1)).val []).getD (0 : Fin (n+1)).val 0 = _
        rw [matrix_entry_data A i.succ j.succ,matrix_entry_data A i.succ 0,
          matrix_entry_data A 0 j.succ,matrix_entry_data A 0 0]
        rfl
      rw [he]
      rfl)
instance poly_schur : PolyTime schur := by unfold schur; apply poly_changeOutput

end CurrentKS.Realization
end

end OAI
