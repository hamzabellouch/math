import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialIterateFamilies
import OAI.Analysis.MatrixSigning.Complexity.PolynomialOptimize
import OAI.Combinatorics.ThinTrees.Normalization.Realization
import OAI.Combinatorics.ThinTrees.RationalMatrix.Gram
import OAI.Combinatorics.ThinTrees.RationalMatrix.MatrixRealization

namespace OAI

/-! Schur history. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
open AlgorithmicThinTrees

def SchurDesc (a b : MatrixObject) : Prop :=
  ∃k, ∃p : Fin k → Fin a.1, ∃r : Fin b.1 → Fin a.1,
    KS.W07.PivotTrace a.2 p r b.2

lemma SchurDesc.refl (a : MatrixObject) : SchurDesc a a :=
  ⟨0,(fun i => Fin.elim0 i),id,KS.W07.PivotTrace.initial⟩

lemma SchurDesc.dim {a b : MatrixObject} (h : SchurDesc a b) : b.1≤a.1 := by
  obtain ⟨k,p,r,h⟩ := h
  have hh := h.size_bound
  omega

lemma SchurDesc.psd {a b : MatrixObject} (h : SchurDesc a b)
    (hA : (a.2.map (fun q : ℚ => (q:ℝ))).PosSemidef) :
    (b.2.map (fun q : ℚ => (q:ℝ))).PosSemidef := by
  obtain ⟨k,p,r,h⟩ := h
  exact h.state_posSemidef hA

lemma SchurDesc.schur {a b : MatrixObject} (h : SchurDesc a b)
    (hA : (a.2.map (fun q : ℚ => (q:ℝ))).PosSemidef) : SchurDesc a (schurData b) := by
  rcases b with ⟨d,B⟩
  cases d with
  | zero => exact h
  | succ d =>
    obtain ⟨k,p,r,h⟩ := h
    by_cases hz : B 0 0=0
    · exact ⟨k,p,(fun i => r i.succ),h.zero hz⟩
    · have hh := (h.state_posSemidef hA).diag_nonneg (i:=0)
      change (0 : ℝ) ≤ (B 0 0:ℝ) at hh
      have hq : 0 ≤ B 0 0 := by exact_mod_cast hh
      exact ⟨k+1,Fin.snoc p (r 0),(fun i => r i.succ),h.positive (lt_of_le_of_ne hq (Ne.symm hz))⟩

lemma SchurDesc.wire {a b : MatrixObject} (h : SchurDesc a b) :
    (matrixObjectCode b).length ≤
      2*a.1+1+a.1*(2*(a.1*(2*(4*KS.W30.inverseBitBound a.1 (matrixObjectCode a).length+7)+1))+1) := by
  have hn := h.dim
  obtain ⟨k,p,r,h⟩ := h
  exact matrixObject_parts_bound b hn (RationalGram.trace_parts h (matrixObject_parts a))

abbrev SchurStack := MatrixObject×List MatrixObject
abbrev schurStackCode := prodCode matrixObjectCode (listCode matrixObjectCode)

def schurNextData (s : SchurStack) : SchurStack :=
  if s.1.1=0 then s else (schurData s.1,s.1::s.2)

abbrev schurCurrent := first matrixObjectCode (listCode matrixObjectCode)
abbrev schurOld := second matrixObjectCode (listCode matrixObjectCode)

def schurNext : Realizes schurStackCode schurStackCode schurNextData :=
  let z := ((schurCurrent.then matrixDim).both (constant schurStackCode natCode 0)).then natEq
  (z.ite (identity schurStackCode)
    ((schurCurrent.then schur).both ((schurCurrent.both schurOld).then (consList matrixObjectCode)))).congr
    (fun s => by simp only [schurNextData]; split_ifs <;> simp_all)
instance poly_schurNext : PolyTime schurNext := by unfold schurNext; infer_instance

def schurHistoryData : MatrixObject → List MatrixObject
  | ⟨0,_⟩ => []
  | ⟨d+1,A⟩ => schurHistoryData ⟨d,KS.W17.schurTail A⟩ ++ [⟨d+1,A⟩]
termination_by a => a.1

lemma schurHistory_length (a : MatrixObject) : (schurHistoryData a).length=a.1 := by
  rcases a with ⟨d,A⟩
  induction d with
  | zero => simp [schurHistoryData]
  | succ d ih => simp [schurHistoryData,ih]

lemma schurHistory_iterate (a : MatrixObject) (xs : List MatrixObject) :
    ((schurNextData^[a.1]) (a,xs)).2=schurHistoryData a++xs := by
  rcases a with ⟨d,A⟩
  induction d generalizing xs with
  | zero => simp [schurHistoryData]
  | succ d ih =>
    rw [Function.iterate_succ_apply]
    change ((schurNextData^[d]) (⟨d,KS.W17.schurTail A⟩,⟨d+1,A⟩::xs)).2=_
    rw [ih]
    simp only [schurHistoryData,List.append_assoc,List.singleton_append]

def schurHistory : Realizes matrixObjectCode (listCode matrixObjectCode) schurHistoryData :=
  (((matrixDim.both ((identity matrixObjectCode).both
    (constant matrixObjectCode (listCode matrixObjectCode) []))).then schurNext.iterate).then
      schurOld).congr (fun a => by simpa only [List.append_nil,id_eq] using schurHistory_iterate a [])

lemma schurNext_invariant (a : MatrixObject)
    (hA : (a.2.map (fun q : ℚ => (q:ℝ))).PosSemidef) (j : ℕ) :
    let s := schurNextData^[j] (a,[])
    SchurDesc a s.1 ∧ (∀b∈s.2,SchurDesc a b) ∧ s.2.length≤j := by
  induction j with
  | zero => exact ⟨SchurDesc.refl a,by simp,by simp⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    dsimp only
    dsimp only at ih
    generalize he : schurNextData^[j] (a,[])=s at ih ⊢
    unfold schurNextData
    split_ifs with hz
    · exact ⟨ih.1,ih.2.1,by omega⟩
    · refine ⟨ih.1.schur hA,?_,?_⟩
      · simpa only [List.mem_cons,forall_eq_or_imp] using And.intro ih.1 ih.2.1
      · simp only [List.length_cons];omega

lemma schurHistory_mem (a : MatrixObject)
    (hA : (a.2.map (fun q : ℚ => (q:ℝ))).PosSemidef) :
    ∀b∈schurHistoryData a, SchurDesc a b := by
  have h := (schurNext_invariant a hA a.1).2.1
  simpa only [schurHistory_iterate,List.append_nil] using h

lemma runsPoly_schurHistory {ι : Type*} {L : ι → ℕ} (a : ι → MatrixObject)
    (ha : IsPoly L (fun i => (matrixObjectCode (a i)).length))
    (hA : ∀i, ((a i).2.map (fun q : ℚ => (q:ℝ))).PosSemidef) :
    RunsPoly L schurHistory a := by
  let dim := fun i => (a i).1
  let bits := fun i => (matrixObjectCode (a i)).length
  have hd : IsPoly L dim := ha.mono (fun i => matrixObject_dim_le (a i))
  have hi : IsPoly L (fun i => KS.W30.inverseBitBound (dim i) (bits i)) := by
    apply (((isPoly_const L 6).mul (ha.add (isPoly_const L 1))).mul
      ((hd.add (isPoly_const L 1)).pow 3)).mono
    exact fun i => KS.W30.inverseBitBound_le_polynomial _ _
  have hb := (((isPoly_const L 2).mul hd).add (isPoly_const L 1)).add
    (hd.mul (((isPoly_const L 2).mul (hd.mul (((isPoly_const L 2).mul
      (((isPoly_const L 4).mul hi).add (isPoly_const L 7))).add (isPoly_const L 1)))).add (isPoly_const L 1)))
  obtain ⟨p,hp⟩ := hb
  have hs : IsPoly (fun s : {s : ι×ℕ // s.2<(a s.1).1} => L s.val.1)
      (fun s => (schurStackCode (schurNextData^[s.val.2] (a s.val.1,[]))).length) := by
    have hpoly := (((isPoly_const L 2).mul (show IsPoly L (fun i => p.eval (L i)) from ⟨p,fun _ => le_rfl⟩)).add (isPoly_const L 1)).add
      (hd.mul (((isPoly_const L 2).mul (show IsPoly L (fun i => p.eval (L i)) from ⟨p,fun _ => le_rfl⟩)).add (isPoly_const L 1)))
    apply (hpoly.reindex (fun s : {s : ι×ℕ // s.2<(a s.1).1} => s.val.1)).mono
    intro s
    obtain ⟨hc,ho,hl⟩ := schurNext_invariant (a s.val.1) (hA s.val.1) s.val.2
    have hb : ∀b, SchurDesc (a s.val.1) b → (matrixObjectCode b).length≤p.eval (L s.val.1) :=
      fun b h => h.wire.trans (hp s.val.1)
    have hcur := hb _ hc
    have hlist := listCode_length_bound _ (p.eval (L s.val.1)) (fun b h => hb b (ho b h))
    have hlen : (schurNextData^[s.val.2] (a s.val.1,[])).2.length≤dim s.val.1 :=
      hl.trans s.property.le
    have hlist' := hlist.trans (Nat.mul_le_mul_right _ hlen)
    dsimp only [dim] at hlist'
    simp only [schurStackCode,prodCode_length]
    dsimp only [Function.comp_apply,dim]
    omega
  unfold schurHistory
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  apply runsPoly_iterate _ _ hw
  obtain ⟨q,hq⟩ := (RunsPoly.of_poly schurNext _ hs).cost
  exact ⟨q,fun i j hj => hq ⟨(i,j),hj⟩⟩

end CurrentKS.Realization
end

end OAI
