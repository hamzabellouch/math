import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Freeze
import OAI.Combinatorics.KMedianRecovery.Recovery.GetRow

namespace OAI

namespace MetricKMedianRecovery.BitMachine
attribute [local irreducible] WordList.mapWith WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run IntegerArray.sumWords IntegerArray.dotWords IntegerArray.dotListsWords
open WordOperations BinaryArithmetic
namespace WordList
lemma length_member_le_encode {ws : List (List Bool)} {w : List Bool} (hw : w∈ws) :
    w.length≤(encode ws).length := by
  induction ws with
  | nil => simp only [List.not_mem_nil] at hw
  | cons v vs ih =>
    simp only [List.mem_cons] at hw
    rw [encode,length_cons]
    rcases hw with rfl|hv
    · omega
    · have hh := ih hv
      omega
lemma tail_encode (ws : List (List Bool)) : tail (encode ws)=encode ws.tail := by
  cases ws with
  | nil => rfl
  | cons w ws => simp only [encode,tail_cons,List.tail_cons]
lemma head_ofFn {n : ℕ} (f : Fin (n+1) → List Bool) : head (encode (List.ofFn f))=f 0 := by
  rw [List.ofFn_succ]
  exact head_cons ..
end WordList
namespace IntegerMatrix
open WordList
lemma dimension_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : n≤(encode A).length := by
  rw [encode]
  simpa only [List.length_ofFn] using length_le_encode (List.ofFn (fun i=>rowEncode (A i)))
lemma entry_length_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    (Signed.encode (A i j)).length≤(encode A).length := by
  have hr := length_member_le_encode (List.mem_ofFn.mpr ⟨i,rfl⟩ : rowEncode (A i)∈List.ofFn (fun i=>rowEncode (A i)))
  have he := length_member_le_encode (List.mem_ofFn.mpr ⟨j,rfl⟩ : Signed.encode (A i j)∈List.ofFn (fun j=>Signed.encode (A i j)))
  rw [←rowEncode_eq] at he
  exact he.trans hr
lemma input_height {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    (A i j).natAbs≤2^(encode A).length := by
  have hl := entry_length_bound A i j
  rw [Signed.encode_length] at hl
  exact Nat.le_of_lt (Nat.size_le.mp (by omega : (A i j).natAbs.size≤(encode A).length))
lemma encode_height {n b : ℕ} (F : Matrix (Fin n) (Fin n) ℤ)
    (hF : ∀ i j,(F i j).natAbs≤2^b) :
    (encode F).length≤n*(2*(n*(2*b+6))+2) := by
  have he (i j : Fin n) : (Signed.encode (F i j)).length≤b+2 := by
    rw [Signed.encode_length]
    have hh := Nat.size_le_size (hF i j)
    rw [Nat.size_pow] at hh
    omega
  have hr (i : Fin n) : (rowEncode (F i)).length≤n*(2*b+6) := by
    rw [rowEncode_eq]
    have hh := encode_le_bound (List.ofFn (fun j=>Signed.encode (F i j))) (b+2) (by
      intro w hw
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
      exact he i j)
    simpa only [List.length_ofFn,Nat.mul_add,Nat.mul_succ,Nat.add_assoc] using hh
  have hh := encode_le_bound (List.ofFn (fun i=>rowEncode (F i))) (n*(2*b+6)) (by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact hr i)
  rw [encode]
  simpa only [List.length_ofFn] using hh

lemma iterate_length_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) {t : ℕ} (ht : t≤n) :
    (encode (MetricKMedianRecovery.BirdInteger.iterate A t)).length≤40*((encode A).length+1)^4 := by
  let L := (encode A).length
  have hn : n≤L := dimension_bound A
  have hh := encode_height (MetricKMedianRecovery.BirdInteger.iterate A t)
    (MetricKMedianRecovery.BirdInteger.iterate_height A (input_height A) t)
  have hb : (t+1)*L+t*(n+1)≤2*(L+1)^2 := by
    have h₁ := Nat.mul_le_mul (Nat.add_le_add_right (ht.trans hn) 1) (Nat.le_refl L)
    have h₂ := Nat.mul_le_mul (ht.trans hn) (Nat.add_le_add_right hn 1)
    nlinarith
  have hq : 1≤L+1 := by omega
  have h₁ : L+1≤(L+1)^4 := by simpa using Nat.pow_le_pow_right hq (show 1≤4 by omega)
  have h₂ : (L+1)^2≤(L+1)^4 := Nat.pow_le_pow_right hq (by omega)
  calc
    _ ≤ n*(2*(n*(2*((t+1)*L+t*(n+1))+6))+2) := hh
    _ ≤ (L+1)*(2*((L+1)*(2*(2*(L+1)^2)+6))+2) := by
      apply Nat.mul_le_mul (by omega)
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      apply Nat.mul_le_mul (by omega)
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hb) 6
    _ ≤ 40*(L+1)^4 := by nlinarith

def loopInput (x : List Bool) : List Bool := pairBits (extractPrefix x,discardPrefix (discardPrefix x))
noncomputable def loopInput_computes : PolyComputes loopInput :=
  extractPrefix_computes.pair (discardPrefix_computes.comp discardPrefix_computes)
noncomputable def loopOp (x : List Bool) : List Bool := stepWords (loopInput x)
noncomputable def loopOp_computes : PolyComputes loopOp := loopInput_computes.comp stepWords_computes
lemma loopOp_encode {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ) (w : List Bool) :
    Fold.operation loopOp (encode A) (encode F) w=encode (BirdDet.Spec.stepEntry A F) := by
  simp only [Fold.operation,loopOp,loopInput,extractPrefix_pairBits,
    discardPrefix_pairBits,stepWords_encode]
lemma fold_steps {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ) (ws : List (List Bool)) :
    ws.foldl (Fold.operation loopOp (encode A)) (encode F)=
      encode ((BirdDet.Spec.stepEntry A)^[ws.length] F) := by
  induction ws generalizing F with
  | nil => rfl
  | cons w ws ih =>
    rw [List.foldl_cons,loopOp_encode,ih,List.length_cons,Function.iterate_succ_apply]

noncomputable def iterationInput (x : List Bool) : List Bool := Fold.pack (WordList.tail x) x x
noncomputable def iterationInput_computes : PolyComputes iterationInput :=
  Fold.pack_computes WordList.tail_computes id_computes id_computes
noncomputable def iterateWords : List Bool → List Bool :=
  (Fold.run loopOp (100*(Polynomial.X+1)^4)) ∘ iterationInput
noncomputable def iterateWords_computes : PolyComputes iterateWords :=
  iterationInput_computes.comp (Fold.run_computes loopOp_computes (100*(Polynomial.X+1)^4))
lemma iterateWords_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    iterateWords (encode A)=encode (MetricKMedianRecovery.BirdInteger.iterate A (n-1)) := by
  let ws := List.ofFn (fun i=>rowEncode (A i))
  have hws : WordList.encode ws=encode A := rfl
  have hlen : ws.length=n := List.length_ofFn
  simp only [iterateWords,Function.comp_apply,iterationInput,←hws,tail_encode]
  rw [Fold.run_encode loopOp (100*(Polynomial.X+1)^4) (WordList.encode ws)
    (WordList.encode ws) ws.tail (40*((encode A).length+1)^4)]
  · rw [hws,fold_steps,←MetricKMedianRecovery.BirdInteger.iterate_eq,List.length_tail,hlen]
  · intro j
    rw [hws,fold_steps,←MetricKMedianRecovery.BirdInteger.iterate_eq]
    apply iterate_length_bound
    simp only [List.length_take,List.length_tail,hlen]
    omega
  · have ht := length_encode_drop ws 1
    rw [List.drop_one] at ht
    let L := (encode A).length
    have hS : L≤(Fold.pack (WordList.encode ws.tail) (WordList.encode ws) (WordList.encode ws)).length := by
      rw [Fold.length_pack,hws]
      omega
    have hq : 1≤L+1 := by omega
    have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hS 1) 4
    have hlin : L+1≤(L+1)^4 := by simpa using Nat.pow_le_pow_right hq (show 1≤4 by omega)
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    change 2*(WordList.encode ws.tail).length+2*(WordList.encode ws).length+40*(L+1)^4+2≤_
    change (WordList.encode ws.tail).length≤L at ht
    rw [hws] at hp
    rw [hws]
    change 2*(WordList.encode ws.tail).length+2*L+40*(L+1)^4+2≤_
    nlinarith

noncomputable def rawDet : List Bool → List Bool := WordList.head ∘ WordList.head ∘ iterateWords
noncomputable def rawDet_computes : PolyComputes rawDet :=
  (iterateWords_computes.comp WordList.head_computes).comp WordList.head_computes
lemma rawDet_encode {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℤ) :
    rawDet (encode A)=Signed.encode (MetricKMedianRecovery.BirdInteger.iterate A n 0 0) := by
  simp only [rawDet,Function.comp_apply]
  rw [iterateWords_encode,Nat.add_sub_cancel,encode,head_ofFn,rowEncode_eq,head_ofFn]

noncomputable def signOp : List Bool → List Bool :=
  (fun x=>Signed.encode (-Signed.decode x)) ∘ discardPrefix ∘ discardPrefix
noncomputable def signOp_computes : PolyComputes signOp :=
  (discardPrefix_computes.comp discardPrefix_computes).comp Signed.neg_computes
lemma sign_fold (ws : List (List Bool)) (z : ℤ) :
    ws.foldl (Fold.operation signOp []) (Signed.encode z)=Signed.encode ((-1)^ws.length*z) := by
  induction ws generalizing z with
  | nil => simp only [List.foldl_nil,List.length_nil,pow_zero,one_mul]
  | cons w ws ih =>
    have hs : Fold.operation signOp [] (Signed.encode z) w=Signed.encode (-z) := by
      simp only [Fold.operation,signOp,Function.comp_apply,discardPrefix_pairBits,Signed.encode_decode]
    rw [List.foldl_cons,hs,ih,List.length_cons,pow_succ]
    congr 1
    ring

noncomputable def signRun : List Bool → List Bool := Fold.run signOp (4*Polynomial.X+4)
noncomputable def signRun_computes : PolyComputes signRun := Fold.run_computes signOp_computes (4*Polynomial.X+4)
lemma signRun_encode (ws : List (List Bool)) (z : ℤ) :
    signRun (Fold.pack (WordList.encode ws) [] (Signed.encode z))=Signed.encode ((-1)^ws.length*z) := by
  unfold signRun
  rw [Fold.run_encode signOp (4*Polynomial.X+4) [] (Signed.encode z) ws (Signed.encode z).length]
  · exact sign_fold ws z
  · intro n
    rw [sign_fold,Signed.encode_length,Signed.encode_length,Int.natAbs_mul,Int.natAbs_pow,
      Int.natAbs_neg,Int.natAbs_one,one_pow,one_mul]
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
noncomputable def determinantInput (x : List Bool) : List Bool := Fold.pack (WordList.tail x) [] (rawDet x)
noncomputable def determinantInput_computes : PolyComputes determinantInput :=
  Fold.pack_computes WordList.tail_computes (const_computes []) rawDet_computes
noncomputable def signedDet : List Bool → List Bool := signRun ∘ determinantInput
noncomputable def signedDet_computes : PolyComputes signedDet := determinantInput_computes.comp signRun_computes
noncomputable def determinantWords (x : List Bool) : List Bool :=
  if x=[] then Signed.encode 1 else signedDet x
noncomputable def determinantWords_computes : PolyComputes determinantWords := by
  have hh := isEmpty_computes.cond (const_computes (Signed.encode 1)) signedDet_computes
  unfold determinantWords
  simpa only [decide_eq_true_eq] using hh
lemma determinantWords_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    determinantWords (encode A)=Signed.encode A.det := by
  rw [←MetricKMedianRecovery.BirdInteger.determinant_eq]
  cases n with
  | zero => rfl
  | succ n =>
    have hne : encode A≠[] := by
      have hh := dimension_bound A
      intro he
      rw [he,List.length_nil] at hh
      omega
    rw [determinantWords,ite_eq_right hne]
    simp only [signedDet,Function.comp_apply,determinantInput,rawDet_encode]
    rw [encode,tail_encode,signRun_encode,List.length_tail,List.length_ofFn,Nat.add_sub_cancel]
    rfl
noncomputable def determinant {n : ℕ} : Turing.TM2ComputableInPolyTime
    (encode : Matrix (Fin n) (Fin n) ℤ → List Bool) Signed.encode Matrix.det :=
  determinantWords_computes.reencode _ _ determinantWords_encode
end IntegerMatrix
end MetricKMedianRecovery.BitMachine

end OAI
