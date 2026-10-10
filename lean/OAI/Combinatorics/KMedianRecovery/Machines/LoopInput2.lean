import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.GetRow2

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList
lemma dimension_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : n≤(encode A).length := by
  rw [encode]
  simpa only [List.length_ofFn] using length_le_encode (List.ofFn (fun i=>rowEncode (A i)))
lemma entry_length_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (BinaryRational.encode (A i j)).length≤(encode A).length := by
  have hr := length_member_le_encode (List.mem_ofFn.mpr ⟨i,rfl⟩ : rowEncode (A i)∈List.ofFn (fun i=>rowEncode (A i)))
  have he := length_member_le_encode (List.mem_ofFn.mpr ⟨j,rfl⟩ : BinaryRational.encode (A i j)∈List.ofFn (fun j=>BinaryRational.encode (A i j)))
  rw [←rowEncode_eq] at he
  exact he.trans hr
lemma input_height {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    RationalHeight.Height (A i j) (encode A).length :=
  (BinaryRational.input_height (A i j)).mono (entry_length_bound A i j)
lemma encode_height {n b : ℕ} (F : Matrix (Fin n) (Fin n) ℚ)
    (hF : ∀ i j,RationalHeight.Height (F i j) b) :
    (encode F).length≤n*(2*(n*(6*b+14))+2) := by
  have hr (i : Fin n) : (rowEncode (F i)).length≤n*(6*b+14) := by
    rw [rowEncode_eq]
    have hh := encode_le_bound (List.ofFn (fun j=>BinaryRational.encode (F i j))) (3*b+6) (by
      intro w hw
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
      exact BinaryRational.encode_height (hF i j))
    simp only [List.length_ofFn] at hh
    convert hh using 1; ring
  have hh := encode_le_bound (List.ofFn (fun i=>rowEncode (F i))) (n*(6*b+14)) (by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact hr i)
  rw [encode]
  simpa only [List.length_ofFn] using hh

lemma iterate_length_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) {t : ℕ} (ht : t≤n) :
    (encode (MetricKMedianRecovery.BirdRationalIteration.iterate A t)).length≤80*((encode A).length+1)^6 := by
  let L := (encode A).length
  let P := L+1
  have hn : n≤L := dimension_bound A
  have hp : 1≤P := by omega
  have hp₂ : 1≤P^2 := one_le_pow₀ hp
  have hp₂₄ : P^2≤P^4 := Nat.pow_le_pow_right hp (by omega)
  have hn₂ : 2*n*n+1≤3*P^2 := by dsimp [P]; nlinarith
  have hb : (t+1)*((2*n*n+1)*L)+t*(n+1)≤4*P^4 := by
    have h₁ : (t+1)*((2*n*n+1)*L)≤P*((3*P^2)*P) := by
      gcongr <;> omega
    have h₂ : t*(n+1)≤P*P := by gcongr <;> omega
    nlinarith
  have hh := encode_height (MetricKMedianRecovery.BirdRationalIteration.iterate A t)
    (MetricKMedianRecovery.BirdRationalIteration.iterate_height A (input_height A) t)
  have hp₁₆ : P≤P^6 := by simpa using Nat.pow_le_pow_right hp (show 1≤6 by omega)
  have hp₂₆ : P^2≤P^6 := Nat.pow_le_pow_right hp (by omega)
  calc
    _ ≤ n*(2*(n*(6*((t+1)*((2*n*n+1)*L)+t*(n+1))+14))+2) := hh
    _ ≤ P*(2*(P*(6*(4*P^4)+14))+2) := by gcongr <;> omega
    _ ≤ 80*(L+1)^6 := by change _≤80*P^6; nlinarith

def loopInput (x : List Bool) : List Bool := pairBits (extractPrefix x,discardPrefix (discardPrefix x))
noncomputable def loopInput_computes : PolyComputes loopInput :=
  extractPrefix_computes.pair (discardPrefix_computes.comp discardPrefix_computes)
noncomputable def loopOp (x : List Bool) : List Bool := stepWords (loopInput x)
noncomputable def loopOp_computes : PolyComputes loopOp := by
  unfold loopOp
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=loopInput) (g:=stepWords) loopInput_computes stepWords_computes)
lemma loopOp_encode {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℚ) (w : List Bool) :
    Fold.operation loopOp (encode A) (encode F) w=encode (BirdDet.Spec.stepEntry A F) := by
  simp only [Fold.operation,loopOp,loopInput,extractPrefix_pairBits,
    discardPrefix_pairBits,stepWords_encode]
lemma fold_steps {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℚ) (ws : List (List Bool)) :
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
  (Fold.run loopOp (200*(Polynomial.X+1)^6)) ∘ iterationInput
noncomputable def iterateWords_computes : PolyComputes iterateWords :=
  iterationInput_computes.comp (Fold.run_computes loopOp_computes (200*(Polynomial.X+1)^6))
lemma iterateWords_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    iterateWords (encode A)=encode (MetricKMedianRecovery.BirdRationalIteration.iterate A (n-1)) := by
  let ws := List.ofFn (fun i=>rowEncode (A i))
  have hws : WordList.encode ws=encode A := rfl
  have hlen : ws.length=n := List.length_ofFn
  simp only [iterateWords,Function.comp_apply,iterationInput,←hws,tail_encode]
  rw [Fold.run_encode loopOp (200*(Polynomial.X+1)^6) (WordList.encode ws)
    (WordList.encode ws) ws.tail (80*((encode A).length+1)^6)]
  · rw [hws,fold_steps,←MetricKMedianRecovery.BirdRationalIteration.iterate,List.length_tail,hlen]
  · intro j
    rw [hws,fold_steps,←MetricKMedianRecovery.BirdRationalIteration.iterate]
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
    have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hS 1) 6
    have hlin : L+1≤(L+1)^6 := by simpa using Nat.pow_le_pow_right hq (show 1≤6 by omega)
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    change 2*(WordList.encode ws.tail).length+2*(WordList.encode ws).length+80*(L+1)^6+2≤_
    change (WordList.encode ws.tail).length≤L at ht
    rw [hws] at hp
    rw [hws]
    change 2*(WordList.encode ws.tail).length+2*L+80*(L+1)^6+2≤_
    nlinarith

noncomputable def rawDet : List Bool → List Bool := WordList.head ∘ WordList.head ∘ iterateWords
noncomputable def rawDet_computes : PolyComputes rawDet :=
  (iterateWords_computes.comp WordList.head_computes).comp WordList.head_computes
lemma rawDet_encode {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    rawDet (encode A)=BinaryRational.encode (MetricKMedianRecovery.BirdRationalIteration.iterate A n 0 0) := by
  simp only [rawDet,Function.comp_apply]
  rw [iterateWords_encode,Nat.add_sub_cancel,encode,head_ofFn,rowEncode_eq,head_ofFn]

noncomputable def signOp : List Bool → List Bool :=
  BinaryRational.negWords ∘ discardPrefix ∘ discardPrefix
noncomputable def signOp_computes : PolyComputes signOp :=
  (discardPrefix_computes.comp discardPrefix_computes).comp BinaryRational.negWords_computes
lemma sign_fold (ws : List (List Bool)) (z : ℚ) :
    ws.foldl (Fold.operation signOp []) (BinaryRational.encode z)=BinaryRational.encode ((-1)^ws.length*z) := by
  induction ws generalizing z with
  | nil => simp only [List.foldl_nil,List.length_nil,pow_zero,one_mul]
  | cons w ws ih =>
    have hs : Fold.operation signOp [] (BinaryRational.encode z) w=BinaryRational.encode (-z) := by
      simp only [Fold.operation,signOp,Function.comp_apply,discardPrefix_pairBits,BinaryRational.negWords_encode]
    rw [List.foldl_cons,hs,ih,List.length_cons,pow_succ]
    congr 1
    ring

noncomputable def signRun : List Bool → List Bool := Fold.run signOp (4*Polynomial.X+4)
noncomputable def signRun_computes : PolyComputes signRun := Fold.run_computes signOp_computes (4*Polynomial.X+4)
lemma signRun_encode (ws : List (List Bool)) (z : ℚ) :
    signRun (Fold.pack (WordList.encode ws) [] (BinaryRational.encode z))=BinaryRational.encode ((-1)^ws.length*z) := by
  unfold signRun
  rw [Fold.run_encode signOp (4*Polynomial.X+4) [] (BinaryRational.encode z) ws (BinaryRational.encode z).length]
  · exact sign_fold ws z
  · intro n
    rw [sign_fold]
    have he : ((-1:ℚ)^((ws.take n).length)*z).num.natAbs=z.num.natAbs ∧
        ((-1:ℚ)^((ws.take n).length)*z).den=z.den := by
      rcases neg_one_pow_eq_or ℚ ((ws.take n).length) with h|h
      · simp only [h,one_mul,and_self]
      · simp only [h,neg_one_mul,Rat.num_neg_eq_neg_num,Int.natAbs_neg,Rat.den_neg_eq_den,and_self]
    simp only [BinaryRational.encode_length,he.1,he.2,Nat.le_refl]
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
noncomputable def determinantInput (x : List Bool) : List Bool := Fold.pack (WordList.tail x) [] (rawDet x)
noncomputable def determinantInput_computes : PolyComputes determinantInput :=
  Fold.pack_computes WordList.tail_computes (const_computes []) rawDet_computes
noncomputable def signedDet : List Bool → List Bool := signRun ∘ determinantInput
noncomputable def signedDet_computes : PolyComputes signedDet := determinantInput_computes.comp signRun_computes
noncomputable def determinantWords (x : List Bool) : List Bool :=
  if x=[] then BinaryRational.encode 1 else signedDet x
noncomputable def determinantWords_computes : PolyComputes determinantWords := by
  have hh := isEmpty_computes.cond (const_computes (BinaryRational.encode 1)) signedDet_computes
  unfold determinantWords
  simpa only [decide_eq_true_eq] using hh
lemma determinantWords_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    determinantWords (encode A)=BinaryRational.encode A.det := by
  rw [←MetricKMedianRecovery.BirdRationalIteration.determinant_eq]
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
    (encode : Matrix (Fin n) (Fin n) ℚ → List Bool) BinaryRational.encode Matrix.det :=
  determinantWords_computes.reencode _ _ determinantWords_encode
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
