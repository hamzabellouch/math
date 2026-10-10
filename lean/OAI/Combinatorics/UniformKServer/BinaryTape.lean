import Mathlib
import OAI.Combinatorics.UniformKServer.RawProgram

namespace OAI

noncomputable section
                                 
section

namespace UniformKServer.BinaryTape
open RawBinary

 theorem value_sum {b : ℕ} (v : Fin b→Bool) :
    value (List.ofFn v)=∑i : Fin b,(if v i then 1 else 0)*2^i.val := by
  induction b with
  | zero=>simp [value]
  | succ b ih=>
    rw [List.ofFn_succ,RawBinary.value_cons,Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ]
    rw [ih]
    simp_rw [←Nat.mul_assoc,←Finset.sum_mul]
    cases v 0 <;> simp only [Nat.bit_val,Bool.toNat_false,Bool.toNat_true,
      Bool.false_eq_true,ite_false,ite_true] <;> omega

 theorem bits_value {b : ℕ} (v : Fin b→Bool) :
    (BitSampling.bitsEquiv b v).val=value (List.ofFn v) := by
  rw [value_sum]
  simp only [BitSampling.bitsEquiv,Equiv.trans_apply,finPiFinEquiv_apply,
    finCongr_apply,Fin.val_cast,Equiv.piCongrRight_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  cases h:v i <;> simp [finTwoEquiv,h]

 theorem value_pad (b : ℕ) (w : List Bool) :
    value (List.ofFn (fun i : Fin b=>w.getD i.val false))=value (w.take b) := by
  induction b generalizing w with
  | zero=>rfl
  | succ b ih=>
    cases w with
    | nil=>
      simp only [List.getD_nil,List.take_nil,List.ofFn_succ,RawBinary.value_cons]
      have hh:=ih []
      simp only [List.getD_nil,List.take_nil] at hh
      rw [hh]
      rfl
    | cons a w=>
      simp only [List.ofFn_succ,Fin.val_zero,List.getD_cons_zero,Fin.val_succ,List.getD_cons_succ,
        List.take_succ_cons,RawBinary.value_cons]
      rw [ih]

 def coins (k M b a : ℕ) : TapeController.Tape k M b :=
  fun i j=>(a.bits.drop (b*i.val)).getD j.val false

 theorem fresh_eq (k M b a : ℕ) :
    RawProgram.fresh k M b a=RawTape.tape (coins k M b a) := by
  unfold RawProgram.fresh
  rw [RawMetric.horizon_eq,RawExpansion.range_eq_ofFn]
  simp only [List.map_ofFn,RawTape.tape]
  apply List.ofFn_inj.mpr
  funext i
  rw [bits_value]
  change value ((a.bits.drop (b*i.val)).take b)=
    value (List.ofFn (fun j : Fin b=>(a.bits.drop (b*i.val)).getD j.val false))
  exact (value_pad b _).symm

 def word {H b : ℕ} (v : Fin H→Fin b→Bool) : List Bool :=
  (List.ofFn fun i=>List.ofFn (v i)).flatten
 def token {H b : ℕ} (v : Fin H→Fin b→Bool) : ℕ := value (word v++[true])
 @[simp] theorem word_length {H b : ℕ} (v : Fin H→Fin b→Bool) : (word v).length=H*b := by
  simp [word,List.length_flatten,List.sum_ofFn,Finset.sum_const,smul_eq_mul]

 theorem word_ofFn {H b : ℕ} (v : Fin H→Fin b→Bool) :
    word v=List.ofFn (fun z : Fin (H*b)=>v (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) := by
  rw [List.ofFn_mul]
  unfold word
  congr 1
  apply List.ofFn_inj.mpr
  funext i
  apply List.ofFn_inj.mpr
  funext j
  have h : (⟨i.val*b+j.val,by nlinarith [i.isLt,j.isLt]⟩ : Fin (H*b))=finProdFinEquiv (i,j) := by
    apply Fin.ext;simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  simp only [h,Equiv.symm_apply_apply]

 theorem slice_word {H b : ℕ} (v : Fin H→Fin b→Bool) (i : Fin H) :
    (((word v)++[true]).drop (b*i.val)).take b=List.ofFn (v i) := by
  rw [word_ofFn]
  have hbound : b*i.val+b≤H*b := by nlinarith [i.isLt]
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_append,List.length_ofFn,List.length_singleton]
    omega
  · intro j h₁ h₂
    have hj : j<b := by simpa only [List.length_ofFn] using h₂
    have hidx : b*i.val+j<H*b := by nlinarith [i.isLt]
    simp only [List.getElem_take,List.getElem_drop]
    rw [List.getElem_append_left (by simpa only [List.length_ofFn] using hidx),List.getElem_ofFn]
    have hh : (⟨b*i.val+j,hidx⟩ : Fin (H*b))=finProdFinEquiv (i,⟨j,hj⟩) := by
      apply Fin.ext;simp [finProdFinEquiv,Nat.add_comm]
    rw [hh,Equiv.symm_apply_apply]
    simp only [List.getElem_ofFn]

 theorem fresh_token {k M b : ℕ} (v : TapeController.Tape k M b) :
    RawProgram.fresh k M b (token v)=RawTape.tape v := by
  unfold RawProgram.fresh token
  rw [RawBits.bits_value,RawMetric.horizon_eq,RawExpansion.range_eq_ofFn]
  simp only [List.map_ofFn,RawTape.tape]
  apply List.ofFn_inj.mpr
  funext i
  change value (((word v++[true]).drop (b*i.val)).take b)=(BitSampling.bitsEquiv b (v i)).val
  rw [slice_word,bits_value]

end UniformKServer.BinaryTape

end


end

end OAI
