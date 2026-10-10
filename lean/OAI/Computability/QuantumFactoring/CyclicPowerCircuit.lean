import Mathlib
import OAI.Computability.QuantumFactoring.ModularPower
import OAI.Computability.QuantumFactoring.CyclicConstants

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality

abbrev cyclicPowerWidth (s w b : ℕ) := ((s*w+w)+b)+s*w

def cyclicPack {s w b : ℕ} (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) : Basis (cyclicPowerWidth s w b) :=
  Fin.append (Fin.append (Fin.append a m) e) z

def cyclicBase (s w b : ℕ) : BooleanNetwork (cyclicPowerWidth s w b) (s*w) :=
  select (fun i => ((i.castAdd w).castAdd b).castAdd (s*w))
def cyclicMod (s w b : ℕ) : BooleanNetwork (cyclicPowerWidth s w b) w :=
  select (fun i => ((Fin.natAdd (s*w) i).castAdd b).castAdd (s*w))
def cyclicAcc (s w b : ℕ) : BooleanNetwork (cyclicPowerWidth s w b) (s*w) :=
  select (Fin.natAdd ((s*w+w)+b))
def cyclicBit (s w : ℕ) {b : ℕ} (i : Fin b) : BooleanNetwork (cyclicPowerWidth s w b) 1 :=
  bit ((Fin.natAdd (s*w+w) i).castAdd (s*w))

@[simp] lemma cyclicBase_eval {s w b : ℕ} (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) : (cyclicBase s w b).eval (cyclicPack a m e z)=a := by
  funext i
  simp only [cyclicBase,eval_select,Function.comp_apply,cyclicPack,Fin.append_left]
@[simp] lemma cyclicMod_eval {s w b : ℕ} (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) : (cyclicMod s w b).eval (cyclicPack a m e z)=m := by
  funext i
  simp only [cyclicMod,eval_select,Function.comp_apply,cyclicPack,Fin.append_left,Fin.append_right]
@[simp] lemma cyclicAcc_eval {s w b : ℕ} (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) : (cyclicAcc s w b).eval (cyclicPack a m e z)=z := by
  funext i
  simp only [cyclicAcc,eval_select,Function.comp_apply,cyclicPack,Fin.append_right]
@[simp] lemma cyclicBit_eval {s w b : ℕ} (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) (i : Fin b) : (cyclicBit s w i).eval (cyclicPack a m e z) 0=e i := by
  simp only [cyclicBit,eval_bit,cyclicPack,Fin.append_left,Fin.append_right]

def cyclicNew (s w : ℕ) [NeZero s] {b : ℕ} (i : Fin b) :
    BooleanNetwork (cyclicPowerWidth s w b) (s*w) :=
  let sq := cyclicMulNet (cyclicAcc s w b) (cyclicAcc s w b) (cyclicMod s w b)
  wordMux (cyclicBit s w i) (cyclicMulNet sq (cyclicBase s w b) (cyclicMod s w b)) sq

def cyclicStep (s w : ℕ) [NeZero s] {b : ℕ} (i : Fin b) :
    BooleanNetwork (cyclicPowerWidth s w b) (cyclicPowerWidth s w b) :=
  (select (Fin.castAdd (s*w))).pair (cyclicNew s w i)

lemma cyclicStep_pack {s w b : ℕ} [NeZero s] (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) (i : Fin b) :
    (cyclicStep s w i).eval (cyclicPack a m e z)=
      cyclicPack a m e ((cyclicNew s w i).eval (cyclicPack a m e z)) := by
  simp only [cyclicStep,eval_pair,eval_select,cyclicPack]
  congr 1
  funext j
  exact Fin.append_left _ _ j

lemma cyclicNew_value {s w b : ℕ} [NeZero s] (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) (i : Fin b) (hm : 0 < (bitsValue m).toNat) :
    decodeCyclic (bitsValue m).toNat ((cyclicNew s w i).eval (cyclicPack a m e z)) =
      if e i then decodeCyclic (bitsValue m).toNat z ^ 2 * decodeCyclic (bitsValue m).toNat a
        else decodeCyclic (bitsValue m).toNat z ^ 2 := by
  have hm' : 0 < (bitsValue ((cyclicMod s w b).eval (cyclicPack a m e z))).toNat := by
    simpa only [cyclicMod_eval] using hm
  have hs := cyclicMulNet_correct (cyclicAcc s w b) (cyclicAcc s w b)
    (cyclicMod s w b) (cyclicPack a m e z) hm'
  have hp := cyclicMulNet_correct
    (cyclicMulNet (cyclicAcc s w b) (cyclicAcc s w b) (cyclicMod s w b))
    (cyclicBase s w b) (cyclicMod s w b) (cyclicPack a m e z) hm'
  rw [cyclicMod_eval] at hs hp
  simp only [cyclicAcc_eval,cyclicBase_eval] at hs hp
  rw [cyclicNew,wordMux_eval,cyclicBit_eval]
  split
  · rw [hp,hs,pow_two]
  · rw [hs,pow_two]

lemma cyclicNew_canonical {s w b : ℕ} [NeZero s] (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z : Basis (s*w)) (i : Fin b) (hm : 0 < (bitsValue m).toNat) :
    CanonicalCyclic (bitsValue m).toNat ((cyclicNew s w i).eval (cyclicPack a m e z)) := by
  have hm' : 0 < (bitsValue ((cyclicMod s w b).eval (cyclicPack a m e z))).toNat := by
    simpa only [cyclicMod_eval] using hm
  rw [cyclicNew,wordMux_eval,cyclicBit_eval]
  split <;>
    simpa only [cyclicMod_eval] using (cyclicMulNet_canonical _ _ _ _ hm')

lemma cyclicMulBound_mono {s w a b c a' b' c' : ℕ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    cyclicMulBound s w a b c ≤ cyclicMulBound s w a' b' c' := by
  dsimp [cyclicMulBound]
  gcongr

abbrev cyclicStepBound (s w : ℕ) :=
  cyclicMulBound s w (cyclicMulBound s w 0 0 0) 0 0 + cyclicMulBound s w 0 0 0+7*(s*w)

lemma cyclicNew_count (s w : ℕ) [NeZero s] {b : ℕ} (i : Fin b) :
    (cyclicNew s w i).net.count ≤ cyclicStepBound s w := by
  let sq := cyclicMulNet (cyclicAcc s w b) (cyclicAcc s w b) (cyclicMod s w b)
  have hs : sq.net.count ≤ cyclicMulBound s w 0 0 0 := cyclicMulNet_count _ _ _
  have hh : (cyclicMulNet sq (cyclicBase s w b) (cyclicMod s w b)).net.count ≤
      cyclicMulBound s w (cyclicMulBound s w 0 0 0) 0 0 :=
    (cyclicMulNet_count sq (cyclicBase s w b) (cyclicMod s w b)).trans
      (cyclicMulBound_mono hs (by rfl) (by rfl))
  simp only [cyclicNew,wordMux_count,cyclicBit,count_bit,zero_add]
  change (cyclicMulNet sq (cyclicBase s w b) (cyclicMod s w b)).net.count +
    sq.net.count + 7*(s*w) ≤ cyclicStepBound s w
  dsimp [cyclicStepBound]
  omega

lemma cyclicStep_count (s w : ℕ) [NeZero s] {b : ℕ} (i : Fin b) :
    (cyclicStep s w i).net.count ≤ cyclicStepBound s w := by
  simpa only [cyclicStep,count_pair,count_select,zero_add] using cyclicNew_count s w i

def cyclicPrefix (s w b : ℕ) [NeZero s] : (k : ℕ) → k ≤ b →
    BooleanNetwork (cyclicPowerWidth s w b) (cyclicPowerWidth s w b)
  | 0,_ => select id
  | k+1,h => (cyclicPrefix s w b k (by omega)).comp (cyclicStep s w ⟨k,by omega⟩)

lemma cyclicPrefix_count (s w b k : ℕ) [NeZero s] (hk : k ≤ b) :
    (cyclicPrefix s w b k hk).net.count ≤ k*cyclicStepBound s w := by
  induction k with
  | zero => simp [cyclicPrefix]
  | succ k ih =>
    have h := cyclicStep_count s w (⟨k,by omega⟩ : Fin b)
    have hi := ih (by omega)
    simp only [cyclicPrefix,count_comp]
    nlinarith

lemma cyclicPrefix_value {s w b : ℕ} [NeZero s] (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (z₀ : Basis (s*w)) (hm : 0 < (bitsValue m).toNat)
    (h₀ : decodeCyclic (bitsValue m).toNat z₀=1) (hc : CanonicalCyclic (bitsValue m).toNat z₀)
    (k : ℕ) (hk : k ≤ b) :
    ∃ z : Basis (s*w), (cyclicPrefix s w b k hk).eval (cyclicPack a m e z₀)=cyclicPack a m e z ∧
      decodeCyclic (bitsValue m).toNat z=decodeCyclic (bitsValue m).toNat a ^horner e k hk ∧
      CanonicalCyclic (bitsValue m).toNat z := by
  induction k with
  | zero => exact ⟨z₀,by simp [cyclicPrefix],by simpa only [horner,pow_zero] using h₀,hc⟩
  | succ k ih =>
    obtain ⟨z,hz,hv,_hzc⟩ := ih (by omega)
    refine ⟨(cyclicNew s w ⟨k,by omega⟩).eval (cyclicPack a m e z),?_,?_,
      cyclicNew_canonical _ _ _ _ _ hm⟩
    · rw [cyclicPrefix,eval_comp,hz,cyclicStep_pack]
    · rw [cyclicNew_value _ _ _ _ _ hm,hv]
      cases he : e (⟨k,by omega⟩ : Fin b)
      · simp only [horner,he,Bool.false_eq_true,ite_false,Bool.toNat_false,Nat.add_zero]
        rw [← pow_mul,Nat.mul_comm (horner e k _) 2]
      · simp only [horner,he,ite_true,Bool.toNat_true]
        rw [← pow_mul,pow_succ,Nat.mul_comm (horner e k _) 2]

/-- n-bit repeated squaring in the coefficient array; no exponential polynomial
or algebraic root is part of the computation. -/
def cyclicPower (s w b : ℕ) [NeZero s] : BooleanNetwork ((s*w+w)+b) (s*w) :=
  ((select id).pair (cyclicOne s w)).comp
    ((cyclicPrefix s w b b le_rfl).rewire (Fin.natAdd ((s*w+w)+b)))

lemma cyclicPower_count (s w b : ℕ) [NeZero s] :
    (cyclicPower s w b).net.count ≤ s*w*w+b*cyclicStepBound s w := by
  have h₁ := arrayConstant_count (n := (s*w+w)+b) (s := s) (w := w) (fun i => if i=0 then 1 else 0)
  have h₂ := cyclicPrefix_count s w b b le_rfl
  simp only [cyclicPower,count_comp,count_pair,count_select,count_rewire,zero_add]
  change (arrayConstant s w _).net.count + _ ≤ _
  omega

lemma cyclicPower_value {s w b : ℕ} [NeZero s] (a : Basis (s*w)) (m : Basis w) (e : Basis b)
    (hw : 0 < w) (hm : 2 ≤ (bitsValue m).toNat) :
    decodeCyclic (bitsValue m).toNat ((cyclicPower s w b).eval (Fin.append (Fin.append a m) e))=
      decodeCyclic (bitsValue m).toNat a ^ horner e b le_rfl ∧
    CanonicalCyclic (bitsValue m).toNat ((cyclicPower s w b).eval (Fin.append (Fin.append a m) e)) := by
  let input := Fin.append (Fin.append a m) e
  obtain ⟨z,hz,hv,hc⟩ := cyclicPrefix_value a m e ((cyclicOne s w).eval input)
    (by omega) (cyclicOne_value hw input) (cyclicOne_canonical hm input) b le_rfl
  have he : (cyclicPower s w b).eval input=z := by
    simp only [cyclicPower,eval_comp,eval_rewire,eval_pair,eval_select,Function.comp_id]
    change ((cyclicPrefix s w b b le_rfl).eval
      (cyclicPack a m e ((cyclicOne s w).eval input))) ∘ Fin.natAdd ((s*w+w)+b)=z
    rw [hz]
    funext i
    exact Fin.append_right _ _ i
  change decodeCyclic (bitsValue m).toNat ((cyclicPower s w b).eval input)=_ ∧
    CanonicalCyclic (bitsValue m).toNat ((cyclicPower s w b).eval input)
  rw [he]
  exact ⟨hv,hc⟩

end ExactQuantumFactoring.BitArithmetic


end

end OAI
