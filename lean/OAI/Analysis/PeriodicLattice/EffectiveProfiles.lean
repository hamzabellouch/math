import OAI.Analysis.PeriodicLattice.EffectiveDerivatives

namespace OAI

/-! Effective smooth profiles, stack codes and planar compilation. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingEffectiveProfiles {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace EffectiveProfiles
open CertifiedReal RecursiveArithmetic ProfileJets
local instance effectiveProfilesLocal1 : Primcodable ℚ := ratPrimcodable

theorem rho : Effective (fun q : ℚ => expNegInvGlue (q : ℝ)) := by
  have h := (rational (q := fun q : ℚ => -q⁻¹) (by fun_prop)).exp
  exact ((constant 0).ite h (ratLE.comp Primrec.id (Primrec.const 0))).congr
    (fun q => by simp [expNegInvGlue])

theorem rhoTerm (k : ℕ) : Effective (fun q : ℚ => ProfileJets.rhoTerm k (q : ℝ)) := by
  have h := (rational (q := fun q : ℚ => q⁻¹^k) (by fun_prop)).mul rho
  exact h.congr (fun q => by simp [ProfileJets.rhoTerm])

theorem denomInv (k : ℕ) : Effective (fun q : ℚ => ProfileJets.denomInv k (q : ℝ)) := by
  have h := rho.add (rho.comp (g := fun q : ℚ => 1-q) (by fun_prop))
  have h' := h.inv (fun q => by
    simpa only [Rat.cast_sub,Rat.cast_one] using (Real.smoothTransition.pos_denom (q : ℝ)).ne')
  exact (h'.pow (Computable.const k)).congr (fun q => by simp [ProfileJets.denomInv])

theorem factor (f : Factor) : Effective (fun q : ℚ => evalFactor f (q : ℝ)) := by
  have ha : Computable (fun q : ℚ => (f.2.1 : ℚ)*q+f.2.2.1) := by fun_prop
  cases hf : f.1
  · exact ((rhoTerm f.2.2.2).comp ha).congr (fun q => by simp [evalFactor,hf])
  · exact ((denomInv f.2.2.2).comp ha).congr (fun q => by simp [evalFactor,hf])

theorem product (l : List Factor) : Effective (fun q : ℚ => evalProduct l (q : ℝ)) := by
  induction l with
  | nil => simpa [evalProduct] using constant (A := ℚ) 1
  | cons f l ih => exact ((factor f).mul ih).congr (fun q => (evalProduct_cons _ _ _).symm)

theorem expression (e : Expr) : Effective (fun q : ℚ => eval e (q : ℝ)) := by
  induction e with
  | nil => simpa [eval] using constant (A := ℚ) 0
  | cons f l ih =>
    have h := ((constant (A := ℚ) (f.1 : ℚ)).mul (product f.2)).add ih
    exact h.congr (fun q => by simp [eval_cons,evalTerm])

theorem pulse : Effective (fun q : ℚ => deriv Profiles.clock (q : ℝ)) := by
  simpa only [jet_correct, eval_clockExpr, iteratedDeriv_one] using expression (jet clockExpr 1)

theorem bump : Effective (fun q : ℚ => Profiles.bump (q : ℝ)) := by
  simpa only [eval_bumpExpr] using expression bumpExpr
end EffectiveProfiles

namespace RecursiveArithmetic
@[fun_prop] theorem intToNat : Primrec Int.toNat := by
  exact (Primrec.ite intNegative (Primrec.const 0) intNatAbs).of_eq (fun z => by
    cases z <;> simp)
@[fun_prop] theorem int_mod : Primrec (fun p : ℤ × ℤ => p.1 % p.2) := by
  exact (intSub.comp Primrec.fst (intMul.comp Primrec.snd int_div)).of_eq
    (fun p => (Int.emod_def p.1 p.2).symm)
@[fun_prop] theorem finVal {n : ℕ} : Primrec (fun i : Fin n => i.val) := Primrec.fin_val
@[fun_prop] theorem machineLookup : Primrec (fun p : Machine × ℕ × ℕ => p.1.lookup p.2.1 p.2.2) := by
  exact (Primrec.list_getD none).comp
    ((Primrec.list_getD []).comp (machineTable.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)
@[fun_prop] theorem optionNone {A : Type*} [Primcodable A] : Primrec (Option.isNone : Option A → Bool) := by
  exact (Primrec.option_casesOn Primrec.id (Primrec.const true) (Primrec.const false).to₂).of_eq (fun o => by cases o <;> rfl)
end RecursiveArithmetic

namespace StackCode
open RecursiveArithmetic

def Code.equiv : Code ≃ ℕ × ℕ × ℕ where
  toFun c := (c.left,c.right,c.state)
  invFun p := ⟨p.1,p.2.1,p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance : Primcodable Code := Primcodable.ofEquiv _ Code.equiv
@[fun_prop] theorem codeLeft : Primrec Code.left := Primrec.fst.comp (Primrec.of_equiv (e := Code.equiv))
@[fun_prop] theorem codeRight : Primrec Code.right := (Primrec.fst.comp Primrec.snd).comp (Primrec.of_equiv (e := Code.equiv))
@[fun_prop] theorem codeState : Primrec Code.state := (Primrec.snd.comp Primrec.snd).comp (Primrec.of_equiv (e := Code.equiv))
@[fun_prop] theorem codeMk : Primrec (fun p : ℕ × ℕ × ℕ => Code.mk p.1 p.2.1 p.2.2) := Primrec.of_equiv_symm (e := Code.equiv)
@[fun_prop] theorem pack_recursive : Primrec (fun p : ℕ × ℕ × Code => pack p.1 p.2.1 p.2.2) := by
  unfold pack; fun_prop
@[fun_prop] theorem unpack_recursive : Primrec (fun p : ℕ × ℕ × ℤ => unpack p.1 p.2.1 p.2.2) := by
  have hr : Primrec (fun p : ℕ × ℕ × ℤ => residue p.1 p.2.1 p.2.2) := by
    unfold residue; fun_prop
  have hu : Primrec (fun p : ℕ × ℕ × ℕ => unpackNat p.1 p.2.1 p.2.2) := by
    exact codeMk.comp (g := fun p : ℕ × ℕ × ℕ => (p.2.2 % p.1^p.2.1, p.2.2 / p.1^p.2.1 % p.1^p.2.1, p.2.2 / p.1^p.2.1 / p.1^p.2.1)) (by fun_prop)
  exact hu.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair hr))
@[fun_prop] theorem stepRight_recursive : Primrec (fun p : ℕ × Code × Instruction =>
    (p.2.2.writeSymbol + p.1*p.2.1.left, p.2.1.right / p.1, p.2.2.nextState)) := by
  have hl := codeLeft.comp (Primrec.fst.comp (Primrec.snd : Primrec (Prod.snd : ℕ × Code × Instruction → Code × Instruction)))
  have hr := codeRight.comp (Primrec.fst.comp (Primrec.snd : Primrec (Prod.snd : ℕ × Code × Instruction → Code × Instruction)))
  have hw := instructionSymbol.comp (Primrec.snd.comp (Primrec.snd : Primrec (Prod.snd : ℕ × Code × Instruction → Code × Instruction)))
  have hs := instructionState.comp (Primrec.snd.comp (Primrec.snd : Primrec (Prod.snd : ℕ × Code × Instruction → Code × Instruction)))
  exact ((Primrec.nat_add.comp hw (Primrec.nat_mul.comp Primrec.fst hl)).pair
    ((Primrec.nat_div.comp hr Primrec.fst).pair hs)).of_eq (fun _ => rfl)
@[fun_prop] theorem stepLeft_recursive : Primrec (fun p : ℕ × Code × Instruction =>
    (p.2.1.left / p.1, p.2.1.left % p.1 + p.1*p.2.2.writeSymbol + p.1*(p.2.1.right-p.2.1.right % p.1), p.2.2.nextState)) := by
  have hl := codeLeft.comp (Primrec.fst.comp (Primrec.snd : Primrec (Prod.snd : ℕ × Code × Instruction → Code × Instruction)))
  have hr := codeRight.comp (Primrec.fst.comp (Primrec.snd : Primrec (Prod.snd : ℕ × Code × Instruction → Code × Instruction)))
  have hw := instructionSymbol.comp (Primrec.snd.comp (Primrec.snd : Primrec (Prod.snd : ℕ × Code × Instruction → Code × Instruction)))
  have hs := instructionState.comp (Primrec.snd.comp (Primrec.snd : Primrec (Prod.snd : ℕ × Code × Instruction → Code × Instruction)))
  exact ((Primrec.nat_div.comp hl Primrec.fst).pair
    ((Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_mod.comp hl Primrec.fst)
      (Primrec.nat_mul.comp Primrec.fst hw))
      (Primrec.nat_mul.comp Primrec.fst (Primrec.nat_sub.comp hr (Primrec.nat_mod.comp hr Primrec.fst)))).pair hs)).of_eq (fun _ => rfl)
@[fun_prop] theorem stepStay_recursive : Primrec (fun p : ℕ × Code × Instruction =>
    (p.2.1.left, p.2.1.right-p.2.1.right % p.1+p.2.2.writeSymbol, p.2.2.nextState)) := by
  have hl := codeLeft.comp (Primrec.fst.comp (Primrec.snd : Primrec (Prod.snd : ℕ × Code × Instruction → Code × Instruction)))
  have hr := codeRight.comp (Primrec.fst.comp (Primrec.snd : Primrec (Prod.snd : ℕ × Code × Instruction → Code × Instruction)))
  have hw := instructionSymbol.comp (Primrec.snd.comp (Primrec.snd : Primrec (Prod.snd : ℕ × Code × Instruction → Code × Instruction)))
  have hs := instructionState.comp (Primrec.snd.comp (Primrec.snd : Primrec (Prod.snd : ℕ × Code × Instruction → Code × Instruction)))
  exact (hl.pair ((Primrec.nat_add.comp
    (Primrec.nat_sub.comp hr (Primrec.nat_mod.comp hr Primrec.fst)) hw).pair hs)).of_eq (fun _ => rfl)
@[fun_prop] theorem step_recursive : Primrec (fun p : ℕ × Code × Instruction => step p.1 p.2.1 p.2.2) := by
  have hm := Primrec.fin_val.comp (instructionMove.comp (Primrec.snd.comp (Primrec.snd : Primrec (Prod.snd : ℕ × Code × Instruction → Code × Instruction))))
  exact (Primrec.ite (Primrec.eq.comp hm (Primrec.const 2)) (codeMk.comp stepRight_recursive)
    (Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) (codeMk.comp stepLeft_recursive) (codeMk.comp stepStay_recursive))).of_eq (fun p => rfl)
end StackCode

namespace CompilerPlanar
open RecursiveArithmetic
@[fun_prop] theorem width_recursive : Primrec (fun p : Input × ℕ => Scales.width p.1.word.length p.2) := by
  have hL := Primrec.list_length.comp (inputWord.comp (Primrec.fst : Primrec (Prod.fst : Input × ℕ → Input)))
  exact (Primrec.nat_add.comp (Primrec.nat_add.comp hL (Primrec.const 1))
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)).of_eq (fun _ => rfl)
@[fun_prop] theorem decode_recursive : Primrec (fun p : Input × ℕ × ℤ =>
    StackCode.unpack (radix p.1) (Scales.width p.1.word.length p.2.1) p.2.2) := by
  have hw := width_recursive.comp ((Primrec.fst : Primrec (Prod.fst : Input × ℕ × ℤ → Input)).pair (Primrec.fst.comp Primrec.snd))
  exact (StackCode.unpack_recursive.comp ((radix_primrec.comp Primrec.fst).pair (hw.pair (Primrec.snd.comp Primrec.snd)))).of_eq (fun _ => rfl)
@[fun_prop] theorem lookupAddress_recursive : Primrec (fun p : Input × ℕ × ℤ =>
    p.1.machine.lookup (StackCode.Code.state (StackCode.unpack (radix p.1) (Scales.width p.1.word.length p.2.1) p.2.2))
      ((StackCode.Code.right (StackCode.unpack (radix p.1) (Scales.width p.1.word.length p.2.1) p.2.2)) % radix p.1)) := by
  have hM := inputMachine.comp (Primrec.fst : Primrec (Prod.fst : Input × ℕ × ℤ → Input))
  have hs := StackCode.codeState.comp decode_recursive
  have hr := Primrec.nat_mod.comp (StackCode.codeRight.comp decode_recursive) (radix_primrec.comp Primrec.fst)
  exact (machineLookup.comp (hM.pair (hs.pair hr))).of_eq (fun _ => rfl)
@[fun_prop] theorem haltTable_recursive : Primrec (fun p : Input × ℕ × ℤ => haltTable p.1 p.2.1 p.2.2) := by
  exact (optionNone.comp lookupAddress_recursive).of_eq (fun p => rfl)
@[fun_prop] theorem nextArgs_recursive : Primrec (fun p : (Input × ℕ × ℤ) × Instruction =>
    (radix p.1.1, Scales.width p.1.1.word.length (p.1.2.1+1),
      StackCode.step (radix p.1.1) (StackCode.unpack (radix p.1.1) (Scales.width p.1.1.word.length p.1.2.1) p.1.2.2) p.2)) := by
  have hr := radix_primrec.comp (Primrec.fst.comp (Primrec.fst : Primrec (Prod.fst : (Input × ℕ × ℤ) × Instruction → Input × ℕ × ℤ)))
  have hw := width_recursive.comp ((Primrec.fst.comp (Primrec.fst : Primrec (Prod.fst : (Input × ℕ × ℤ) × Instruction → Input × ℕ × ℤ))).pair
    (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const 1)))
  have hs := StackCode.step_recursive.comp (hr.pair ((decode_recursive.comp Primrec.fst).pair Primrec.snd))
  exact (hr.pair (hw.pair hs)).of_eq (fun _ => rfl)
@[fun_prop] theorem nextTable_recursive : Primrec (fun p : Input × ℕ × ℤ => nextTable p.1 p.2.1 p.2.2) := by
  exact (Primrec.option_casesOn lookupAddress_recursive (Primrec.const 0)
    (StackCode.pack_recursive.comp nextArgs_recursive).to₂).of_eq (fun p => by
      dsimp only
      unfold nextTable RuleTable.next
      dsimp only
      cases p.1.machine.lookup (StackCode.unpack (radix p.1) (Scales.width p.1.word.length p.2.1) p.2.2).state
        ((StackCode.unpack (radix p.1) (Scales.width p.1.word.length p.2.1) p.2.2).right % radix p.1) <;> rfl)
end CompilerPlanar
namespace EffectiveFields
open CertifiedReal Quantitative RapidCalculus TorusCalculus RecursiveArithmetic CompilerPlanar
open scoped ContDiff
local instance effectiveProfilesLocal2 : Primcodable ℚ := ratPrimcodable
local instance effectiveProfilesLocal3 : DecidablePred Input.WellFormed := Classical.decPred _
local instance effectiveProfilesLocal4 : Primcodable ValidInput := Primcodable.subtype RecursiveArithmetic.inputWellFormed

@[fun_prop] theorem rat_natFloor : Primrec (fun q : ℚ => ⌊q⌋₊) :=
  (intToNat.comp rat_floor).of_eq (fun q => Int.floor_toNat q)

def qepsilon (d : Input) (n : ℕ) : ℚ := ((radix d : ℚ)^Scales.exponent d.word.length n)⁻¹
def qbeta (d : Input) (n : ℕ) : ℚ := if n=0 then 1/4 else qepsilon d n
@[simp] theorem cast_qepsilon (d : Input) (n : ℕ) :
    (qepsilon d n : ℝ) = Scales.epsilon (radix d) d.word.length n := by simp [qepsilon,Scales.epsilon]
@[simp] theorem cast_qbeta (d : Input) (n : ℕ) :
    (qbeta d n : ℝ) = Scales.beta (radix d) d.word.length n := by simp [qbeta,Scales.beta]; split_ifs <;> simp
@[fun_prop] theorem qepsilon_recursive : Primrec (fun p : Input × ℕ => qepsilon p.1 p.2) := by
  have hb := ratNat.comp (radix_primrec.comp (Primrec.fst : Primrec (Prod.fst : Input × ℕ → Input)))
  have he := Scales.exponent_primrec.comp ((listLength.comp (inputWord.comp (Primrec.fst : Primrec (Prod.fst : Input × ℕ → Input)))).pair Primrec.snd)
  exact (ratInv.comp (rat_pow.comp (hb.pair he))).of_eq (fun _ => rfl)
@[fun_prop] theorem qbeta_recursive : Primrec (fun p : Input × ℕ => qbeta p.1 p.2) := by
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const (1/4)) qepsilon_recursive

theorem selector_effective {A : Type*} [Primcodable A] {e : A → ℚ} {c : A × ℤ → ℚ}
    (he : Computable e) (hc : Computable c) :
    Effective (fun p : A × ℚ => Profiles.selector (e p.1) (fun j => (c (p.1,j):ℝ)) p.2) := by
  let z : A × ℚ → ℚ := fun p => (p.2-1/2)/(e p.1)
  have hz : Computable z := by
    have hs := rat_sub.to_comp.comp ((Computable.snd : Computable (Prod.snd : A × ℚ → ℚ)).pair (Computable.const (1/2 : ℚ)))
    exact (rat_div.to_comp.comp (hs.pair (he.comp Computable.fst))).of_eq (fun _ => rfl)
  let j : A × ℚ → ℤ := fun p => ⌊z p+1/2⌋
  have hj : Computable j := by
    exact (rat_floor.to_comp.comp (rat_add.to_comp.comp (hz.pair (Computable.const (1/2 : ℚ))))).of_eq (fun _ => rfl)
  have hcoeff := rational (hc.comp (Computable.fst.pair hj))
  have hb : Computable (fun p : A × ℚ => z p - j p) := by
    exact (rat_sub.to_comp.comp (hz.pair (ratInt.to_comp.comp hj))).of_eq (fun _ => rfl)
  exact (hcoeff.mul (EffectiveProfiles.bump.comp hb)).congr (fun p => by
    have hl : (j p : ℝ) ≤ (z p : ℝ)+1/2 := by
      dsimp only [j]
      simpa using (Rat.cast_le (K:=ℝ)).mpr (Int.floor_le (z p+1/2))
    have hu : (z p : ℝ)+1/2 < (j p : ℝ)+1 := by
      dsimp only [j]
      simpa using (Rat.cast_lt (K:=ℝ)).mpr (Int.lt_floor_add_one (z p+1/2))
    have hnear : |((p.2:ℝ)-1/2)/(e p.1) - (j p:ℝ)| < 5/8 := by
      have hzcast : (z p : ℝ) = ((p.2:ℝ)-1/2)/(e p.1) := by simp [z]
      rw [← hzcast]; apply abs_lt.mpr; constructor <;> linarith
    rw [Profiles.selector_single _ hnear]
    simp [Profiles.latticeBump,z])

abbrev SlotPoint := Input × ℕ × ℚ
private theorem slotIndex_recursive : Primrec (fun p : SlotPoint => (p.1,p.2.1)) :=
  Primrec.fst.pair (Primrec.fst.comp Primrec.snd)
private theorem slotNext_recursive : Primrec (fun p : SlotPoint => (p.1,p.2.1+1)) :=
  (Primrec.fst.pair (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))).of_eq (fun _ => rfl)
private theorem slotPrev_recursive : Primrec (fun p : SlotPoint => (p.1,p.2.1-1,p.2.2)) :=
  Primrec.fst.pair ((Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)).pair
    (Primrec.snd.comp Primrec.snd))

theorem halt_selector : Effective (fun p : SlotPoint => Profiles.selector
    (Scales.epsilon (radix p.1) p.1.word.length p.2.1)
    (fun j => if haltTable p.1 p.2.1 j then 1 else 0) p.2.2) := by
  have hc : Computable (fun p : (Input × ℕ) × ℤ => (if haltTable p.1.1 p.1.2 p.2 then 1 else 0 : ℚ)) := by
    have ha : Primrec (fun p : (Input × ℕ) × ℤ => (p.1.1,p.1.2,p.2)) :=
      (Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
    exact ((Primrec.cond (haltTable_recursive.comp ha) (Primrec.const (1 : ℚ)) (Primrec.const (0 : ℚ))).of_eq (fun _ => Bool.cond_eq_ite _ _ _)).to_comp
  have h := selector_effective qepsilon_recursive.to_comp hc
  exact (h.comp (g := fun p : SlotPoint => ((p.1,p.2.1),p.2.2)) (by fun_prop)).congr (fun p => by
    simp only [cast_qepsilon]
    congr 1
    funext j
    split_ifs <;> norm_num)

theorem next_selector : Effective (fun p : SlotPoint => Profiles.selector
    (Scales.epsilon (radix p.1) p.1.word.length p.2.1)
    (fun j => (nextTable p.1 p.2.1 j : ℝ)) p.2.2) := by
  have hc : Computable (fun p : (Input × ℕ) × ℤ => (nextTable p.1.1 p.1.2 p.2 : ℚ)) := by
    have ha : Primrec (fun p : (Input × ℕ) × ℤ => (p.1.1,p.1.2,p.2)) :=
      (Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
    exact ((ratNat.comp (nextTable_recursive.comp ha)).of_eq (fun _ => rfl)).to_comp
  have h := selector_effective qepsilon_recursive.to_comp hc
  exact (h.comp (g := fun p : SlotPoint => ((p.1,p.2.1),p.2.2)) (by fun_prop)).congr (fun p => by simp)

theorem coeff_a : Effective (fun p : SlotPoint => (Planar.coefficients (radix p.1) p.1.word.length (loadingCode p.1)
    (fun n j => nextTable p.1 n j) (fun n j => if haltTable p.1 n j then 1 else 0) p.2.1 p.2.2).1) := by
  have hb0 := rational (q := fun p : SlotPoint => qbeta p.1 p.2.1) ((qbeta_recursive.comp slotIndex_recursive).to_comp)
  have hb1 := rational (q := fun p : SlotPoint => qbeta p.1 (p.2.1+1)) ((qbeta_recursive.comp slotNext_recursive).to_comp)
  have hslot := (hb0.sub hb1).add (((constant 2).mul hb1).mul halt_selector)
  have h := (constant 0).ite (hslot.comp (g := fun p : SlotPoint => (p.1,p.2.1-1,p.2.2)) slotPrev_recursive.to_comp)
    (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
  exact h.congr (fun p => by cases hn : p.2.1 <;> simp [Planar.coefficients,Planar.slot])

theorem coeff_b : Effective (fun p : SlotPoint => (Planar.coefficients (radix p.1) p.1.word.length (loadingCode p.1)
    (fun n j => nextTable p.1 n j) (fun n j => if haltTable p.1 n j then 1 else 0) p.2.1 p.2.2).2) := by
  have hload := (rational ((qepsilon_recursive.comp (Primrec.fst.pair (Primrec.const 0) : Primrec (fun p : SlotPoint => (p.1,0)))).to_comp)).mul
    (rational ((ratNat.comp (loadingCode_primrec.comp (Primrec.fst : Primrec (Prod.fst : SlotPoint → Input)))).to_comp))
  have he := rational (q := fun p : SlotPoint => qepsilon p.1 (p.2.1+1)) (qepsilon_recursive.comp slotNext_recursive).to_comp
  have hslot := he.mul next_selector
  have h := hload.ite (hslot.comp (g := fun p : SlotPoint => (p.1,p.2.1-1,p.2.2)) slotPrev_recursive.to_comp)
    (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
  exact h.congr (fun p => by cases hn : p.2.1 <;> simp [Planar.coefficients,Planar.slot])

private theorem slot_value (d : Input) (p : BiPoint) :
    FluidLift.v d (time p.1) p.2 = Profiles.pulse ⌊max p.1 0⌋₊ (time p.1) •
      Planar.coefficients (radix d) d.word.length (loadingCode d)
        (fun n j => nextTable d n j) (fun n j => if haltTable d n j then 1 else 0) ⌊max p.1 0⌋₊ p.2 := by
  apply Profiles.schedule_on_slot
  · dsimp only [time]; exact_mod_cast Nat.floor_le (le_max_right p.1 0)
  · dsimp only [time]; exact_mod_cast (Nat.lt_floor_add_one (max p.1 0)).le

private theorem pointSlot_recursive : Computable (fun p : ValidInput × BiPoint => (p.1.1,⌊max p.2.1 0⌋₊,p.2.2)) := by
  have ht := ratMax.comp ((Primrec.fst.comp (Primrec.snd : Primrec (Prod.snd : ValidInput × BiPoint → BiPoint))).pair (Primrec.const 0))
  exact ((validData_recursive.comp Primrec.fst).pair ((rat_natFloor.comp ht).pair (Primrec.snd.comp Primrec.snd))).to_comp
private theorem pointPulse_recursive : Computable (fun p : ValidInput × BiPoint => max p.2.1 0 - (⌊max p.2.1 0⌋₊:ℚ)) := by
  have ht := ratMax.comp ((Primrec.fst.comp (Primrec.snd : Primrec (Prod.snd : ValidInput × BiPoint → BiPoint))).pair (Primrec.const 0))
  exact ((rat_sub.comp (ht.pair (ratNat.comp (rat_natFloor.comp ht)))).of_eq (fun _ => rfl)).to_comp

theorem a_base : Effective (fun p : ValidInput × BiPoint => biValue (FluidLift.a p.1.1) p.2) := by
  have ha := pointSlot_recursive
  have ht := pointPulse_recursive
  exact ((EffectiveProfiles.pulse.comp ht).mul (coeff_a.comp ha)).congr (fun p => by
    dsimp only [biValue,FluidLift.a]
    rw [slot_value p.1.1 p.2]
    simp only [Prod.smul_fst,smul_eq_mul,Profiles.pulse,time]; push_cast; rfl)

theorem b_base : Effective (fun p : ValidInput × BiPoint => biValue (FluidLift.b p.1.1) p.2) := by
  have ha := pointSlot_recursive
  have ht := pointPulse_recursive
  exact ((EffectiveProfiles.pulse.comp ht).mul (coeff_b.comp ha)).congr (fun p => by
    dsimp only [biValue,FluidLift.b]
    rw [slot_value p.1.1 p.2]
    simp only [Prod.smul_snd,smul_eq_mul,Profiles.pulse,time]; push_cast; rfl)
end EffectiveFields

end
end PeriodicLattice

end OAI
