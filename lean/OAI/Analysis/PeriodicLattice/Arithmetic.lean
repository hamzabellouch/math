import OAI.Analysis.PeriodicLattice.ProfileJets

namespace OAI

/-! Recursive arithmetic and effective profile syntax. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingArithmetic {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace RecursiveArithmetic
open Encodable Primrec

theorem natPow : Primrec₂ (fun a b : ℕ => a ^ b) :=
  Primrec₂.unpaired'.mp Nat.Primrec.pow

theorem factorial : Primrec Nat.factorial := by
  have h := Primrec.nat_rec₁ (1 : ℕ)
    ((Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd).to₂)
  exact h.of_eq (fun n => by induction n <;> simp [Nat.factorial, *])

@[simp] theorem encode_int_ofNat (n : ℕ) : encode (n : ℤ) = 2 * n := rfl
@[simp] theorem encode_int_negSucc (n : ℕ) : encode (Int.negSucc n) = 2 * n + 1 := rfl

theorem intOfNat : Primrec (fun n : ℕ => (n : ℤ)) :=
  Primrec.encode_iff.mp (Primrec.nat_double.of_eq (fun _ => rfl))

theorem intNegSucc : Primrec Int.negSucc :=
  Primrec.encode_iff.mp (Primrec.nat_double_succ.of_eq (fun _ => rfl))

theorem intNatAbs : Primrec Int.natAbs := by
  have h := Primrec.cond (Primrec.nat_bodd.comp (Primrec.encode : Primrec (encode : ℤ → ℕ)))
    (Primrec.succ.comp (Primrec.nat_div2.comp Primrec.encode))
    (Primrec.nat_div2.comp Primrec.encode)
  exact h.of_eq (fun z => by cases z <;> simp [Nat.bodd, Nat.div2_val, show (2 : ℕ) ≠ 0 from by decide])

theorem intNegative : PrimrecPred (fun z : ℤ => z < 0) := by
  refine ⟨inferInstance, ?_⟩
  exact (Primrec.nat_bodd.comp Primrec.encode).of_eq (fun z => by
    cases z <;> simp [Nat.bodd])

theorem intAbsSign {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → ℤ} {g h : α → ℕ → β} (hf : Primrec f) (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec (fun a => if f a < 0 then h a (f a).natAbs else g a (f a).natAbs) :=
  Primrec.ite (intNegative.comp hf) (hh.comp Primrec.id (intNatAbs.comp hf))
    (hg.comp Primrec.id (intNatAbs.comp hf))

theorem intNeg : Primrec (fun z : ℤ => -z) := by
  have hc : Primrec (fun z : ℤ => if z < 0 then (z.natAbs : ℤ)
      else if z.natAbs = 0 then 0 else Int.negSucc (z.natAbs - 1)) :=
    Primrec.ite intNegative (intOfNat.comp intNatAbs)
      (Primrec.ite (Primrec.eq.comp intNatAbs (Primrec.const 0)) (Primrec.const 0)
        (intNegSucc.comp (Primrec.nat_sub.comp intNatAbs (Primrec.const 1))))
  exact hc.of_eq (fun z => by cases z <;> simp; split_ifs <;> omega)

theorem intSubNat : Primrec₂ (fun a b : ℕ => (a : ℤ) - b) := by
  have hc : Primrec (fun p : ℕ × ℕ => if p.2 ≤ p.1 then ((p.1 - p.2 : ℕ) : ℤ)
      else Int.negSucc (p.2 - p.1 - 1)) :=
    Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
      (intOfNat.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
      (intNegSucc.comp (Primrec.nat_sub.comp (Primrec.nat_sub.comp Primrec.snd Primrec.fst) (Primrec.const 1)))
  exact hc.of_eq (fun p => by dsimp only; split_ifs <;> omega)

theorem intAdd : Primrec₂ (fun a b : ℤ => a + b) := by
  have ap := Primrec.fst (α := ℤ) (β := ℤ)
  have bp := Primrec.snd (α := ℤ) (β := ℤ)
  have aa := intNatAbs.comp ap
  have ab := intNatAbs.comp bp
  have hp := intOfNat.comp (Primrec.nat_add.comp aa ab)
  have hc := Primrec.ite (intNegative.comp ap)
    (Primrec.ite (intNegative.comp bp) (intNeg.comp hp) (intSubNat.comp ab aa))
    (Primrec.ite (intNegative.comp bp) (intSubNat.comp aa ab) hp)
  exact hc.of_eq (fun p => by
    rcases p with ⟨a,b⟩
    cases a <;> cases b <;>
      simp only [Int.natAbs_natCast, Int.natAbs_negSucc, Int.ofNat_eq_natCast,
      Int.negSucc_lt_zero, not_lt_of_ge (Int.natCast_nonneg _), ↓reduceIte]
    all_goals simp [Int.negSucc_eq] <;> omega)

theorem intSub : Primrec₂ (fun a b : ℤ => a - b) :=
  (intAdd.comp Primrec.fst (intNeg.comp Primrec.snd)).of_eq (fun _ => by simp [sub_eq_add_neg])

theorem intMul : Primrec₂ (fun a b : ℤ => a * b) := by
  have ap := Primrec.fst (α := ℤ) (β := ℤ)
  have bp := Primrec.snd (α := ℤ) (β := ℤ)
  have hp := intOfNat.comp (Primrec.nat_mul.comp (intNatAbs.comp ap) (intNatAbs.comp bp))
  have hc := Primrec.ite (intNegative.comp ap)
    (Primrec.ite (intNegative.comp bp) hp (intNeg.comp hp))
    (Primrec.ite (intNegative.comp bp) (intNeg.comp hp) hp)
  exact hc.of_eq (fun p => by
    rcases p with ⟨a,b⟩
    cases a <;> cases b <;>
      simp only [Int.natAbs_natCast, Int.natAbs_negSucc, Int.ofNat_eq_natCast,
      Int.negSucc_lt_zero, not_lt_of_ge (Int.natCast_nonneg _), ↓reduceIte]
    all_goals simp [Int.negSucc_eq] <;> ring)

theorem intLE : PrimrecRel (fun a b : ℤ => a ≤ b) := by
  exact (intNegative.comp (intSub.comp Primrec.snd Primrec.fst)).not.of_eq (fun p => by dsimp only; omega)

end RecursiveArithmetic

attribute [fun_prop] Primrec
attribute [fun_prop] Primrec.id Primrec.const Primrec.comp Primrec.pair Primrec.fst Primrec.snd
attribute [fun_prop] RecursiveArithmetic.intOfNat RecursiveArithmetic.intNatAbs
attribute [fun_prop] RecursiveArithmetic.intNeg RecursiveArithmetic.factorial
namespace RecursiveArithmetic
@[fun_prop] theorem int_add : Primrec (fun p : ℤ × ℤ => p.1 + p.2) := intAdd
@[fun_prop] theorem int_sub : Primrec (fun p : ℤ × ℤ => p.1 - p.2) := intSub
@[fun_prop] theorem int_mul : Primrec (fun p : ℤ × ℤ => p.1 * p.2) := intMul
@[fun_prop] theorem nat_add : Primrec (fun p : ℕ × ℕ => p.1 + p.2) := Primrec.nat_add
@[fun_prop] theorem nat_sub : Primrec (fun p : ℕ × ℕ => p.1 - p.2) := Primrec.nat_sub
@[fun_prop] theorem nat_mul : Primrec (fun p : ℕ × ℕ => p.1 * p.2) := Primrec.nat_mul
@[fun_prop] theorem nat_pow : Primrec (fun p : ℕ × ℕ => p.1 ^ p.2) := natPow
@[fun_prop] theorem nat_div : Primrec (fun p : ℕ × ℕ => p.1 / p.2) := Primrec.nat_div
@[fun_prop] theorem nat_mod : Primrec (fun p : ℕ × ℕ => p.1 % p.2) := Primrec.nat_mod
@[fun_prop] theorem nat_max : Primrec (fun p : ℕ × ℕ => max p.1 p.2) := Primrec.nat_max
@[fun_prop] theorem natSucc : Primrec Nat.succ := Primrec.succ

@[fun_prop] theorem list_cons {α : Type*} [Primcodable α] :
    Primrec (fun p : α × List α => p.1 :: p.2) := Primrec.list_cons

@[fun_prop] theorem list_append {α : Type*} [Primcodable α] :
    Primrec (fun p : List α × List α => p.1 ++ p.2) := Primrec.list_append

@[fun_prop] theorem natListSum : Primrec (List.sum : List ℕ → ℕ) :=
  (Primrec.list_foldr Primrec.id (Primrec.const 0) (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    (fun l => by dsimp only; induction l <;> simp_all)

@[fun_prop] theorem natListProd : Primrec (List.prod : List ℕ → ℕ) :=
  (Primrec.list_foldr Primrec.id (Primrec.const 1) (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    (fun l => by dsimp only; induction l <;> simp_all)

end RecursiveArithmetic

namespace RecursiveArithmetic
@[fun_prop] theorem bool_cond {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Bool} {f g : α → β} (hp : Primrec p) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => if p a then f a else g a) :=
  (Primrec.cond hp hf hg).of_eq (fun a => by cases p a <;> rfl)

@[fun_prop] theorem listMap {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : α → List β} {g : α × β → γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a).map (fun b => g (a,b))) := Primrec.list_map hf hg

@[fun_prop] theorem listFlatMap {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : α → List β} {g : α × β → List γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a).flatMap (fun b => g (a,b))) := Primrec.list_flatMap hf hg
end RecursiveArithmetic

namespace ProfileJets
open RecursiveArithmetic

@[fun_prop] theorem factorBound_primrec : Primrec factorBound := by
  unfold factorBound; fun_prop
@[fun_prop] theorem productBound_primrec : Primrec productBound := by
  exact natListProd.comp (Primrec.list_map Primrec.id (factorBound_primrec.comp Primrec.snd).to₂)
@[fun_prop] theorem termBound_primrec : Primrec termBound := by
  unfold termBound; fun_prop
@[fun_prop] theorem bound_primrec : Primrec bound := by
  exact natListSum.comp (Primrec.list_map Primrec.id (termBound_primrec.comp Primrec.snd).to₂)

@[fun_prop] theorem multPrefix_primrec :
    Primrec (fun p : ℤ × List Factor × Expr => multPrefix p.1 p.2.1 p.2.2) := by
  have hh : Primrec (fun p : (ℤ × List Factor × Expr) × Term =>
      (p.1.1 * p.2.1, p.1.2.1 ++ p.2.2)) := by fun_prop
  exact Primrec.list_map (Primrec.snd.comp Primrec.snd) hh.to₂

@[fun_prop] theorem diffFactor_primrec : Primrec diffFactor := by
  unfold diffFactor; fun_prop

@[fun_prop] theorem diffProduct_primrec : Primrec diffProduct := by
  have hh : Primrec (fun p : List Factor × Factor × List Factor × Expr =>
      multPrefix 1 p.2.2.1 (diffFactor p.2.1) ++ multPrefix 1 [p.2.1] p.2.2.2) := by
    fun_prop
  exact (Primrec.list_rec Primrec.id (Primrec.const []) hh.to₂).of_eq
    (fun l => by dsimp only; induction l <;> simp_all [diffProduct])

@[fun_prop] theorem diffTerm_primrec : Primrec diffTerm := by
  unfold diffTerm; fun_prop
@[fun_prop] theorem diff_primrec : Primrec diff := by
  exact Primrec.list_flatMap Primrec.id (diffTerm_primrec.comp Primrec.snd).to₂
@[fun_prop] theorem jet_primrec : Primrec (fun p : Expr × ℕ => jet p.1 p.2) := by
  exact Primrec.nat_iterate Primrec.snd Primrec.fst (diff_primrec.comp Primrec.snd)

@[fun_prop] theorem pulseBound_primrec : Primrec pulseBound := by
  unfold pulseBound; fun_prop
@[fun_prop] theorem bumpBound_primrec : Primrec bumpBound := by
  unfold bumpBound; fun_prop
end ProfileJets

namespace RecursiveArithmetic
@[fun_prop] theorem inputMachine : Primrec Input.machine :=
  Primrec.fst.comp (Primrec.of_equiv (e := Input.codeEquiv))
@[fun_prop] theorem inputWord : Primrec Input.word :=
  Primrec.snd.comp (Primrec.of_equiv (e := Input.codeEquiv))
@[fun_prop] theorem machineStates : Primrec Machine.states :=
  Primrec.fst.comp (Primrec.of_equiv (e := Machine.codeEquiv))
@[fun_prop] theorem machineSymbols : Primrec Machine.symbols :=
  (Primrec.fst.comp Primrec.snd).comp (Primrec.of_equiv (e := Machine.codeEquiv))
@[fun_prop] theorem machineStart : Primrec Machine.start :=
  (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp (Primrec.of_equiv (e := Machine.codeEquiv))
@[fun_prop] theorem listLength {α : Type*} [Primcodable α] : Primrec (List.length : List α → ℕ) :=
  Primrec.list_length

@[fun_prop] theorem ofDigits : Primrec (fun p : ℕ × List ℕ => Nat.ofDigits p.1 p.2) := by
  have hg : Primrec (fun p : (ℕ × List ℕ) × ℕ × ℕ => p.2.1 + p.1.1 * p.2.2) := by fun_prop
  exact (Primrec.list_foldr Primrec.snd (Primrec.const 0) hg.to₂).of_eq
    (fun p => by dsimp only; induction p.2 <;> simp_all [Nat.ofDigits])

@[fun_prop] theorem sumRange {α : Type*} [Primcodable α] {f : α → ℕ} {g : α → ℕ → ℕ}
    (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => ∑ i ∈ Finset.range (f a), g a i) := by
  have hh := natListSum.comp (Primrec.list_map (Primrec.list_range.comp hf) hg)
  exact hh.of_eq (fun a => by simpa only [List.toFinset_range] using (List.sum_toFinset (g a) List.nodup_range).symm)
end RecursiveArithmetic

namespace CompilerPlanar
@[fun_prop] theorem radix_primrec : Primrec radix := by unfold radix; fun_prop
@[fun_prop] theorem loadingCode_primrec : Primrec loadingCode := by
  have he : loadingCode = fun d => Nat.ofDigits (radix d) d.word * radix d ^ (d.word.length+1) +
      d.machine.start * radix d ^ (2*(d.word.length+1)) := by
    funext d
    simp [loadingCode, StackCode.configurationCode, StackCode.stackExecution,
      StackCode.initialCode, StackCode.pack, Scales.width]
    rw [pow_mul]; ring
  rw [he]; fun_prop
end CompilerPlanar

namespace Scales
open RecursiveArithmetic
@[fun_prop] theorem capacity_primrec : Primrec (fun p : ℕ × ℕ × ℕ => capacity p.1 p.2.1 p.2.2) := by
  unfold capacity codeExponent width; fun_prop
@[fun_prop] theorem exponent_primrec : Primrec (fun p : ℕ × ℕ => exponent p.1 p.2) := by
  unfold exponent codeExponent width; fun_prop
@[fun_prop] theorem crudeSlotBound_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ × ℕ => crudeSlotBound p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold crudeSlotBound; fun_prop
@[fun_prop] theorem allSlotsBound_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ × ℕ => allSlotsBound p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have h : Primrec (fun p : ℕ × ℕ × ℕ × ℕ =>
      ∑ n ∈ Finset.range (max 1 p.2.2.1), (n+3)^p.2.2.2 * crudeSlotBound p.1 p.2.1 p.2.2.1 n) := by
    have hg : Primrec (fun p : (ℕ × ℕ × ℕ × ℕ) × ℕ =>
        (p.2+3)^p.1.2.2.2 * crudeSlotBound p.1.1 p.1.2.1 p.1.2.2.1 p.2) := by fun_prop
    exact sumRange (by fun_prop) hg.to₂
  unfold allSlotsBound weightBound
  exact Primrec.nat_add.comp (by fun_prop) h
end Scales
namespace Planar
@[fun_prop] theorem planarBound_primrec : Primrec (fun p : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
    planarBound p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  unfold planarBound; fun_prop
end Planar

end
end PeriodicLattice

end OAI
