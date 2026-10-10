import OAI.Analysis.PeriodicLattice.RationalArithmetic

namespace OAI

/-! Well-formed input encodings and effective real enclosures. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingEffectiveReals {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace RecursiveArithmetic
open Encodable Primrec
local instance effectiveRealsLocal1 : Primcodable ℚ := ratPrimcodable

@[fun_prop] theorem rat_abs : Primrec (abs : ℚ → ℚ) := by
  have hn : PrimrecPred (fun q : ℚ => q < 0) :=
    (intNegative.comp ratNum).of_eq (fun q => Rat.num_neg)
  exact (Primrec.ite hn ratNeg Primrec.id).of_eq (fun q => by split_ifs with h; exact (abs_of_neg h).symm; exact (abs_of_nonneg (not_lt.mp h)).symm)

theorem ratLE : PrimrecRel (fun a b : ℚ => a ≤ b) := by
  exact (intLE.comp (by fun_prop : Primrec (fun p : ℚ × ℚ => p.1.num * p.2.den))
    (by fun_prop : Primrec (fun p : ℚ × ℚ => p.2.num * p.1.den))).of_eq (fun p => (Rat.le_iff p.1 p.2).symm)

theorem ratLT : PrimrecRel (fun a b : ℚ => a < b) :=
  (ratLE.comp Primrec.snd Primrec.fst).not.of_eq (fun _ => not_le)

@[fun_prop] theorem rat_floor : Primrec (fun q : ℚ => ⌊q⌋) :=
  (int_div.comp (ratNum.pair (intOfNat.comp ratDen))).of_eq (fun q => (Rat.floor_def q).symm)

@[fun_prop] theorem listSumRat : Primrec (List.sum : List ℚ → ℚ) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (rat_add.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd))).to₂).of_eq
    (fun l => by dsimp only; induction l <;> simp_all)

@[fun_prop] theorem sumRangeRat {α : Type*} [Primcodable α] {f : α → ℕ} {g : α → ℕ → ℚ}
    (hf : Primrec f) (hg : Primrec₂ g) : Primrec (fun a => ∑ i ∈ Finset.range (f a), g a i) :=
  (listSumRat.comp (Primrec.list_map (Primrec.list_range.comp hf) hg)).of_eq
    (fun a => by simpa only [List.toFinset_range] using (List.sum_toFinset (g a) List.nodup_range).symm)

theorem allList {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α × β → Prop} {l : α → List β} (hp : PrimrecPred p) (hl : Primrec l) :
    PrimrecPred (fun a => ∀ b ∈ l a, p (a,b)) :=
  (hp.forall_mem_list.comp (Primrec.list_map hl (Primrec.fst.pair Primrec.snd).to₂)).of_eq
    (fun a => by simp)

@[fun_prop] theorem machineTable : Primrec Machine.table :=
  (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp (Primrec.of_equiv (e := Machine.codeEquiv))
@[fun_prop] theorem instructionState : Primrec Instruction.nextState :=
  Primrec.fst.comp (Primrec.of_equiv (e := Instruction.codeEquiv))
@[fun_prop] theorem instructionSymbol : Primrec Instruction.writeSymbol :=
  (Primrec.fst.comp Primrec.snd).comp (Primrec.of_equiv (e := Instruction.codeEquiv))
@[fun_prop] theorem instructionMove : Primrec Instruction.move :=
  (Primrec.snd.comp Primrec.snd).comp (Primrec.of_equiv (e := Instruction.codeEquiv))

theorem entryValid : PrimrecPred (fun p : Machine × Option Instruction =>
    ∀ I, p.2 = some I → I.nextState < p.1.states ∧ I.writeSymbol < p.1.symbols) := by
  have hp : PrimrecPred (fun p : Machine × Instruction =>
      p.2.nextState < p.1.states ∧ p.2.writeSymbol < p.1.symbols) :=
    (Primrec.nat_lt.comp (by fun_prop) (by fun_prop)).and
      (Primrec.nat_lt.comp (by fun_prop) (by fun_prop))
  have hg : Primrec (fun p : (Machine × Option Instruction) × Instruction =>
      decide (p.2.nextState < p.1.1.states ∧ p.2.writeSymbol < p.1.1.symbols)) :=
    hp.decide.comp (g := fun p : (Machine × Option Instruction) × Instruction => (p.1.1,p.2))
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have hc := Primrec.option_casesOn (o := fun p : Machine × Option Instruction => p.2)
      (f := fun _ => true) (g := fun p I => decide (I.nextState < p.1.states ∧ I.writeSymbol < p.1.symbols))
      Primrec.snd (Primrec.const true) hg.to₂
  exact (Primrec.eq.comp hc (Primrec.const true)).of_eq (fun p => by cases p.2 <;> simp)

theorem machineWellFormed : PrimrecPred Machine.WellFormed := by
  have hi : PrimrecPred (fun p : Machine × List (Option Instruction) =>
      ∀ e ∈ p.2, ∀ I, e = some I → I.nextState < p.1.states ∧ I.writeSymbol < p.1.symbols) :=
    allList (entryValid.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)) Primrec.snd
  exact ((Primrec.nat_lt.comp (Primrec.const 0) machineStates).and
    ((Primrec.nat_lt.comp (Primrec.const 0) machineSymbols).and
    ((Primrec.nat_lt.comp machineStart machineStates).and
    ((Primrec.nat_le.comp (Primrec.list_length.comp machineTable) machineStates).and
    ((allList (Primrec.nat_le.comp (Primrec.list_length.comp Primrec.snd)
      (machineSymbols.comp Primrec.fst)) machineTable).and (allList hi machineTable)))))).of_eq
    (fun _ => Iff.rfl)

theorem inputWellFormed : PrimrecPred Input.WellFormed :=
  ((machineWellFormed.comp inputMachine).and
    (allList (Primrec.nat_lt.comp Primrec.snd (machineSymbols.comp (inputMachine.comp Primrec.fst))) inputWord)).of_eq
      (fun _ => Iff.rfl)
end RecursiveArithmetic

abbrev ValidInput := {d : Input // d.WellFormed}
local instance validInputDec : DecidablePred Input.WellFormed := Classical.decPred _
local instance validInputCode : Primcodable ValidInput := Primcodable.subtype RecursiveArithmetic.inputWellFormed

namespace CertifiedReal
open Encodable Filter Topology
local instance effectiveRealsLocal2 : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable

def error (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
def qerror (n : ℕ) : ℚ := 1 / ((n : ℚ) + 1)

@[simp] theorem cast_qerror (n : ℕ) : (qerror n : ℝ) = error n := by simp [qerror, error]
theorem error_pos (n : ℕ) : 0 < error n := by unfold error; positivity
theorem error_le_one (n : ℕ) : error n ≤ 1 := by unfold error; exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
theorem error_tendsto : Tendsto error atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

@[fun_prop] theorem qerror_primrec : Primrec qerror := by unfold qerror; fun_prop

def Effective {A : Type*} [Primcodable A] (f : A → ℝ) : Prop :=
  ∃ q : A × ℕ → ℚ, Computable q ∧ ∀ a n, |f a - (q (a,n) : ℝ)| ≤ error n

section
variable {A B : Type*} [Primcodable A] [Primcodable B]

theorem computable_find {p : A → ℕ → Prop} [DecidableRel p]
    (hp : Computable (fun an : A × ℕ => decide (p an.1 an.2))) (he : ∀ a, ∃ n, p a n) :
    Computable (fun a => Nat.find (he a)) := by
  have hr : Partrec (fun a => Nat.rfind (fun n => Part.some (decide (p a n)))) :=
    Partrec.rfind hp.partrec.to₂
  apply hr.of_eq_tot
  intro a
  apply (Nat.mem_rfind (p := (fun n => Part.some (decide (p a n))) )).mpr
  constructor
  · simpa using Nat.find_spec (he a)
  · intro m hm
    simpa only [Part.mem_some_iff, eq_comm (a := false), decide_eq_false_iff_not] using Nat.find_min (he a) hm

theorem of_enclosures {f : A → ℝ} {q e : A × ℕ → ℚ}
    (hq : Computable q) (he : Computable e)
    (bound : ∀ a n, |f a - (q (a,n) : ℝ)| ≤ (e (a,n) : ℝ))
    (small : ∀ a, Tendsto (fun n => (e (a,n) : ℝ)) atTop (𝓝 0)) : Effective f := by
  have existsSmall : ∀ an : A × ℕ, ∃ k, e (an.1,k) ≤ qerror an.2 := by
    intro an
    have hh := (small an.1).eventually (gt_mem_nhds (error_pos an.2))
    obtain ⟨k,hk⟩ := hh.exists
    exact ⟨k, by exact_mod_cast (show (e (an.1,k) : ℝ) ≤ (qerror an.2 : ℝ) by simpa using hk.le)⟩
  have hc : Computable (fun p : (A × ℕ) × ℕ => decide (e (p.1.1,p.2) ≤ qerror p.1.2)) :=
    RecursiveArithmetic.ratLE.decide.to_comp.comp
      (he.comp ((Computable.fst.comp Computable.fst).pair Computable.snd))
      (qerror_primrec.to_comp.comp (Computable.snd.comp Computable.fst))
  let pick (an : A × ℕ) := Nat.find (existsSmall an)
  have hpick := computable_find (A := A × ℕ) (p := fun (an : A × ℕ) (k : ℕ) => e (an.1,k) ≤ qerror an.2) hc existsSmall
  have hfinal : Computable (fun an => q (an.1,pick an)) := hq.comp (Computable.fst.pair hpick)
  refine ⟨fun an => q (an.1,pick an), hfinal, ?_⟩
  intro a n
  apply (bound a (pick (a,n))).trans
  rw [← cast_qerror]
  exact_mod_cast Nat.find_spec (existsSmall (a,n))

theorem Effective.comp {f : B → ℝ} (hf : Effective f) {g : A → B} (hg : Computable g) :
    Effective (fun a => f (g a)) := by
  obtain ⟨q,hq,he⟩ := hf
  exact ⟨fun an => q (g an.1,an.2), hq.comp ((hg.comp Computable.fst).pair Computable.snd),
    fun a n => he (g a) n⟩

theorem Effective.congr {f g : A → ℝ} (hf : Effective f) (h : ∀ a, f a = g a) : Effective g := by
  simpa only [funext h] using hf

theorem rational {q : A → ℚ} (hq : Computable q) : Effective (fun a => (q a : ℝ)) :=
  ⟨fun an => q an.1, hq.comp Computable.fst, fun a n => by simpa using (error_pos n).le⟩

omit [Primcodable A] in
theorem Effective.approximants_tendsto {f : A → ℝ} {q : A × ℕ → ℚ}
    (he : ∀ a n, |f a - (q (a,n) : ℝ)| ≤ error n) (a : A) :
    Tendsto (fun n => (q (a,n) : ℝ)) atTop (𝓝 (f a)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) _ error_tendsto
  intro n
  simpa [Real.dist_eq, abs_sub_comm] using he a n
end
end CertifiedReal

attribute [fun_prop] Computable
attribute [fun_prop] Computable.id Computable.const Computable.comp Computable.pair Computable.fst Computable.snd
attribute [fun_prop] Primrec.to_comp

namespace CertifiedReal
open Encodable Filter Topology
local instance effectiveRealsLocal3 : Primcodable ℚ := RecursiveArithmetic.ratPrimcodable
section
variable {A B : Type*} [Primcodable A] [Primcodable B]

theorem constant (q : ℚ) : Effective (fun _ : A => (q : ℝ)) := rational (Computable.const _)

theorem Effective.add {f g : A → ℝ} (hf : Effective f) (hg : Effective g) :
    Effective (fun a => f a + g a) := by
  obtain ⟨q,hq,bq⟩ := hf
  obtain ⟨v,hv,bv⟩ := hg
  refine of_enclosures (q := fun an => q an + v an) (e := fun an => 2 * qerror an.2)
    (by fun_prop) (by fun_prop) ?_ ?_
  · intro a n
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat, cast_qerror, two_mul, sub_add_sub_comm] using
      abs_add_le (f a - (q (a,n) : ℝ)) (g a - (v (a,n) : ℝ)) |>.trans (add_le_add (bq a n) (bv a n))
  · intro a
    simpa using error_tendsto.const_mul 2

theorem Effective.neg {f : A → ℝ} (hf : Effective f) : Effective (fun a => -f a) := by
  obtain ⟨q,hq,bq⟩ := hf
  refine ⟨fun an => -q an, by fun_prop, fun a n => ?_⟩
  rw [Rat.cast_neg, show -f a - -(q (a,n) : ℝ) = -(f a - (q (a,n) : ℝ)) by ring, abs_neg]
  exact bq a n

theorem Effective.sub {f g : A → ℝ} (hf : Effective f) (hg : Effective g) :
    Effective (fun a => f a - g a) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem Effective.mul {f g : A → ℝ} (hf : Effective f) (hg : Effective g) :
    Effective (fun a => f a * g a) := by
  obtain ⟨q,hq,bq⟩ := hf
  obtain ⟨v,hv,bv⟩ := hg
  refine of_enclosures (q := fun an => q an * v an)
    (e := fun an => qerror an.2 * (|q an| + |v an| + qerror an.2))
    (by fun_prop) (by fun_prop) ?_ ?_
  · intro a n
    simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_abs, cast_qerror]
    have bg : |g a| ≤ |(v (a,n) : ℝ)| + error n := by
      have := abs_add_le (g a - (v (a,n) : ℝ)) (v (a,n) : ℝ)
      have := this.trans (add_le_add (bv a n) le_rfl)
      rw [sub_add_cancel] at this
      exact this.trans_eq (add_comm _ _)
    calc
      |f a * g a - (q (a,n) : ℝ) * (v (a,n) : ℝ)| =
        |(f a - q (a,n)) * g a + (q (a,n) : ℝ) * (g a - v (a,n))| := by congr 1; ring
      _ ≤ |f a - (q (a,n) : ℝ)| * |g a| + |(q (a,n) : ℝ)| * |g a - (v (a,n) : ℝ)| := by
        simpa only [abs_mul] using abs_add_le ((f a - q (a,n)) * g a) ((q (a,n) : ℝ) * (g a - v (a,n)))
      _ ≤ error n * (|(v (a,n) : ℝ)| + error n) + |(q (a,n) : ℝ)| * error n := by
        exact add_le_add (mul_le_mul (bq a n) bg (abs_nonneg _) (error_pos n).le)
          (mul_le_mul_of_nonneg_left (bv a n) (abs_nonneg _))
      _ = _ := by ring
  · intro a
    have hqa := Effective.approximants_tendsto bq a
    have hva := Effective.approximants_tendsto bv a
    simpa using error_tendsto.mul ((hqa.abs.add hva.abs).add error_tendsto)

end
end CertifiedReal

end
end PeriodicLattice

end OAI
