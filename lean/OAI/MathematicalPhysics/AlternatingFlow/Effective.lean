import OAI.MathematicalPhysics.AlternatingFlow.Machines

namespace OAI

section EffectiveDevelopment

open scoped BigOperators ENNReal Topology ContDiff
open MeasureTheory

namespace AlternatingNS
namespace Effective

lemma nat_pow : Primrec₂ (fun b n : ℕ => b ^ n) :=
  Primrec₂.unpaired'.mp Nat.Primrec.pow

lemma capacity : Primrec₂ Scales.K :=
  Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)) (Primrec.const 2)

lemma exponent : Primrec₂ Scales.s :=
  Primrec.nat_mul.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 1))
    (nat_pow.comp (Primrec.const 2) (nat_pow.comp
      (Primrec.nat_add.comp Primrec.snd (Primrec.const 3)) (Primrec.const 2)))

lemma states : Primrec Machine.states :=
  Primrec.nat_add.comp Primrec.fst (Primrec.const 1)

lemma alphabet : Primrec Machine.alphabet :=
  Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)

lemma initialState : Primrec Machine.initialState :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

lemma haltingStates : Primrec Machine.haltingStates :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

lemma table : Primrec Machine.table :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

lemma base : Primrec Machine.base :=
  Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.nat_add.comp (Primrec.const 1)
      (Primrec.nat_max.comp (Primrec.nat_add.comp states (Primrec.const 1)) alphabet))

lemma instruction : Primrec (fun z : Machine × ℕ × ℕ => z.1.instruction z.2.1 z.2.2) := by
  have h := Primrec.list_getElem?.comp (table.comp Primrec.fst)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd)
      (alphabet.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.option_getD.comp h (Primrec.const none)).of_eq (by
    intro z; dsimp only [Machine.instruction];
    cases (z.1.table[z.2.1 * z.1.alphabet + z.2.2]?) <;> rfl)

lemma member {α : Type*} [Primcodable α] : PrimrecRel (fun l : List α => fun a => a ∈ l) :=
  (Primrec.eq.exists_mem_list).of_eq (by simp)

lemma command : Primrec (fun z : Machine × ℕ × ℕ => z.1.command z.2.1 z.2.2) := by
  apply Primrec.ite
  · exact (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (states.comp Primrec.fst)).or
      (member.comp (haltingStates.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
  · exact (Primrec.fst.comp Primrec.snd).pair
      ((Primrec.snd.comp Primrec.snd).pair (Primrec.const (1 : Fin 3)))
  · exact Primrec.option_getD.comp instruction ((states.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.snd).pair (Primrec.const (1 : Fin 3))))

lemma program_of_computable {A B : Type*} [Primcodable A] [Primcodable B]
    (f : A → B) (hf : Computable f) : ∃ c : Program, ∀ a, Returns c a (f a) := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  refine ⟨c, fun a => ?_⟩
  simp [Returns, hc, Encodable.encodek]

lemma compiler_of_computable {A B C : Type*} [Primcodable A] [Primcodable B] [Primcodable C]
    (f : A → B → C) (hf : Computable₂ f) :
    ∃ compile : A → Program, Computable compile ∧
      ∀ a b, Returns (compile a) b (f a b) := by
  obtain ⟨c, hc⟩ := program_of_computable (fun z : A × B => f z.1 z.2) hf
  refine ⟨fun a => c.curry (Encodable.encode a),
    (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const c) Primrec.encode).to_comp, ?_⟩
  intro a b
  simpa only [Returns, Nat.Partrec.Code.eval_curry, Encodable.encode_prod_val] using hc (a, b)

theorem command_program : ∃ compile : Machine → Program, Computable compile ∧
    ∀ M q a, Returns (compile M) (q, a) (M.command q a) := by
  obtain ⟨c, hC, h⟩ := compiler_of_computable
    (fun M : Machine => fun z : ℕ × ℕ => M.command z.1 z.2) command.to_comp
  exact ⟨c, hC, fun M q a => h M (q, a)⟩

end Effective
end AlternatingNS

end EffectiveDevelopment

end OAI
