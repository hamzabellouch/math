import OAI.Computability.DegreeRigidity.OrdinalCodes.NumericalCohenSets
import OAI.Computability.DegreeRigidity.CohenForcing.InternalCohenValue

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory UniformArithmetic Encodable
open CohenBorelForcing ShuffleRequirements
open EncodedForcing (word word_primrec)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem realizes_arith : Arith (fun O n => Realizes (word n) (O 0)) := by
  have hbit := Arith.pure (fun v => (word (left v)).getD (right v) false = true)
    (Primrec.eq.comp ((Primrec.list_getD false).comp (word_primrec.comp left_primrec)
      right_primrec) (Primrec.const true))
  have hquery := (Arith.query 0).comp _ right_primrec
  have hlt := less right_primrec (Primrec.list_length.comp (word_primrec.comp left_primrec))
  apply (hlt.imp (hbit.iff hquery)).all.congr
  intro O n
  simp only [left,right,Nat.unpair_pair]
  constructor
  · intro h i hi
    have hh := h i hi
    cases hb : (word n).getD i false <;> cases ho : O 0 i <;> simp_all
  · intro h i hi
    have hh : (word n).getD i false = O 0 i := h i hi
    rw [hh]

noncomputable def prefixCodes (A : Oracle) : Oracle :=
  arithmeticReal (fun O n => Realizes (word n) (O 0)) (fun _ => A)

theorem prefixCodes_true (A : Oracle) (n : ℕ) :
    prefixCodes A n = true ↔ Realizes (word n) A := arithmeticReal_true _ _ n

theorem prefixCodes_mem (N : ZFSet.{0}) (hN : Transitive N) (hTN : SourceT N)
    (A : Oracle) (hA : realCode A ∈ N) : realCode (prefixCodes A) ∈ N :=
  sourceT_arithmetic_comprehension N hN hTN realizes_arith (fun _ => A) (fun _ => hA)

theorem prefixFilterSet_eq_image (A : Oracle) :
    genericFilterSet conditions (pushFilter (realFilter A)).carrier = wordImage (prefixCodes A) := by
  apply ZFSet.ext
  intro q
  rw [mem_genericFilterSet]
  constructor
  · rintro ⟨p,hp,rfl⟩
    let s := conditionEquiv.symm p
    have hl : label conditions p = wordCode s.word := by
      rw [← label_encodeCondition s]
      exact congrArg (label conditions) (conditionEquiv.apply_symm_apply p).symm
    rw [hl,wordImage_spec (fun t => Realizes t A) _ (prefixCodes_true A)]
    exact hp
  · intro hq
    obtain ⟨s,rfl⟩ := (prefix_iff_wordCode q).mp ((mem_conditions q).mp (ZFSet.mem_sep.mp hq).1)
    have hs := (wordImage_spec (fun t => Realizes t A) _ (prefixCodes_true A) s).mp hq
    exact ⟨conditionEquiv ⟨s⟩,by simpa [pushFilter,realFilter] using hs,label_encodeCondition ⟨s⟩⟩

theorem prefixFilterSet_mem (N : ZFSet.{0}) (hN : Transitive N) (hTN : SourceT N)
    (A : Oracle) (hA : realCode A ∈ N) :
    genericFilterSet conditions (pushFilter (realFilter A)).carrier ∈ N := by
  rw [prefixFilterSet_eq_image]
  exact wordImage_mem N hN hTN _ (prefixCodes_mem N hN hTN A hA)

end TuringRigidity.InternalCohen

end OAI
