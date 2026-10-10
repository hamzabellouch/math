import Mathlib
import OAI.Computability.QuantumFactoring.BitStackTabulate
import OAI.Computability.QuantumFactoring.BitStackDivision
import OAI.Computability.QuantumFactoring.BitStackOptions

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
lemma boolFold_eq (xs : List Bool) (b : Bool) :
    xs.foldl (fun b a=>a&&b) b=(xs.all id && b):=by
  induction xs generalizing b with
  | nil=>simp
  | cons a xs ih=>simp only [List.foldl_cons,ih,List.all_cons,id_eq];cases a <;> cases b <;> simp
namespace Procedure
noncomputable def boolListAll : Procedure (listCode boolCode) boolCode (fun xs=>xs.all id):=by
  let fold:=foldList false boolAnd (Polynomial.C 1) (by intro xs b i;simp only [boolCode,List.length_singleton,Polynomial.eval_C];rfl)
  exact (fold.comp ((identity _).pair (constant _ boolCode true))).congrFun (by intro xs;change xs.foldl (fun b a=>a&&b) true=xs.all id;rw [boolFold_eq];simp)
noncomputable def unaryPrime : Procedure unaryCode boolCode (fun n=>decide (Nat.Prime n)):=by
  let i:=(unaryToBits.comp (first unaryCode Nat.bits))
  let n:=second unaryCode Nat.bits
  let small:=binaryLt.comp (i.pair (constant _ Nat.bits 2))
  let nondvd:=boolNot.comp (binaryEq.comp ((binaryMod.comp (n.pair i)).pair (constant _ Nat.bits 0)))
  let test:=boolOr.comp (small.pair nondvd)
  let table:=tabulate (f:=fun n i=>decide (i<2) || !decide (n%i=0)) false test
  let all:=(boolListAll.comp table).comp ((identity unaryCode).pair unaryToBits)
  let large:=boolNot.comp (binaryLt.comp (unaryToBits.pair (constant unaryCode Nat.bits 2)))
  exact (boolAnd.comp (large.pair all)).congrFun (by
    intro n
    apply Bool.eq_iff_iff.mpr
    change ((!decide (n<2)) && ((List.range n).map (fun i=>decide (i<2) || !decide (n%i=0))).all id)=true ↔ _
    simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_false_iff_not,List.all_eq_true,List.mem_map,
      id_eq,decide_eq_true_eq]
    rw [Nat.prime_def_lt']
    constructor
    · rintro ⟨hn,h⟩
      refine ⟨by omega,?_⟩
      intro m hm hmn hd
      have ht:=h _ ⟨m,List.mem_range.mpr hmn,rfl⟩
      simp only [Bool.or_eq_true,decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not] at ht
      exact ht.elim (by omega) (fun h=>h (Nat.dvd_iff_mod_eq_zero.mp hd))
    · rintro ⟨hn,h⟩
      refine ⟨by omega,?_⟩
      rintro b ⟨m,hm,rfl⟩
      simp only [Bool.or_eq_true,decide_eq_true_eq,Bool.not_eq_true',decide_eq_false_iff_not]
      by_cases hlt : m<2
      · exact Or.inl hlt
      · exact Or.inr (fun hz=>h m (by omega) (List.mem_range.mp hm) (Nat.dvd_iff_mod_eq_zero.mpr hz)))
end Procedure

end ExactQuantumFactoring.BitStackProgram
end

end OAI
