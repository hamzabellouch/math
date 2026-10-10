import Mathlib
import OAI.Computability.MaxCut.Machines.Printer
import OAI.Computability.MaxCut.Estimates.Anchor

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode.InstanceAdapter
open scoped BigOperators
open MaxCutGames.Foundations.Target CounterMachine Turing
attribute [local instance] Classical.propDecidable

theorem exists_gridComputer (q : ℕ) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ) :
    ∃ pc : TM2ComputableInPolyTime (bits : Instance q → List Bool) ScaledGraph.bits
      (fun g => gridGraph g t ht K), ∀ k, Finite (pc.tm.Γ k) := by
  obtain ⟨len,hlen⟩ := RawGrid.Rep.length q (K+1)
  obtain ⟨bit,hbit⟩ := RawGrid.Rep.entry q t ht K (K+1) (Expr.Represented.arg 0)
  have htable (g : Instance q) : table len bit (bits g) = (gridGraph g t ht K).bits := by
    apply List.ext_getElem
    · simp only [table,List.length_ofFn,hlen,RawGrid.bits_length]
    · intro i hi hj
      have hi' : i<RawGrid.length q (K+1) (bits g) := by
        simpa only [RawGrid.bits_length] using hj
      have hh := RawGrid.bits_getD g t ht K i hi'
      rw [List.getElem?_eq_getElem hj] at hh
      simp only [Option.getD_some] at hh
      simp only [table,List.getElem_ofFn,hbit]
      exact hh.symm
  let first := tableComputer len bit
  let pc : TM2ComputableInPolyTime (bits : Instance q → List Bool) ScaledGraph.bits
      (fun g => gridGraph g t ht K) := {
    tm := first.tm
    inputAlphabet := first.inputAlphabet
    outputAlphabet := first.outputAlphabet
    time := first.time
    outputsFun := fun g => by
      have hh := first.outputsFun (bits g)
      change TM2OutputsInTime first.tm ((bits g).map first.inputAlphabet.symm)
        (some ((table len bit (bits g)).map first.outputAlphabet.symm)) _ at hh
      rw [htable] at hh
      exact hh }
  exact ⟨pc, tableComputer_finiteAlphabet len bit⟩

end OptimalMaxCut.LongCode.InstanceAdapter

end

end OAI
