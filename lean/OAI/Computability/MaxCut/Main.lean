import Mathlib
import OAI.Computability.MaxCut.Machines.MachineUniformRounding
import OAI.Computability.MaxCut.Games.UniformPartition
import OAI.Computability.MaxCut.PCP.Parity
import OAI.Computability.MaxCut.Encoding.PortTableEncoding
import OAI.Computability.MaxCut.Machines.MachineTableIteration
import OAI.Computability.MaxCut.Games.CloneTable
import OAI.Computability.MaxCut.Games.Theorem
import OAI.Computability.MaxCut.Encoding.Bit
import OAI.Computability.MaxCut.Arithmetic.GridComputer

namespace OAI

noncomputable section

namespace OptimalMaxCut.LongCode.InstanceAdapter
open MaxCutGames.Foundations.Target MaxCutGames.Foundations.Complexity

theorem bits_eq_gameBits {q : ℕ} (g : Instance q) : bits g = gameBits g := by
  have hw (l : List ℕ) : CounterMachine.Expr.unaryWords l = encodeWords l := by
    induction l with
    | nil => rfl
    | cons n l ih =>
      simp only [CounterMachine.Expr.unaryWords,List.flatMap_cons,encodeWords,encodeWord] at *
      rw [ih]
  unfold bits gameBits
  rw [hw]
  rfl

 theorem exists_encoded_gridComputer (q : ℕ) (t : ℚ) (ht : t ∈ Set.Icc (-1:ℚ) 1) (K : ℕ) :
    ∃ pc : Turing.TM2ComputableInPolyTime (gameBits : Instance q → List Bool) ScaledGraph.bits
      (fun g => gridGraph g t ht K), MachineFiniteAlphabet.FiniteAlphabet pc.tm := by
  obtain ⟨pc,hpc⟩ := exists_gridComputer q t ht K
  let pc' : Turing.TM2ComputableInPolyTime (gameBits : Instance q → List Bool) ScaledGraph.bits
      (fun g => gridGraph g t ht K) := {
    tm := pc.tm
    inputAlphabet := pc.inputAlphabet
    outputAlphabet := pc.outputAlphabet
    time := pc.time
    outputsFun := fun g => by simpa only [bits_eq_gameBits] using pc.outputsFun g }
  exact ⟨pc',hpc⟩
end OptimalMaxCut.LongCode.InstanceAdapter

namespace OptimalMaxCut
open LongCode LongCode.InstanceAdapter
open MaxCutGames.Foundations.Target MaxCutGames.Foundations.Complexity

/-- Optimal Max-Cut approximation hardness: for EVERY fixed real alpha above
the exact Goemans--Williamson constant, an ordinary binary polynomial reduction
prints a full finite SIMPLE UNWEIGHTED graph and a strict YES/NO optimum gap.
The construction uses an analytic inequality, rational long-code construction,
integer rounding, finite-field derandomization and a graph-printer TM. -/
theorem main : MainStatement := by
  intro α ha ha1
  obtain ⟨t,ε,y,n,δ,K,ht,ht0,ht1,hε,hεhalf,hδ,hδhalf,hy,hn,hgap,hcomplete,hsound⟩ :=
    Game.exists_grid_gap_parameters α ha ha1
  obtain ⟨ug⟩ := MaxCutGames.theorem11 (ε : ℝ) δ (by exact_mod_cast hε)
    hεhalf hδ hδhalf
  obtain ⟨pc,hpc⟩ := exists_encoded_gridComputer ug.alphabet t ht K
  refine ⟨{
    yesBound := y
    noBound := n
    yes_pos := hy
    no_nonneg := hn
    gap := hgap
    construct := fun input => gridGraph (ug.construct input) t ht K
    computation := MachineSequential.composeBits ug.computation pc
    finiteAlphabet := MachineFiniteAlphabet.composeBits ug.computation pc ug.finiteAlphabet hpc
    completeness := ?_
    soundness := ?_ }⟩
  · intro input hin
    exact hcomplete (ofInstance (ug.construct input)) (vertexEquiv _ _) (anchor _)
      (InstanceAdapter.complete _ _ (ug.completeness input hin))
  · intro input hin
    exact hsound (by have := ug.alphabetAtLeastTwo; omega)
      (ofInstance (ug.construct input)) (vertexEquiv _ _) (anchor _)
      (InstanceAdapter.sound _ (ug.simpleBipartite input) _ (ug.soundness input hin))

end OptimalMaxCut

example : OptimalMaxCut.MainStatement := OptimalMaxCut.main

end

end OAI
