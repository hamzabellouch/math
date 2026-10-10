import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Sewn
import OAI.Combinatorics.MatchingCount.Sampling.FiniteSampler
import OAI.Combinatorics.MatchingCount.Sampling.FiniteSampler2
import OAI.Combinatorics.MatchingCount.Sampling.FiniteSampler3
import OAI.Combinatorics.MatchingCount.Sampling.FiniteSampler4
import OAI.Combinatorics.MatchingCount.Algorithm.GuardBudget
import OAI.Combinatorics.MatchingCount.Machines.ProgramComposition
import OAI.Combinatorics.MatchingCount.Graphs.Output
import OAI.Combinatorics.MatchingCount.Arithmetic.TreeDivision
import OAI.Combinatorics.MatchingCount.Machines.TreeLanguage
import OAI.Combinatorics.MatchingCount.Sampling.TreeUnitCorrect
import OAI.Combinatorics.MatchingCount.Tapes.RandomReservoir
import OAI.Combinatorics.MatchingCount.Complexity.PhysicalCost
import OAI.Combinatorics.MatchingCount.Probability.MainLaw

namespace OAI

namespace MatchingFPRAS

theorem thm_main : MainStatement := by
  obtain ⟨C,d,hC,hbound⟩:=LiteralPhysical.mainTime_bound
  refine ⟨LiteralPhysical.mainProgram.machine,C,d,hC,?_⟩
  intro G ε δ he he1 hd _hd1
  dsimp only
  have hn:=hbound G ε δ he he1 hd.le
  obtain ⟨hp,hz⟩:=LiteralPhysical.mainProgram_outputs G ε δ he he1 hd.le
    (timeBound C d G ε δ) hn
  exact ⟨hp,hz,LiteralPhysical.mainProgram_success G ε δ he he1 hd
    (timeBound C d G ε δ) hn⟩
end MatchingFPRAS

end OAI
