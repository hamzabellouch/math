import Mathlib
import OAI.Computability.MinUncut.Encoding.Binary
import OAI.Computability.MinUncut.Graphs.DemandOrder

namespace OAI

section
noncomputable section
namespace MinUncut.Outer.Parameters
open MinUncut.Inner MinUncut.SourceBridge
open MinUncutGames MinUncutGames.Reduction MinUncutGames.Foundations

def sourceError {J : ℕ} (P : Parameters J) : ℚ := min (1/2) (P.o.b4/P.o.t)

lemma sourceError_pos {J : ℕ} (P : Parameters J) : 0<P.sourceError := by
  apply lt_min (by norm_num)
  exact div_pos P.ho.2.1 (by exact_mod_cast P.t_pos)

lemma sourceError_small {J : ℕ} (P : Parameters J) : P.sourceError≤1/2 := min_le_left _ _

lemma sourceError_budget {J : ℕ} (P : Parameters J) : (P.o.t:ℝ)*(P.sourceError:ℝ)≤P.o.b4 := by
  have hh := min_le_right (1/2:ℚ) (P.o.b4/P.o.t)
  have ht : (0:ℚ)<P.o.t := by exact_mod_cast P.t_pos
  have hh' : (P.o.t:ℚ)*P.sourceError≤P.o.b4 := by
    rw [mul_comm]
    exact (le_div_iff₀ ht).mp hh
  exact_mod_cast hh'

def baseTable : PCP.RoundTables.BaseTable := Classical.choose PCP.ExpanderTables.exists_base_table

lemma baseTable_certificate :
    PCP.SpectralReturn.SpectralCertificate (PCP.ExpanderTables.graph baseTable) (1/100:ℝ) :=
  Classical.choose_spec PCP.ExpanderTables.exists_base_table

def sourceReduction {J : ℕ} (P : Parameters J) : SourceBridge.BinaryReduction P.sourceError :=
  SourceBridge.binaryReduction {
    reduce := MinUncutGames.Outer.HastadSource.output baseTable P.sourceError P.sourceError_pos
    completeness := MinUncutGames.Outer.HastadSource.complete baseTable P.sourceError P.sourceError_pos
    soundness := MinUncutGames.Outer.HastadSource.sound baseTable baseTable_certificate P.sourceError P.sourceError_pos
    computation := MinUncutGames.Outer.HastadSource.computation baseTable P.sourceError P.sourceError_pos
    finiteAlphabet := MinUncutGames.Outer.HastadSource.finiteAlphabet baseTable P.sourceError P.sourceError_pos }

def sourceGraph {J : ℕ} (P : Parameters J) (F : BinaryFormula.Formula) : MinUncut.Output :=
  P.graph (equations (P.sourceReduction.reduce F))

lemma sourceGraph_yes {J : ℕ} (P : Parameters J) (F : BinaryFormula.Formula) (hF : F.Satisfiable) :
    (P.sourceGraph F).opt≤(P.sourceGraph F).threshold := by
  obtain ⟨s,hs⟩ := binaryReduction_complete P.sourceReduction F hF P.o.t P.o.b4 P.sourceError_budget
  exact P.graph_yes _ s hs

lemma sourceGraph_no {K J : ℕ} (hK : 2≤K) (hKJ : 8*K≤J) (P : Parameters J)
    (F : BinaryFormula.Formula) (hF : ¬F.Satisfiable) :
    K*(P.sourceGraph F).threshold<(P.sourceGraph F).opt :=
  P.graph_no hK hKJ _ (binaryReduction_sound P.sourceError_small P.sourceReduction F hF)

end MinUncut.Outer.Parameters
namespace MinUncut
open Outer

def parameters (K : ℕ) : Parameters (10*(max K 2)) := Parameters.select _ (by omega)

def semanticReduction (K : ℕ) (F : MinUncutGames.BinaryFormula.Formula) : Output :=
  (parameters K).sourceGraph F

lemma semanticReduction_yes {K : ℕ} (F : MinUncutGames.BinaryFormula.Formula) (hF : F.Satisfiable) :
    (semanticReduction K F).opt≤(semanticReduction K F).threshold :=
  (parameters K).sourceGraph_yes F hF

lemma semanticReduction_no {K : ℕ} (hK : 2≤K) (F : MinUncutGames.BinaryFormula.Formula) (hF : ¬F.Satisfiable) :
    K*(semanticReduction K F).threshold<(semanticReduction K F).opt :=
  (parameters K).sourceGraph_no hK (by omega) F hF

end MinUncut

end
end

end OAI
