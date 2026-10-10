import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.Program

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler.Program
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {Ω E R : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace R] {d q r : ℕ}

def independentSeq (A : Program Ω d q E) (B : Program (E × R) d r E) :
    Program (Ω × R) d (q+r) E :=
  (A.seedMap Prod.fst measurable_fst).seq
    (B.seedMap (fun p => (p.2,p.1.2)) (by fun_prop))

lemma independentSeq_run (A : Program Ω d q E) (B : Program (E × R) d r E)
    (V : Point d → ℝ) (p : Ω × R) :
    (A.independentSeq B).run V p=B.run V (A.run V p.1,p.2) := by
  rw [independentSeq,seq_run,seedMap_run,seedMap_run]

lemma independentSeq_law (A : Program Ω d q E) (B : Program (E × R) d r E)
    {V : Point d → ℝ} (hV : Measurable (firstOrderReply V)) (μ : Measure Ω) (γ : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] :
    (μ.prod γ).map ((A.independentSeq B).run V)=((μ.map (A.run V)).prod γ).map (B.run V) := by
  have hm := Measure.map_prod_map μ γ (A.measurable_run V hV) measurable_id
  rw [Measure.map_id] at hm
  rw [hm,Measure.map_map (B.measurable_run V hV) ((A.measurable_run V hV).prodMap measurable_id)]
  congr 1
  funext p
  exact independentSeq_run A B V p

end LogConcaveSampling.OracleCompiler.Program

end

end

end OAI
