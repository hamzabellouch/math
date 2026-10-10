import Mathlib
import OAI.Probability.LogConcave.Numerics.Picard
import OAI.Probability.LogConcave.Sampling.PrimitiveExpectedFieldLipschitz

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory
open scoped Classical BigOperators NNReal

variable {X Z : Type*} [MeasurableSpace X] [PseudoMetricSpace Z] {d : ℕ}

lemma eval_exists_lipschitz {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (E : MeanTree X d) (f : Z → X)
    (hb : ∃K : ℝ≥0,LipschitzWith K (fun z => base E (f z)))
    (hc : centers (fun r b => 0<r ∧ (lam:ℝ)*r^2≤1/4 ∧
      ∃K : ℝ≥0,LipschitzWith K (fun z => b (f z))) E) :
    ∃K : ℝ≥0,LipschitzWith K (fun z => E.eval F (f z)) := by
  induction E with | node k b hm a r C ih =>
    choose K hK using fun i => ih i (hc i).1.2.2 (hc i).2
    let L : ℝ≥0 := ∑ i,K i
    have hL (i : Fin k) : K i≤L := Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i)
    have hM (i : Fin k) := (primitiveExpectedField_lipschitz hF (hc i).1.1 (hc i).1.2.1).comp ((hK i).weaken (hL i))
    have hs := finite_weighted_lipschitz a (fun i z => primitiveExpectedField F ((C i).eval F (f z)) (r i)) hM
    obtain ⟨L,hL⟩ := hb
    exact ⟨_,hL.add hs⟩

end LogConcaveSampling.MeanTree

end

end

end OAI
