import Mathlib
import OAI.Probability.LogConcave.Sampling.TapeSnocEquiv
import OAI.Probability.LogConcave.OraclePrograms.Program

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.OracleCompiler.Program
open MeasureTheory ProbabilityTheory Function
open scoped Classical

variable {E R : Type*} [MeasurableSpace E] [MeasurableSpace R] {d q : ℕ}

def fresh (A : ℕ → Program (E × R) d q E) :
    (n : ℕ) → Program (E × (Fin n → R)) d (q*n) E
  | 0 => pure Prod.fst measurable_fst
  | n+1 =>
      (((fresh A n).seedMap (fun p : E × (Fin (n+1) → R) => (p.1,Fin.init p.2))
        (measurable_fst.prodMk (Measurable.of_eval
          (fun index => (measurable_pi_apply index.castSucc).comp measurable_snd)))).seq
        ((A n).seedMap (fun p : (E × (Fin (n+1) → R)) × E => (p.2,p.1.2 (Fin.last n)))
          (by fun_prop)))

lemma fresh_run (A : ℕ → Program (E × R) d q E) (V : Point d → ℝ) (n : ℕ)
    (p : E × (Fin n → R)) :
    (fresh A n).run V p=stateRun id (fun j => (A j).run V) n p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fresh,seq_run,seedMap_run,stateRun]
    rw [ih]

lemma fresh_law (A : ℕ → Program (E × R) d q E) {V : Point d → ℝ}
    (hV : Measurable (firstOrderReply V)) (μ : Measure E) (γ : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] (n : ℕ) :
    (μ.prod (Measure.pi (fun _ : Fin n => γ))).map ((fresh A n).run V)=
      stateLaw μ γ (fun j => (A j).run V) n := by
  have h := stateRun_law μ γ id measurable_id (fun j => (A j).run V)
    (fun j => (A j).measurable_run V hV) n
  simpa only [←funext (fresh_run A V n),Measure.map_id] using h

end LogConcaveSampling.OracleCompiler.Program

end
end

end OAI
