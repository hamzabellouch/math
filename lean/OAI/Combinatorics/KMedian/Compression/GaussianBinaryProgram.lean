import Mathlib
import OAI.Combinatorics.KMedian.Binary.BooleanLoopFrom
import OAI.Combinatorics.KMedian.Compression.GaussianListRun
import OAI.Combinatorics.KMedian.Compression.GaussianInputBounds

namespace OAI


                                             
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Polynomial

def Input.result (I : Input) : Row := kernelList I.rows I.cols I.data

noncomputable def startProgram : PolyProgram Input.encode eState (fun I : Input => desc I.rows I.cols I.data []) := by
  let raw : PolyProgram Input.encode edata Input.raw := (identity edata).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  exact ((raw.fanout (constant Input.encode efs [])).comp (injectLeft eUp ed)).congr _ (fun _ => rfl)

noncomputable def kernelProgram : PolyProgram Input.encode er Input.result :=
  loopFrom startProgram bodyProgram Input.result (2*X+2) statePolynomial (fun I => by
    obtain ⟨t,ht,hrun⟩ := full_run I.encode.length I.encode.length
      (residualHeight I.encode.length I.encode.length I.encode.length)
      (returnHeight I.encode.length I.encode.length I.encode.length)
      I.rows I.cols I.data I.underdetermined (input_audit I)
    refine ⟨t,?_,?_⟩
    · have hr := (input_bounds I).1
      simp only [eval_add,eval_mul,eval_ofNat,eval_X]
      omega
    · simpa only [statePolynomial_eval,Input.result] using hrun)

 theorem kernel_binary_polytime :
    Nonempty (Turing.TM2ComputableInPolyTime Input.encode er Input.result) := ⟨kernelProgram.stock⟩

 theorem kernel_finite_work : ∀ k : kernelProgram.machine.K, Finite (kernelProgram.machine.tm.Γ k) :=
  kernelProgram.finite_work
end MetricKMedian.Gaussian.ListOperation
end

end OAI
