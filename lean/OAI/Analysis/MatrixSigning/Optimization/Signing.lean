import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.NormalizedRun
import OAI.Analysis.MatrixSigning.Optimization.Coordinates

namespace OAI

open Matrix

namespace CurrentKS.RationalInput
open CurrentKS.RationalFace CurrentKS.RationalSDP
open scoped BigOperators

def signing (x : Input) : List Bool :=
  if (indices x).length=0 then List.replicate x.N true else
    let s := normalizedRun (normalizedCoordinates x)
    List.ofFn fun i => decide (orientation x i*extend (index x) (fun _ => 1) s i=1)

lemma orientation_abs (x : Input) (i : Fin x.N) : |orientation x i|=1 := by
  unfold orientation
  split_ifs <;> norm_num

end CurrentKS.RationalInput

end OAI
