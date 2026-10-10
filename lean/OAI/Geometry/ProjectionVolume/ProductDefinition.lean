import OAI.Geometry.ProjectionVolume.Basic

namespace OAI

noncomputable section

namespace Paper092

def cartesianBody {r s : ℕ} (A : Set (Euclidean r)) (B : Set (Euclidean s)) :
    Set (Euclidean (r + s)) :=
  {x | WithLp.toLp 2 (fun i : Fin r => x (Fin.castAdd s i)) ∈ A ∧
    WithLp.toLp 2 (fun i : Fin s => x (Fin.natAdd r i)) ∈ B}

end Paper092

end

end OAI
