import Mathlib

namespace OAI

noncomputable section

namespace SingularEdgeOne

def fieldP (p b r : ℝ) : ℝ :=
  (1 / 4 : ℝ) * (2 * r) ^ (p - 1) * (p + (2 - p) * (b / r) ^ 2)

def fieldQ (p b r : ℝ) : ℝ := (2 * r) ^ (p - 2) * b

def edgeU (p w l : ℝ) : ℝ :=
  (1 / 4 : ℝ) * (2 * l) ^ (p - 1) * ((2 - p) * (w / l) ^ 2 + p / 4)

def edgeV (p w l : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (2 * l) ^ (p - 1) * (w / l)

def ceiling (p b : ℝ) : ℝ := b ^ 2 * (p / 4 + (2 - p) * b ^ 2)

def edgeCeiling (p w : ℝ) : ℝ := w ^ 2 * ((2 - p) * w ^ 2 + p / 16)

def coefficient (p : ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ 4 * (2 * p ^ 2 + 10 * p - 13) / (30 * p)

def edgeA (p : ℝ) : ℝ := (2 - p) / 2560 + p / 1536

def edgeG (p : ℝ) : ℝ :=
  (1 / (16 * p)) *
    ((((2 - p) ^ 2 / 80 + p * (2 - p) / 24 + p ^ 2 / 16) / 16) + 1 / 96)

def edgeEnergy (p w l : ℝ) : ℝ :=
  (edgeU p w l ^ 2 + (1 / 2 : ℝ) * edgeV p w l ^ 2) / 2

def angularEnergy (p R : ℝ) : ℝ :=
  ((2 - p) * R ^ 2 + p / 4) ^ 2 / 32 + R ^ 2 / 16

def FlexibleCutoff (p : ℝ) (rho padding : ℝ → ℝ) : Prop :=
  (∀ᶠ c : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < rho c ∧ 0 < padding c) ∧
  Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0)) rho (fun c : ℝ => c) ∧
  Filter.Tendsto (fun c : ℝ => c * (rho c) ^ (p - 2))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
  Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0)) padding (fun c : ℝ => c ^ 2) ∧
  Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0)) (fun c : ℝ => c ^ 3) padding

end SingularEdgeOne

end

end OAI
