import OAI.Geometry.PeriodicTiling.EncodingParameters

namespace OAI

namespace PeriodicTilingThree

abbrev D (p : ℕ) := p ^ 4
abbrev Residues (p : ℕ) := ZMod (p ^ 2) × ZMod (p ^ 2)

variable {p : ℕ} [NeZero p]

abbrev K (E : EncodingParameters p) (i : Channel p) := ZMod (E.r i)
abbrev P (E : EncodingParameters p) (i : Channel p) := ZMod (E.a i) × ZMod (E.b i)
abbrev Input (E : EncodingParameters p) := ∀ i : Channel p, K E i
abbrev Useful (E : EncodingParameters p) := ∀ i : Channel p, P E i

abbrev V (E : EncodingParameters p) :=
  ZMod (D p) × (∀ i : Channel p, ZMod ((E.r i) ^ 2) × P E i)

abbrev Ambient (E : EncodingParameters p) := Plane × V E
abbrev Base (E : EncodingParameters p) := Plane × Input E

abbrev Low (E : EncodingParameters p) := Input E
abbrev G (E : EncodingParameters p) := Ambient E

structure GraphOutputs (E : EncodingParameters p) where
  c : Base E → Useful E
  beta : Base E → Input E
  z : Base E → ZMod (D p)

abbrev Outputs (E : EncodingParameters p) := GraphOutputs E

end PeriodicTilingThree

end OAI
