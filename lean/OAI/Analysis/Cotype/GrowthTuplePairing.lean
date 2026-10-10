import OAI.Analysis.Cotype.FrameLifts
import OAI.Analysis.Cotype.CompactMomentAssembly

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {T : X →L[ℝ] Y} {n m : ℕ} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T n m Dg Df)

abbrev amplifiedOperator (_d : GrowthPairingData T n m Dg Df) : GrowthSpace n X →L[ℝ] GrowthSpace n Y :=
  l2Amplification (l2Amplification T)

def tuplePairing (U V : Fin m → Cube n) (ε δ : Cube m) : ℝ :=
  d.Z V δ (d.amplifiedOperator (d.P U ε))

def primalSlice (U : Fin m → Cube n) (v : Cube n) (ε : Cube m) : ℝ :=
  d.y v (d.amplifiedOperator (d.P U ε))

def dualSlice (u : Cube n) (V : Fin m → Cube n) (δ : Cube m) : ℝ :=
  d.Z V δ (d.amplifiedOperator (d.x u))

theorem tuplePairing_equivariant (g : WalshSymmetry n) (U V : Fin m → Cube n) (ε δ : Cube m) :
    d.tuplePairing (fun i => primalSymmetry g (U i)) (fun j => dualSymmetry g (V j)) ε δ =
      d.tuplePairing U V ε δ := by
  unfold tuplePairing
  rw [d.P_equivariant, d.Z_equivariant]
  exact symmetry_pairing_invariant (l2Amplification (Ω := Cube (n+n)) T) g _ _

theorem primalSlice_equivariant (g : WalshSymmetry n) (U : Fin m → Cube n) (v : Cube n) (ε : Cube m) :
    d.primalSlice (fun i => primalSymmetry g (U i)) (dualSymmetry g v) ε = d.primalSlice U v ε := by
  unfold primalSlice
  rw [d.P_equivariant, ← d.y_equivariant]
  exact symmetry_pairing_invariant (l2Amplification (Ω := Cube (n+n)) T) g _ _

theorem dualSlice_equivariant (g : WalshSymmetry n) (u : Cube n) (V : Fin m → Cube n) (δ : Cube m) :
    d.dualSlice (primalSymmetry g u) (fun i => dualSymmetry g (V i)) δ = d.dualSlice u V δ := by
  unfold dualSlice
  rw [← d.x_equivariant, d.Z_equivariant]
  exact symmetry_pairing_invariant (l2Amplification (Ω := Cube (n+n)) T) g _ _

theorem tuplePairing_primal_moment (U V : Fin m → Cube n) (δ : Cube m) (i : Fin m) :
    moment ℝ (fun ε => d.tuplePairing U V ε δ) i =
      (1/(2*24*Dg*Real.sqrt m)) * d.dualSlice (U i) V δ := by
  change moment ℝ (fun ε => ((d.Z V δ).comp d.amplifiedOperator) (d.P U ε)) i = _
  rw [← moment_clm ((d.Z V δ).comp d.amplifiedOperator) (d.P U) i, d.P_moment, map_smul]
  rfl

theorem tuplePairing_dual_moment (U V : Fin m → Cube n) (ε : Cube m) (j : Fin m) :
    moment ℝ (fun δ => d.tuplePairing U V ε δ) j =
      (1/(2*24*Df*Real.sqrt m)) * d.primalSlice U (V j) ε := by
  let ev := ContinuousLinearMap.apply ℝ ℝ (d.amplifiedOperator (d.P U ε))
  change moment ℝ (fun δ => ev (d.Z V δ)) j = _
  rw [← moment_clm ev (d.Z V) j, d.Z_moment, map_smul]
  rfl

theorem primalSlice_moment (U : Fin m → Cube n) (v : Cube n) (i : Fin m) :
    moment ℝ (d.primalSlice U v) i =
      (1/(2*24*Dg*Real.sqrt m)) * (d.gamma * character v (U i)) := by
  change moment ℝ (fun ε => ((d.y v).comp d.amplifiedOperator) (d.P U ε)) i = _
  rw [← moment_clm ((d.y v).comp d.amplifiedOperator) (d.P U) i, d.P_moment, map_smul]
  change _ * d.y v (l2Amplification (l2Amplification T) (d.x (U i))) = _
  rw [d.exact_pairing]

theorem dualSlice_moment (u : Cube n) (V : Fin m → Cube n) (j : Fin m) :
    moment ℝ (d.dualSlice u V) j =
      (1/(2*24*Df*Real.sqrt m)) * (d.gamma * character (V j) u) := by
  let ev := ContinuousLinearMap.apply ℝ ℝ (d.amplifiedOperator (d.x u))
  change moment ℝ (fun δ => ev (d.Z V δ)) j = _
  rw [← moment_clm ev (d.Z V) j, d.Z_moment, map_smul]
  change _ * d.y (V j) (l2Amplification (l2Amplification T) (d.x u)) = _
  rw [d.exact_pairing]

end GrowthPairingData
end Cotype

end

end OAI
