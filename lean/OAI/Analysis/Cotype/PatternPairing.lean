import OAI.Analysis.Cotype.WalshFrameOrbit
import OAI.Analysis.Cotype.FrameFeasibility
import OAI.Analysis.Cotype.GrowthTuplePairing

namespace OAI

noncomputable section

namespace Cotype

structure SignFrameRealization (n r s : ℕ) (S : Fin r × Fin s → Bool) where
  U : Fin r → Cube n
  V : Fin s → Cube n
  U_frame : BinaryFrame U
  V_frame : BinaryFrame V
  pairing : ∀ i j, character (V j) (U i) = sign (S (i,j))

def signFrameChoice {n r s : ℕ} (hn : r+s ≤ n) (S : Fin r × Fin s → Bool) :
    SignFrameRealization n r s S := by
  apply Classical.choice
  obtain ⟨U,V,hU,hV,hUV⟩ := sign_frames_feasible hn S
  exact ⟨⟨U,V,hU,hV,hUV⟩⟩

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {T : X →L[ℝ] Y} {n m : ℕ} {Dg Df : ℝ}
namespace GrowthPairingData
variable (d : GrowthPairingData T n m Dg Df)

def patternPairing (hn : m+m ≤ n) (S : Fin m × Fin m → Bool) (ε δ : Cube m) : ℝ :=
  let q := signFrameChoice hn S
  d.tuplePairing q.U q.V ε δ

def patternPrimal (hn : m+1 ≤ n) (s : Cube m) (ε : Cube m) : ℝ :=
  let q := signFrameChoice hn (fun ij : Fin m × Fin 1 => s ij.1)
  d.primalSlice q.U (q.V 0) ε

def patternDual (hn : 1+m ≤ n) (s : Cube m) (δ : Cube m) : ℝ :=
  let q := signFrameChoice hn (fun ij : Fin 1 × Fin m => s ij.2)
  d.dualSlice (q.U 0) q.V δ

theorem patternPairing_eq (hn : m+m ≤ n) (S : Fin m × Fin m → Bool)
    (U V : Fin m → Cube n) (hU : BinaryFrame U) (hV : BinaryFrame V)
    (hS : ∀ i j, character (V j) (U i) = sign (S (i,j))) (ε δ : Cube m) :
    d.patternPairing hn S ε δ = d.tuplePairing U V ε δ := by
  let q := signFrameChoice hn S
  obtain ⟨g,hgU,hgV⟩ := walsh_paired_frames_orbit q.U U q.V V q.U_frame hU q.V_frame hV
    (fun i j => (q.pairing i j).trans (hS i j).symm)
  have h := d.tuplePairing_equivariant g q.U q.V ε δ
  rw [show (fun i => primalSymmetry g (q.U i)) = U from funext hgU,
      show (fun j => dualSymmetry g (q.V j)) = V from funext hgV] at h
  exact h.symm

theorem patternPrimal_eq (hn : m+1 ≤ n) (s : Cube m)
    (U : Fin m → Cube n) (v : Cube n) (hU : BinaryFrame U)
    (hv : BinaryFrame (fun _ : Fin 1 => v))
    (hs : ∀ i, character v (U i) = sign (s i)) (ε : Cube m) :
    d.patternPrimal hn s ε = d.primalSlice U v ε := by
  let q := signFrameChoice hn (fun ij : Fin m × Fin 1 => s ij.1)
  obtain ⟨g,hgU,hgv⟩ := walsh_paired_frames_orbit q.U U q.V (fun _ : Fin 1 => v)
    q.U_frame hU q.V_frame hv (fun i j => (q.pairing i j).trans (hs i).symm)
  have h := d.primalSlice_equivariant g q.U (q.V 0) ε
  rw [show (fun i => primalSymmetry g (q.U i)) = U from funext hgU, hgv 0] at h
  exact h.symm

theorem patternDual_eq (hn : 1+m ≤ n) (s : Cube m)
    (u : Cube n) (V : Fin m → Cube n) (hu : BinaryFrame (fun _ : Fin 1 => u))
    (hV : BinaryFrame V) (hs : ∀ j, character (V j) u = sign (s j)) (δ : Cube m) :
    d.patternDual hn s δ = d.dualSlice u V δ := by
  let q := signFrameChoice hn (fun ij : Fin 1 × Fin m => s ij.2)
  obtain ⟨g,hgu,hgV⟩ := walsh_paired_frames_orbit q.U (fun _ : Fin 1 => u) q.V V
    q.U_frame hu q.V_frame hV (fun i j => (q.pairing i j).trans (hs j).symm)
  have h := d.dualSlice_equivariant g (q.U 0) q.V δ
  rw [hgu 0, show (fun j => dualSymmetry g (q.V j)) = V from funext hgV] at h
  exact h.symm

theorem patternPairing_primal_moment (hn : m+m ≤ n) (hd : 1+m ≤ n)
    (S : Fin m × Fin m → Bool) (δ : Cube m) (i : Fin m) :
    moment ℝ (fun ε => d.patternPairing hn S ε δ) i =
      (1/(2*24*Dg*Real.sqrt m)) * d.patternDual hd (fun j => S (i,j)) δ := by
  let q := signFrameChoice hn S
  change moment ℝ (fun ε => d.tuplePairing q.U q.V ε δ) i = _
  rw [d.tuplePairing_primal_moment]
  rw [d.patternDual_eq hd (fun j => S (i,j)) (q.U i) q.V
    (q.U_frame.comp (fun _ : Fin 1 => i) (fun _ _ _ => Subsingleton.elim _ _))
    q.V_frame (q.pairing i)]

theorem patternPairing_dual_moment (hn : m+m ≤ n) (hp : m+1 ≤ n)
    (S : Fin m × Fin m → Bool) (ε : Cube m) (j : Fin m) :
    moment ℝ (fun δ => d.patternPairing hn S ε δ) j =
      (1/(2*24*Df*Real.sqrt m)) * d.patternPrimal hp (fun i => S (i,j)) ε := by
  let q := signFrameChoice hn S
  change moment ℝ (fun δ => d.tuplePairing q.U q.V ε δ) j = _
  rw [d.tuplePairing_dual_moment]
  rw [d.patternPrimal_eq hp (fun i => S (i,j)) q.U (q.V j) q.U_frame
    (q.V_frame.comp (fun _ : Fin 1 => j) (fun _ _ _ => Subsingleton.elim _ _))
    (fun i => q.pairing i j)]

theorem patternPrimal_moment (hn : m+1 ≤ n) (s : Cube m) (i : Fin m) :
    moment ℝ (d.patternPrimal hn s) i =
      (1/(2*24*Dg*Real.sqrt m)) * (d.gamma * sign (s i)) := by
  let q := signFrameChoice hn (fun ij : Fin m × Fin 1 => s ij.1)
  change moment ℝ (d.primalSlice q.U (q.V 0)) i = _
  rw [d.primalSlice_moment, q.pairing]

theorem patternDual_moment (hn : 1+m ≤ n) (s : Cube m) (j : Fin m) :
    moment ℝ (d.patternDual hn s) j =
      (1/(2*24*Df*Real.sqrt m)) * (d.gamma * sign (s j)) := by
  let q := signFrameChoice hn (fun ij : Fin 1 × Fin m => s ij.2)
  change moment ℝ (d.dualSlice (q.U 0) q.V) j = _
  rw [d.dualSlice_moment, q.pairing]

end GrowthPairingData
end Cotype

end

end OAI
