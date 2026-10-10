import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalBands

namespace OAI

namespace SharpRamseyFive.Marking
open Filter Real
noncomputable section
def bandLo (σ width : ℝ) (b : Fin 7) : ℝ :=
  if b.val%2=0 then ((b.val/2+1:ℕ):ℝ)*σ-width else σ
def bandHi (σ width : ℝ) (b : Fin 7) : ℝ :=
  if b.val%2=0 then ((b.val/2+1:ℕ):ℝ)*σ+width else 4*σ
lemma band_endpoints {σ width u : ℝ} {b : Fin 7}
    (_hσ : 0≤σ) (_hw : 0≤width) (hu : σ≤u ∧ u≤4*σ)
    (hb : BandCondition σ width u b) :
    bandLo σ width b≤u ∧ u≤bandHi σ width b := by
  unfold bandLo bandHi BandCondition at *
  split_ifs at * with he
  · have hh:=abs_le.mp hb
    constructor <;> linarith
  · exact hu
lemma band_lo_le_hi {σ width : ℝ} {b : Fin 7} (hσ : 0≤σ) (hw : 0≤width) :
    bandLo σ width b≤bandHi σ width b := by
  unfold bandLo bandHi
  split_ifs <;> linarith
lemma band_gap_closed {σ width : ℝ} {b : Fin 7} (hb : b.val%2=0) :
    bandHi σ width b-bandLo σ width b=2*width := by simp [bandHi,bandLo,hb];ring
lemma band_gap_open {σ width : ℝ} {b : Fin 7} (hb : b.val%2≠0) :
    bandHi σ width b-bandLo σ width b=3*σ := by simp [bandHi,bandLo,hb];ring
end
end SharpRamseyFive.Marking

end OAI
