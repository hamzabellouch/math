import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketFamily
import OAI.Analysis.LipschitzHilbert.Fourier.SchwartzDilation
import OAI.Analysis.LipschitzHilbert.Estimates.HorizontalDilation

namespace OAI

/-! Normalize a top's horizontal length while retaining its packet
lattice and its original analyzing coefficients. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert

theorem lineEnvelope_horizontalDilation (a l r x : ℝ) (n : ℕ) (hr : r ≠ 0) :
    lineEnvelope (a/r) (l/r) n x = lineEnvelope a l n (r*x) := by
  unfold lineEnvelope
  congr 3
  field_simp

namespace PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

def horizontalRescale (P : PlanarPacketFamily N κ ι) (r : ℝ) (hr : 0 < r) :
    PlanarPacketFamily N κ ι where
  baseX := P.baseX/r
  baseZ := P.baseZ
  topLength := P.topLength/r
  width := P.width
  constant := P.constant
  topLength_pos := div_pos P.topLength_pos hr
  width_pos := P.width_pos
  constant_pos := P.constant_pos
  site := P.site
  site_injective := P.site_injective
  wave := fun j i k y => schwartzDilation (P.wave j i k y) r hr.ne'
  wave_measurable := by
    intro j i k
    exact (P.wave_measurable j i k).comp
      ((measurable_fst).prodMk (measurable_const.mul measurable_snd))
  wave_bound := by
    intro j i k y x
    have hcx : P.baseX/r+(P.topLength/r/(2:ℝ)^j.val)*(P.site j i).1 =
        (P.baseX+(P.topLength/(2:ℝ)^j.val)*(P.site j i).1)/r := by ring
    have hlen : P.topLength/r/(2:ℝ)^j.val = (P.topLength/(2:ℝ)^j.val)/r := by ring
    rw [hcx,hlen,lineEnvelope_horizontalDilation _ _ r _ _ hr.ne']
    exact P.wave_bound j i k y (r*x)

@[simp] theorem horizontalRescale_length (P : PlanarPacketFamily N κ ι) (r : ℝ) (hr : 0 < r) (j : Fin N) :
    (P.horizontalRescale r hr).length j = P.length j/r := by
  unfold horizontalRescale length
  ring

@[simp] theorem horizontalRescale_centerX (P : PlanarPacketFamily N κ ι)
    (r : ℝ) (hr : 0 < r) (j : Fin N) (i : ι j) :
    (P.horizontalRescale r hr).centerX j i = P.centerX j i/r := by
  simp only [centerX,horizontalRescale_length]
  change P.baseX/r+P.length j/r*(P.site j i).1 = _
  ring

@[simp] theorem horizontalRescale_centerZ (P : PlanarPacketFamily N κ ι)
    (r : ℝ) (hr : 0 < r) (j : Fin N) (i : ι j) :
    (P.horizontalRescale r hr).centerZ j i = P.centerZ j i := rfl

@[simp] theorem horizontalRescale_wave (P : PlanarPacketFamily N κ ι)
    (r : ℝ) (hr : 0 < r) (j : Fin N) (i : ι j) (k : κ) (y x : ℝ) :
    (P.horizontalRescale r hr).wave j i k y x = P.wave j i k y (r*x) := rfl

theorem horizontalRescale_mainCoefficient (P : PlanarPacketFamily N κ ι)
    (r : ℝ) (hr : 0 < r) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (j : Fin N) (i : ι j) :
    (P.horizontalRescale r hr).mainCoefficient d
      (fun z => v (z.1,r*z.2)) (fun z => g (z.1,r*z.2)) j i = P.mainCoefficient d v g j i := by
  ext k
  simp only [mainCoefficient,analyzingCoefficient,WithLp.ofLp_toLp]
  change ((↑((P.horizontalRescale r hr).length j*P.width) : ℂ)⁻¹)*
      (∫ z, g (z.1,r*z.2) k * conj ((P.horizontalRescale r hr).selectedWave d
        (fun z => v (z.1,r*z.2)) ⟨j,i⟩ k z) ∂volume.prod volume) = _
  have heq : (fun z : ℝ × ℝ => g (z.1,r*z.2) k * conj
      ((P.horizontalRescale r hr).selectedWave d (fun z => v (z.1,r*z.2)) ⟨j,i⟩ k z)) =
      (fun z => (fun w : ℝ × ℝ => g w k*conj (P.selectedWave d v ⟨j,i⟩ k w))
        (referenceHorizontalDilation r hr.ne' z)) := by
    funext z
    rfl
  have hint := integral_referenceHorizontalDilation
    (fun w : ℝ × ℝ => g w k*conj (P.selectedWave d v ⟨j,i⟩ k w)) r hr.ne'
  rw [heq,hint,horizontalRescale_length,abs_of_pos (inv_pos.mpr hr)]
  change ((↑((P.length j/r)*P.width) : ℂ)⁻¹)*(r⁻¹ • _) =
    ((↑(P.length j*P.width) : ℂ)⁻¹)*_
  rw [Complex.real_smul]
  push_cast
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp [hrC]
  rfl

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI
