import OAI.Geometry.NodalSets.Coefficients.DualWaveCoefficient
import OAI.Geometry.NodalSets.Elliptic.PairedJetControl

namespace OAI

namespace Yau.Geometry
noncomputable section

lemma two_coefficient_energy {ι : Type*} [Fintype ι]
    (f : ι → ℂ) (p m : ι) (s Rp Rm : ℝ) (hs : 0 ≤ s)
    (hp : s*|Rp| ≤ ‖f p‖) (hm : s*|Rm| ≤ ‖f m‖) :
    s^2*(Rp^2+Rm^2) ≤ 2*∑ i, ‖f i‖^2 := by
  classical
  have hpp := pow_le_pow_left₀ (mul_nonneg hs (abs_nonneg Rp)) hp 2
  have hmm := pow_le_pow_left₀ (mul_nonneg hs (abs_nonneg Rm)) hm 2
  rw [mul_pow,sq_abs] at hpp hmm
  have hpS : ‖f p‖^2 ≤ ∑ i, ‖f i‖^2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg ‖f i‖) (Finset.mem_univ p)
  have hmS : ‖f m‖^2 ≤ ∑ i, ‖f i‖^2 :=
    Finset.single_le_sum (fun i _ ↦ sq_nonneg ‖f i‖) (Finset.mem_univ m)
  nlinarith

end
end Yau.Geometry

end OAI
