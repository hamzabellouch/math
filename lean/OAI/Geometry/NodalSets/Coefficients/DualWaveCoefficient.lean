import OAI.Geometry.NodalSets.Elliptic.Logarithm

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

def dualWaveCoefficient (N : ℝ) (V : Coord → ℂ) (S : ℝ) (x : Coord) (b : ℝ) (v : Coord) : ℂ :=
  (Real.exp (-N*S):ℂ)*((b:ℂ)*V x+(N:ℂ)⁻¹*fderiv ℝ V x v)

lemma dualWaveCoefficient_factor (N : ℝ) (V : Coord → ℂ) (S : ℝ) (x : Coord)
    (b : ℝ) (v : Coord) (hn : V x ≠ 0) :
    dualWaveCoefficient N V S x b v = (Real.exp (-N*S):ℂ)*V x*((b:ℂ)+normalizedLogJet N V x v) := by
  unfold dualWaveCoefficient normalizedLogJet
  field_simp [hn]

lemma real_log_product_le_coefficient (N : ℝ) (V : Coord → ℂ) (S : ℝ) (x : Coord)
    (b : ℝ) (v : Coord) (hn : V x ≠ 0) :
    (‖V x‖*Real.exp (-N*S))*|b+(normalizedLogJet N V x v).re| ≤
      ‖dualWaveCoefficient N V S x b v‖ := by
  rw [dualWaveCoefficient_factor N V S x b v hn,norm_mul,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  have h := Complex.abs_re_le_norm ((b:ℂ)+normalizedLogJet N V x v)
  simp only [Complex.add_re,Complex.ofReal_re] at h
  have hh := mul_le_mul_of_nonneg_left h (mul_nonneg (norm_nonneg (V x)) (Real.exp_pos (-N*S)).le)
  simpa only [mul_comm (Real.exp (-N*S)) ‖V x‖] using hh

end
end Yau.Geometry

end OAI
