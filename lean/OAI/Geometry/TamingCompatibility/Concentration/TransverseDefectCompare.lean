import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.PlaneTransverseGraph

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
open RadialPotential
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma transverse_graph_sq_bound (K L : V →L[ℝ] V) (hK : ∀ v, K (K v) = -v)
    (hL : ∀ v, L (L v) = -v) (z a : V) (ha : a ≠ 0)
    {m C : ℝ} (hm : 0 < m) (hma : m ≤ ‖hermitianGraph K a‖)
    (_hC : 0 ≤ C) (hKL : ‖K-L‖ ≤ C*‖z‖) :
    ‖transverse (first a) (second a (L a)) z‖^2 ≤
      (2/m^2)*hermitianDefect K z a + (2*‖hermitianGraph K‖^2*C^2)*‖z‖^4 := by
  let D := hermitianDefect K z a
  have hD : 0 ≤ D := hermitianDefect_nonneg K hK z a
  have hbase := transverse_graph_bound K L hK hL z a ha
  have h₁ : Real.sqrt D/‖hermitianGraph K a‖ ≤ Real.sqrt D/m :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hm hma
  have h₂ : ‖hermitianGraph K z‖*‖K-L‖ ≤ (‖hermitianGraph K‖*C)*‖z‖^2 := by
    have hh := mul_le_mul ((hermitianGraph K).le_opNorm z) hKL (norm_nonneg _) (by positivity)
    nlinarith
  have hh : ‖transverse (first a) (second a (L a)) z‖ ≤ Real.sqrt D/m+(‖hermitianGraph K‖*C)*‖z‖^2 :=
    hbase.trans (add_le_add h₁ h₂)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hs : (Real.sqrt D/m)^2 = D/m^2 := by rw [div_pow,Real.sq_sqrt hD]
  have hcross := sq_nonneg (Real.sqrt D/m-(‖hermitianGraph K‖*C)*‖z‖^2)
  change _ ≤ (2/m^2)*D+_
  rw [div_mul_eq_mul_div]
  have he : 2*D/m^2 = 2*(D/m^2) := by ring
  rw [he]
  nlinarith

lemma defect_quotient_radius_compare {d t g B : ℝ} (hd : 0 ≤ d)
    (ht : 0 ≤ t) (hg : 0 ≤ g) (htg : t ≤ g) (hgt : g ≤ B*t)
    (hz : t = 0 → d = 0) : d/t^4 ≤ B^4*(d/g^4) := by
  by_cases ht0 : t = 0
  · simp [ht0,hz ht0]
  by_cases hg0 : g = 0
  · have : t = 0 := by linarith
    exact (ht0 this).elim
  · have ht4 : 0 < t^4 := pow_pos (lt_of_le_of_ne ht (Ne.symm ht0)) 4
    have hg4 : 0 < g^4 := pow_pos (lt_of_le_of_ne hg (Ne.symm hg0)) 4
    apply (div_le_iff₀ ht4).mpr
    rw [mul_assoc,div_mul_eq_mul_div,← mul_div_assoc]
    apply (le_div_iff₀ hg4).mpr
    have hp := pow_le_pow_left₀ hg hgt 4
    rw [mul_pow] at hp
    nlinarith
end TamingCompatibility.PlaneVariation

end
end

end OAI
