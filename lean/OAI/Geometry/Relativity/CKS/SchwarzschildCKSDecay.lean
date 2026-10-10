import OAI.Geometry.Relativity.CKS.SchwarzschildRadialDecay
import OAI.Geometry.Relativity.CKS.SchwarzschildCKSAlgebra

namespace OAI

noncomputable section
open Set Filter CKSLorentz CKSMixedGeometry CKSAngularSlice
open scoped ContDiff Topology
namespace CKSSchwarzschild

def compactDenominator (m s : ℝ) : ℝ :=
  letI := CKSBoundarySurface.two_atLeastTwo
  (1+s^2-2*m*s^3)*(1+s^2)
def compactCoefficient (m s : ℝ) : ℝ :=
  letI := CKSBoundarySurface.two_atLeastTwo
  2*m / compactDenominator m s
def compactRemainder (m s : ℝ) : ℝ :=
  letI := CKSBoundarySurface.two_atLeastTwo
  2*m*s*(-2+2*m*s-s^2+2*m*s^3)/compactDenominator m s
lemma compactDenominator_pos {m s : ℝ} (hm : 0 < m) (hs : s ∈ Icc 0 (1/(4*m+4))) :
    0 < compactDenominator m s := by
  have hD : 0 < 4*m+4 := by positivity
  have hms := (le_div_iff₀ hD).mp hs.2
  have hmss : 0 ≤ 1-2*m*s := by nlinarith
  have hp : 0 < 1+s^2-2*m*s^3 := by nlinarith [mul_nonneg (sq_nonneg s) hmss]
  exact mul_pos hp (by positivity)
lemma compactCoefficient_smooth {m s : ℝ} (hm : 0 < m) (hs : s ∈ Icc 0 (1/(4*m+4))) :
    ContDiffAt ℝ ∞ (compactCoefficient m) s := by
  exact contDiffAt_const.div (by unfold compactDenominator; fun_prop)
    (compactDenominator_pos hm hs).ne'
lemma compactRemainder_smooth {m s : ℝ} (hm : 0 < m) (hs : s ∈ Icc 0 (1/(4*m+4))) :
    ContDiffAt ℝ ∞ (compactRemainder m) s := by
  unfold compactRemainder
  apply ContDiffAt.div
  · fun_prop
  · unfold compactDenominator; fun_prop
  · exact (compactDenominator_pos hm hs).ne'
lemma tail_inverse_small {m r : ℝ} (hm : 0 < m) (hr : 4*m+4 ≤ r) :
    r⁻¹ ∈ Icc 0 (1/(4*m+4)) := by
  have hD : 0 < 4*m+4 := by positivity
  exact ⟨inv_nonneg.mpr (hD.le.trans hr),by simpa only [one_div] using (inv_le_inv₀ (hD.trans_le hr) hD).mpr hr⟩
lemma radialCoefficient_id {m r : ℝ} (hm : 0 < m) (hr : 4*m+4 ≤ r) :
    radialCoefficient m r = compactCoefficient m r⁻¹/r^5 ∧
    radialCoefficient m r - 2*m/r^5 = compactRemainder m r⁻¹/r^6 := by
  have hrp : 0 < r := lt_of_lt_of_le (by positivity) hr
  have hd : 0 < 1+r^2-2*m/r := by
    have hmr : 2*m < r := by linarith
    have h := (div_lt_one hrp).mpr hmr
    nlinarith [sq_nonneg r]
  have hs := tail_inverse_small hm hr
  have hc : compactDenominator m r⁻¹ ≠ 0 := (compactDenominator_pos hm hs).ne'
  have h1 : 1+r^2 ≠ 0 := by positivity
  have hpoly : r+r^3-2*m ≠ 0 := by
    have : 0 < (1+r^2-2*m/r)*r := mul_pos hd hrp
    have he : (1+r^2-2*m/r)*r = r+r^3-2*m := by field_simp
    rw [he] at this
    exact this.ne'
  have hpoly' : r+r^3-m*2 ≠ 0 := by simpa only [mul_comm m 2] using hpoly
  constructor
  · unfold radialCoefficient compactCoefficient compactDenominator
    field_simp (disch := first | assumption | positivity | (convert hpoly using 1; ring))
    ring
  · unfold radialCoefficient compactRemainder compactDenominator
    field_simp (disch := first | assumption | positivity | (convert hpoly using 1; ring))
    ring

lemma radial_decay {m : ℝ} (hm : 0 < m) (θ : Angle) :
    SourceRemainderOn 3 6 (angularRadialTail (4*m+4) (Metric.ball θ 1))
      (fun y => radialCoefficient m (y 0)-2*m/(y 0)^5) ∧
    SourceRemainderOn 2 5 (angularRadialTail (4*m+4) (Metric.ball θ 1))
      (fun y => radialCoefficient m (y 0)) := by
  have hR : 0 < 4*m+4 := by positivity
  have hδ : 0 < 1/(4*m+4) := one_div_pos.mpr hR
  have hδR : 1/(1/(4*m+4)) ≤ 4*m+4 := by simp
  constructor
  · apply (compactified_radial_source 3 6 hδ hR hδR θ (fun s hs => compactRemainder_smooth hm hs)).congrOn
      (angularRadialTail_open _ Metric.isOpen_ball)
    intro y hy
    exact (radialCoefficient_id hm hy.1.le).2.symm
  · apply (compactified_radial_source 2 5 hδ hR hδR θ (fun s hs => compactCoefficient_smooth hm hs)).congrOn
      (angularRadialTail_open _ Metric.isOpen_ball)
    intro y hy
    exact (radialCoefficient_id hm hy.1.le).1.symm
end CKSSchwarzschild

end

end OAI
