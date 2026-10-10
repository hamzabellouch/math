import OAI.Geometry.RCD.Harmonic.HoleDefectCharge

namespace OAI

/-! # Hole radii controlled by the mass outside the good set -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.hole_mass_charge {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {ι : Type*} [Fintype ι]
    {p : X} {R C : ℝ} (hR : 0 < R) (hC : 0 < C) (hcurv : -1 ≤ K*(2*R)^2)
    {Ω : Set X} (hfin : hausdorff n X Ω ≠ ⊤)
    {z : ι → X} {r : ι → ℝ} (hz : ∀ i, dist (z i) p ≤ R)
    (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i/(4*C) ≤ R)
    (hsub : ∀ i, ball (z i) (r i/(4*C)) ⊆ Ω)
    (hdisj : Pairwise (fun i j =>
      Disjoint (ball (z i) (r i/(4*C))) (ball (z j) (r j/(4*C))))) :
    (∑ i, (r i)^n) ≤
      ((4*C)^n*(Real.cosh 1^(n-1)*2^n)*R^n/(hausdorff n X).real (ball p R))*
        (hausdorff n X).real Ω := by
  have hf : IntegrableOn (fun _ : X => (1:ℝ)) Ω (hausdorff n X) :=
    integrableOn_const (C := (1:ℝ)) hfin
  have hh := hX.hole_defect_charge hn hR (show (0:ℝ)<1 by norm_num) hcurv hf
    (Filter.Eventually.of_forall (fun _ => zero_le_one)) hz
    (fun i => div_pos (hr i) (by positivity : 0 < 4*C)) (fun _ => le_rfl) hrR hsub hdisj
    (fun _ => by simp [integral_const,Measure.real])
  simp only [integral_const,smul_eq_mul,mul_one,one_mul,Measure.real,Measure.restrict_apply_univ] at hh
  have hscaled := mul_le_mul_of_nonneg_left hh (show 0 ≤ (4*C)^n by positivity)
  have heq : (4*C)^n*(∑ i, (r i/(4*C))^n) = ∑ i, (r i)^n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow]
    field_simp
  rw [heq] at hscaled
  change (∑ i, (r i)^n) ≤ _
  convert hscaled using 1
  dsimp only [Measure.real]
  ring

end RegularPointCoordinates

end

end OAI
