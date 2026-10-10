import OAI.NumberTheory.JointDickman.Analysis.LaplacePolynomial

namespace OAI

/-! # Fixed-order Watson estimate for a locally controlled Taylor remainder -/
namespace JointDickman
open MeasureTheory Set Filter Asymptotics Finset
open scoped Topology

theorem laplace_taylor_isBigO {z η C : ℝ} (hz1 : z < 1) (hη : 0 < η) (hC : 0 ≤ C)
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f (volume.restrict (Ioc 0 η)))
    (a : ℕ → ℂ) (H : ℕ)
    (hb : ∀ t ∈ Ioc 0 η, ‖f t - ∑ j ∈ range (H+1), a j*(t:ℂ)^j‖ ≤ C*t^(H+1)) :
    (fun L : ℝ => (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) • f t) -
      ∑ j ∈ range (H+1), (L^(z-j-1)*Real.Gamma ((j:ℝ)+1-z)) • a j)
      =O[atTop] (fun L => L^(z-H-2)) := by
  let p : ℝ → ℂ := fun t => ∑ j ∈ range (H+1), a j*(t:ℂ)^j
  have hpmeas : AEStronglyMeasurable p (volume.restrict (Ioc 0 η)) := by
    have hpcont : Continuous p := by unfold p; fun_prop
    exact hpcont.aestronglyMeasurable
  have hR : (fun L : ℝ => ∫ t : ℝ in Ioc 0 η,
      (t^(-z)*Real.exp (-(L*t))) • (f t-p t)) =O[atTop] (fun L => L^(z-H-2)) := by
    refine isBigO_iff.mpr ⟨C*Real.Gamma ((H:ℝ)+2-z),?_⟩
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    have hh := laplace_remainder_bound hz1 hL hC (H+1) (fun t => f t-p t) hb
    rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hL _)]
    convert hh using 1; push_cast; ring_nf
  have hP := (laplace_polynomial_cutoff_error hz1 hη a H (z-H-2)).isBigO
  apply (hR.add hP).congr' _ (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  have hr := laplace_weighted_integrable hz1 hL (H+1) (fun t => f t-p t)
    (hf.sub hpmeas) hb
  have hp := laplace_polynomial_integrable (η := η) hz1 hL a H
  have he : (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) • f t) =
      (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) • (f t-p t)) +
      (∫ t : ℝ in Ioc 0 η, (t^(-z)*Real.exp (-(L*t))) • p t) := by
    rw [← integral_add hr hp]
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => by dsimp only; rw [smul_sub]; dsimp only [p]; abel)
  rw [he]
  dsimp only [p]
  abel

end JointDickman

end OAI
