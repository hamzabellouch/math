import Mathlib
import OAI.Geometry.PrescribedPotential.ComplexKernel
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedRicci.BoundedSmoothPoisson
import OAI.Geometry.PrescribedRicci.KahlerCauchySchwarz
import OAI.Geometry.PrescribedRicci.KahlerL2Comparison
import OAI.Geometry.PrescribedRicci.MongeAmpereEnergy

namespace OAI

/-! Kahler Poisson L2. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped SchwartzMap ContDiff Classical
namespace Anticanonical.SourceSmooth
open GlobalElliptic
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X}
namespace KaehlerMetric

lemma integral_const (g : KaehlerMetric A) (c : ℝ) :
    g.integral (fun _ => c) = c * g.integral (fun _ => 1) := by
  simpa only [mul_one] using g.integral_const_mul c (fun _ => 1)

lemma volume_pos [Nonempty X] (g : KaehlerMetric A) : 0 < g.integral (fun _ => 1) := by
  obtain ⟨S,⟨D⟩⟩ := exists_gluingData g
  obtain ⟨C,B,hC,hB,hbound⟩ := D.localizers.kahler_L2_comparison g
  have hn : D.localizers.embed 0 (Smooth.const 1) ≠ 0 := by
    intro hh
    have he : Smooth.const (A := A) 1 = 0 := D.localizers.embed_injective 0 (by simpa using hh)
    have hx := congrArg (fun f : Smooth A => f (Classical.arbitrary X)) he
    exact one_ne_zero hx
  have hnorm : 0 < ‖D.localizers.embed 0 (Smooth.const 1)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  have hb := (hbound (Smooth.const 1)).1
  change ‖D.localizers.embed 0 (Smooth.const 1)‖ ^ 2 ≤ C * g.integral (fun _ => ‖(1 : ℂ)‖ ^ 2) at hb
  simp only [norm_one, one_pow] at hb
  exact (mul_pos_iff_of_pos_left hC).mp (hnorm.trans_le hb)

variable [ConnectedSpace X]

 

theorem exists_meanZero_poisson_L2 (g : KaehlerMetric A) : ∃ K : ℝ, 0 < K ∧
    ∀ f : SmoothRealFunction A, g.integral f.value = 0 → ∃ u : SmoothRealFunction A,
      (g.laplacian u).value = f.value ∧
      g.integral (fun x => u.value x ^ 2) ≤ K * g.integral (fun x => f.value x ^ 2) := by
  obtain ⟨S,⟨D⟩⟩ := exists_gluingData g
  obtain ⟨C,B,hC,hB,hbound⟩ := D.localizers.kahler_L2_comparison g
  obtain ⟨Q,hQ,hpoisson⟩ := D.exists_complex_poisson_bounded
  let K := 1 + B * Q ^ 2 * C
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,fun f hf => ?_⟩
  obtain ⟨v,c,hv,hvn⟩ := hpoisson (Smooth.ofReal f)
  let u := v.part Complex.reCLM
  have he (x : X) : (g.laplacian u).value x = f.value x + c.re := by
    rw [← complexL_re, hv, Smooth.add_apply, Complex.add_re, Smooth.ofReal_apply, Complex.ofReal_re]
    rfl
  have hz : c.re = 0 := by
    have hi := g.integral_laplacian u
    rw [show (g.laplacian u).value = (fun x => f.value x + c.re) from funext he,
      g.integral_add f.continuous continuous_const, hf, zero_add, g.integral_const] at hi
    exact (mul_eq_zero.mp hi).resolve_right (ne_of_gt g.volume_pos)
  have hI : 0 ≤ g.integral (fun x => f.value x ^ 2) := g.integral_nonneg (fun _ => sq_nonneg _)
  refine ⟨u, funext (fun x => by rw [he x,hz,add_zero]), ?_⟩
  have hr : g.integral (fun x => u.value x ^ 2) ≤ g.integral (fun x => ‖v x‖ ^ 2) := by
    apply g.integral_mono (u.continuous.pow 2) (v.continuous.norm.pow 2)
    intro x
    change (v x).re ^ 2 ≤ ‖v x‖ ^ 2
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 (Complex.abs_re_le_norm (v x))
  have hnv : ‖D.localizers.embed 0 v‖ ^ 2 ≤ Q ^ 2 * ‖D.localizers.embed 0 (Smooth.ofReal f)‖ ^ 2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hQ (norm_nonneg _))).2 hvn
  have hnf : ‖D.localizers.embed 0 (Smooth.ofReal f)‖ ^ 2 ≤ C * g.integral (fun x => f.value x ^ 2) := by
    simpa only [Smooth.ofReal_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs] using (hbound (Smooth.ofReal f)).1
  calc
    _ ≤ g.integral (fun x => ‖v x‖ ^ 2) := hr
    _ ≤ B * ‖D.localizers.embed 0 v‖ ^ 2 := (hbound v).2
    _ ≤ B * (Q ^ 2 * ‖D.localizers.embed 0 (Smooth.ofReal f)‖ ^ 2) := mul_le_mul_of_nonneg_left hnv hB.le
    _ ≤ B * (Q ^ 2 * (C * g.integral (fun x => f.value x ^ 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnf (sq_nonneg Q)) hB.le
    _ ≤ K * g.integral (fun x => f.value x ^ 2) := by dsimp [K]; nlinarith

end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI
