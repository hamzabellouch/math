import OAI.Geometry.RCD.Coordinates.LocalHarmonicFrameDefect
import OAI.Geometry.RCD.Harmonic.BoundedGramTraceDefect

namespace OAI

/-! # Original harmonic frame energy controlled by its actual Gram defect -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_gram_energy_defect {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (hn : 2≤n) (hK : K≤0) (p : X)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    {R b : ℝ} (hR : 0<R) (hb : 4*R<b)
    (hH : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p b) (u i))
    (hL : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball p b),
      localGamma (hausdorff n X) hX.quadratic (u i) (u i) x≤4)
    (g : compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (q : Lp ℝ 2 (hausdorff n X)) (hq : IsWeakLaplacian (hausdorff n X) hX.quadratic g.val q)
    (d : SobolevSpace (hausdorff n X) hX.quadratic) (A : ℝ≥0)
    (hd : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic d x|≤A)
    (hqr : q =ᵐ[(hausdorff n X).restrict (ball p (2*R))]
      SobolevSpace.toLp (hausdorff n X) hX.quadratic d) :
    ∀ᵐ x ∂(hausdorff n X).restrict (ball p R),
      5*gramDefect (hausdorff n X) hX.quadratic u x≤1 →
      |localGamma (hausdorff n X) hX.quadratic g.val g.val x-
        ∑ i, (localGamma (hausdorff n X) hX.quadratic (u i) g.val x)^2|≤
      Real.sqrt (30*gramDefect (hausdorff n X) hX.quadratic u x)*
        |localGamma (hausdorff n X) hX.quadratic g.val g.val x| := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  have hsmall : ball p R⊆ball p b := ball_subset_ball (by linarith)
  have hLt (i : Fin n) : ∀ᵐ x ∂μ.restrict (ball p R), localGamma μ hQ (u i) (u i) x≤4 :=
    ae_restrict_of_ae_restrict_of_subset hsmall (hL i)
  have htr := bounded_gram_trace_defect μ hQ u hLt
  have hL' : ∀ i, ∀ᵐ x ∂μ.restrict (ball p b),
      localGamma μ hQ (u i) (u i) x≤((2:ℝ≥0):ℝ)^2 := by
    norm_num only [NNReal.coe_ofNat,show (2:ℝ)^2=4 by norm_num]
    exact hL
  have hh := hX.local_harmonic_frame_defect hn hK p u hR hb hH (fun _ => 2) hL'
    g q hq d A hd hqr (fun x => 5*gramDefect μ hQ u x)
    (Eventually.of_forall (fun x => mul_nonneg (by norm_num) (gramDefect_nonneg μ hQ u x)))
    (htr.mono (fun _ hx => hx.1)) (htr.mono (fun _ hx => hx.2))
  simpa only [← mul_assoc,show (6:ℝ)*5=30 by norm_num] using hh

end RegularPointCoordinates

end

end OAI
