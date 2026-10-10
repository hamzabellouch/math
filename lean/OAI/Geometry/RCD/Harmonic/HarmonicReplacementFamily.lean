import OAI.Geometry.RCD.Harmonic.AnnularHarmonicReplacement
import OAI.Geometry.RCD.Metric.MeasuredAnnularMass

namespace OAI

/-! # Harmonic replacements on a fixed inner physical ball

The annular condition is derived from the actual measured maps. The
normalization remains the mass of the larger approximation ball.
-/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_replacement_family {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {S R L E : ℝ}
    (hS : 0<S) (hR : 0<R) (hRS : 2*R≤S) (hL : 0≤L) (hE : 0≤E)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*(2*(R*r k))^2)
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (hε : Tendsto ε atTop (𝓝 0))
    (u : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hub : ∀ᶠ k in atTop,
      ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k)‖^2≤
        L*(hausdorff n X).real (ball (p k) (S*r k)) ∧
      r k^2*energyForm (hausdorff n X) hX.quadratic (u k) (u k)≤
        E*(hausdorff n X).real (ball (p k) (S*r k))) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∃ w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic,
      ∀ k, w k-u (k+N)∈SobolevSpace.dirichlet (hausdorff n X) hX.quadratic
          (ball (p (k+N)) (R*r (k+N))) ∧
        IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p (k+N)) (R*r (k+N))) (w k) ∧
        energyForm (hausdorff n X) hX.quadratic (w k) (w k)≤
          energyForm (hausdorff n X) hX.quadratic (u (k+N)) (u (k+N)) ∧
        ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k)‖^2≤
          C*(hausdorff n X).real (ball (p (k+N)) (S*r (k+N))) ∧
        r (k+N)^2*energyForm (hausdorff n X) hX.quadratic (w k) (w k)≤
          E*(hausdorff n X).real (ball (p (k+N)) (S*r (k+N))) ∧
        r (k+N)^2*energyForm (hausdorff n X) hX.quadratic (u (k+N)) (u (k+N))≤
          E*(hausdorff n X).real (ball (p (k+N)) (S*r (k+N))) := by
  have hann := measured_annulus_doubles hn hS hR hRS hr hV
    (fun k => (hX.finiteOnBounded _ isBounded_ball).ne)
    (fun k => ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne) hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hann.and hub)
  obtain ⟨P,hP,hreplace⟩ := hX.annular_harmonic_replacement hn
  let C := 2*L+2*P*(R^2*E)+1
  have hC : 0<C := by dsimp only [C]; positivity
  have hex (k : ℕ) : ∃ w : SobolevSpace (hausdorff n X) hX.quadratic,
      w-u (k+N)∈SobolevSpace.dirichlet (hausdorff n X) hX.quadratic
          (ball (p (k+N)) (R*r (k+N))) ∧
        IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p (k+N)) (R*r (k+N))) w ∧
        energyForm (hausdorff n X) hX.quadratic w w≤
          energyForm (hausdorff n X) hX.quadratic (u (k+N)) (u (k+N)) ∧
        ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic w‖^2≤
          C*(hausdorff n X).real (ball (p (k+N)) (S*r (k+N))) ∧
        r (k+N)^2*energyForm (hausdorff n X) hX.quadratic w w≤
          E*(hausdorff n X).real (ball (p (k+N)) (S*r (k+N))) ∧
        r (k+N)^2*energyForm (hausdorff n X) hX.quadratic (u (k+N)) (u (k+N))≤
          E*(hausdorff n X).real (ball (p (k+N)) (S*r (k+N))) := by
    have hh := hN (k+N) (Nat.le_add_left N k)
    have huE : (R*r (k+N))^2*energyForm (hausdorff n X) hX.quadratic (u (k+N)) (u (k+N))≤
        (R^2*E)*(hausdorff n X).real (ball (p (k+N)) (S*r (k+N))) := by
      have ht := mul_le_mul_of_nonneg_left hh.2.2 (sq_nonneg R)
      convert ht using 1 <;> ring
    obtain ⟨w,hwb,hwh,hwe,hwl⟩ := hreplace (p (k+N)) (R*r (k+N))
      (mul_pos hR (hr (k+N))) (hcurv (k+N)) hh.1 (u (k+N))
      ((hausdorff n X).real (ball (p (k+N)) (S*r (k+N)))) L (R^2*E) hh.2.1 huE
    refine ⟨w,hwb,hwh,hwe,hwl.trans ?_,?_,hh.2.2⟩
    · apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
      dsimp only [C]
      linarith
    · exact (mul_le_mul_of_nonneg_left hwe (sq_nonneg _)).trans hh.2.2
  choose w hw using hex
  exact ⟨C,hC,N,w,hw⟩

end RegularPointCoordinates

end

end OAI
