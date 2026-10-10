import Mathlib
import OAI.Probability.LogConcave.Numerics.CenteringStateQuadratureBudget
import OAI.Probability.LogConcave.Dynamics.ObservableIntegralMeasurable

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature RMSIntegral
open scoped Classical BigOperators NNReal

def centeringMeanCircuit {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h ψ s : ℝ) (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1))
    (y : Point (d+d)) : Point d :=
  s • (productPointEquiv d d y).2+
    ∑j,weight (probabilityNodes nc) j 0 1 • conditionalFieldMean F x r T
      (productPointEquiv d d (stationaryPicard nc Nc
        (centeringVelocityJoint F x r T h ψ s n m N e) y j)).1

def centeringInitialBudget (d : ℕ) (lam : ℝ≥0) (r R s : ℝ) : ℝ :=
  (((d+d:ℕ):ℝ)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)*centeringStateBudget 1)

def centeringPicardBudget (nc Nc d : ℕ) (lam K : ℝ≥0) (r R s Bv : ℝ) : ℝ :=
  (2*Real.sqrt (2*(centeringRowBudget nc:ℝ)^2*Bv+
      2*centeringStateQuadratureBudget nc d lam r R s)+
    ((centeringRowBudget nc*K:ℝ≥0):ℝ)^Nc*Real.sqrt (centeringInitialBudget d lam r R s))^2

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r R T h ψ s : ℝ}
  (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2)
  (hR : 0<R) (hRT : R^2 ≤ 1-T^2) (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0<s)
  (X : StationaryPath (gibbs (centeringPotential F x r T))
    (skewLieField (centeringPotential F x r T) (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)))

include hlam hR hRT hs

theorem centeringPicard_state_rms (n m N nc Nc : ℕ) (hnc : 0<nc)
    (e : ProbabilityNode T h (n+1)) {K : ℝ≥0}
    (hhat : LipschitzWith K (centeringVelocityJoint F x r T h ψ s n m N e))
    (hq : centeringRowBudget nc*K ≤ 1/2) {Bv : ℝ} (hBv : 0 ≤ Bv)
    (hvi : Integrable (fun y => ‖centeringVelocityJoint F x r T h ψ s n m N e y-
      skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) y‖^2)
      (gibbs (centeringPotential F x r T)))
    (hvb : (∫y,‖centeringVelocityJoint F x r T h ψ s n m N e y-
      skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) y‖^2
      ∂gibbs (centeringPotential F x r T)) ≤ Bv) (i : Fin (nc+1)) :
    Integrable (fun y => ‖stationaryPicard nc Nc
      (centeringVelocityJoint F x r T h ψ s n m N e) y i-X.path y (probabilityNodes nc i)‖^2)
      (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖stationaryPicard nc Nc (centeringVelocityJoint F x r T h ψ s n m N e) y i-
      X.path y (probabilityNodes nc i)‖^2 ∂gibbs (centeringPotential F x r T)) ≤
      centeringPicardBudget nc Nc d lam K r R s Bv := by
  have hH := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let : IsProbabilityMeasure (gibbs (centeringPotential F x r T)) :=
    probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  exact stationaryPicard_rms X (centeringTrueVelocity_continuous hF x hr hlam hl hT0 hT1 s)
    hhat (centering_lipschitz_memLp hF x hr hlam hl hT0 hT1 (LipschitzWith.id)) nc hnc hq
    (centeringStateQuadratureBudget_nonneg nc d lam r R s) hBv
    (by positivity [centeringStateBudget_nonneg 1])
    (centering_state_quadrature_rms hF x hr hlam hl hR hRT hT0 hT1 hs X nc hnc) hvi hvb
    (fun j => (centering_initial_rms hF x hr hlam hl hR hRT hT0 hT1 hs X
      (probabilityNodes_mem hnc j)).2) Nc i

theorem centeringMeanCircuit_rms (n m N nc Nc : ℕ) (hnc : 0<nc)
    (e : ProbabilityNode T h (n+1)) {K : ℝ≥0}
    (hhat : LipschitzWith K (centeringVelocityJoint F x r T h ψ s n m N e))
    {Bz : ℝ} (hBz : 0 ≤ Bz)
    (hZi : ∀j, Integrable (fun y => ‖stationaryPicard nc Nc
      (centeringVelocityJoint F x r T h ψ s n m N e) y j-X.path y (probabilityNodes nc j)‖^2)
      (gibbs (centeringPotential F x r T)))
    (hZb : ∀j, (∫y,‖stationaryPicard nc Nc
      (centeringVelocityJoint F x r T h ψ s n m N e) y j-X.path y (probabilityNodes nc j)‖^2
      ∂gibbs (centeringPotential F x r T)) ≤ Bz) :
    let ideal := fun y => s • (productPointEquiv d d y).2+
      ∫t in (0:ℝ)..1,conditionalFieldMean F x r T (productPointEquiv d d (X.path y t)).1
    Integrable (fun y => ‖centeringMeanCircuit F x r T h ψ s n m N nc Nc e y-ideal y‖^2)
      (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖centeringMeanCircuit F x r T h ψ s n m N nc Nc e y-ideal y‖^2
      ∂gibbs (centeringPotential F x r T)) ≤
      2*(centeringRowBudget nc:ℝ)^2*((Real.pi^2/2)*T*((lam:ℝ)*r))^2*Bz+
        2*centeringMeanQuadratureBudget nc d lam r R s := by
  intro ideal
  have hH := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let : IsProbabilityMeasure (gibbs (centeringPotential F x r T)) :=
    probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  have hMc : LipschitzWith ⟨(Real.pi^2/2)*T*((lam:ℝ)*r),by positivity⟩
      (fun y => conditionalFieldMean F x r T (productPointEquiv d d y).1) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have hp : dist (productPointEquiv d d y).1 (productPointEquiv d d z).1 ≤ dist y z := by
      simpa only [dist_eq_norm,map_sub,Prod.fst_sub] using productPointEquiv_fst_norm_le (y-z)
    exact ((conditionalFieldMean_lipschitz hF x hr.le hl hT0 hT1).dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left hp (NNReal.coe_nonneg _))
  have hquad := centering_mean_quadrature_rms hF x hr hlam hl hR hRT hT0 hT1 hs X nc hnc
  have he := stationaryOutput_rms X hMc nc
    (fun j y => stationaryPicard nc Nc (centeringVelocityJoint F x r T h ψ s n m N e) y j)
    (stationaryPicard_measurable nc Nc hhat.continuous.measurable) hBz hZi hZb hquad.1 hquad.2
    (fun y => s • (productPointEquiv d d y).2)
  exact he
end LogConcaveSampling

end

end

end OAI
