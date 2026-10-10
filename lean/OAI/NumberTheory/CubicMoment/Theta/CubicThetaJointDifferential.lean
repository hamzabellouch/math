import OAI.NumberTheory.CubicMoment.Theta.CubicThetaJointMajorant

namespace OAI

/-! The full real differential of the actual theta series is obtained by
summing its Fourier-term differentials on each positive-height strip. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaAngular_hasFDerivAt {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) {p : ℂ × ℝ} (hp : 0<p.2) :
    HasFDerivAt (cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ))
      (∑' n : Eisenstein,cubicThetaSeriesTermFDeriv (cubicThetaAngularCoefficient a ℓ) p n) p := by
  obtain ⟨u,hu,hbu⟩ := cubicThetaAngular_uniform_differentials hC ha ℓ
    (show 0<p.2/2 by positivity)
  have hconv : Convex ℝ {q : ℂ × ℝ | p.2/2<q.2} :=
    (convex_Ioi (p.2/2)).linear_preimage (LinearMap.snd ℝ ℂ ℝ)
  have hopen : IsOpen {q : ℂ × ℝ | p.2/2<q.2} := isOpen_lt continuous_const continuous_snd
  have hmem : p∈{q : ℂ × ℝ | p.2/2<q.2} := by change p.2/2<p.2; linarith
  exact hasFDerivAt_tsum_of_isPreconnected hu hopen hconv.isPreconnected
    (fun n q hq => cubicThetaSeriesTerm_hasFDerivAt _
      (lt_trans (by positivity : 0<p.2/2) hq) n)
    hbu hmem (cubicThetaAngular_summable hC ha ℓ hp p.1) hmem

theorem cubicThetaAngular_differentiableAt {a : Eisenstein → ℂ} {C : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) {p : ℂ × ℝ} (hp : 0<p.2) :
    DifferentiableAt ℝ (cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ)) p :=
  (cubicThetaAngular_hasFDerivAt hC ha ℓ hp).differentiableAt

end CubicFirstMoment

end

end OAI
