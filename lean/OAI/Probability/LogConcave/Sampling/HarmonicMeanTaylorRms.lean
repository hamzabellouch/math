import Mathlib
import OAI.Probability.LogConcave.Analysis.CenteringPotential
import OAI.Probability.LogConcave.Dynamics.JointHarmonicFlow

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

local instance harmonicMeanTaylorRmsDecidableEqUnit : DecidableEq Unit := Classical.decEq _

theorem harmonic_mean_taylor_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r T)
        (harmonicSkew d) (Ξ y t)) (Icc (0:ℝ) 1) t)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀t∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y t)=
      gibbs (centeringPotential F x r T)) :
    ∀n : ℕ,∀a b : ℝ,0≤a → a≤b → b≤1 →
      Integrable (fun y => ‖tensorVector (centeringMeanArray F x r T) (Ξ y b)-chainTaylor
        (fun k t => tensorVector (iterTensorLie (centeringPotential F x r T)
          (harmonicSkew d)
          (centeringMeanArray F x r T) k) (Ξ y t)) n a b‖^2)
        (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖tensorVector (centeringMeanArray F x r T) (Ξ y b)-chainTaylor
        (fun k t => tensorVector (iterTensorLie (centeringPotential F x r T)
          (harmonicSkew d)
          (centeringMeanArray F x r T) k) (Ξ y t)) n a b‖^2
        ∂gibbs (centeringPotential F x r T))≤
      ((b-a)^(n+1)/(n.factorial:ℝ))^2*
        ((d*((lam:ℝ)*r)^2)*
        iterEnergyBudget (centeringGradientBound lam r T (by positivity))
          (fun _ => 2)
          (fun k => 2+normalizedTensorMajorant (k+1) (1-T^2))
          (fun k => (normalizedTensorMajorant (k+1) (1-T^2))^2) (n+1) 0) := by
  have hH : PolySmooth (centeringPotential F x r T) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht : HasGaussianLowerTail (centeringPotential F x r T) := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let := probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  intro n a b ha hab hb
  have hsub : uIcc a b⊆Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hab]
    intro t h; exact ⟨ha.trans h.1,h.2.trans hb⟩
  have h := stationary_lie_taylor_rms (S:=Unit) (d:=d+d)
    (H:=centeringPotential F x r T) hH ht
    (centeringPotential_gradient_lipschitz hF x hr hl hT0 hT1)
    (harmonicSkew d) (centeringMeanArray F x r T)
    (harmonicSkew_polySmooth d) (centeringMeanArray_polySmooth hF x hr hlam hl hT0 hT1)
    (jointSkew_skew _ 1)
    (fun _ => 2)
    (fun k => 2+normalizedTensorMajorant (k+1) (1-T^2))
    (fun k => (normalizedTensorMajorant (k+1) (1-T^2))^2)
    (α:=1) (κ:=d*((lam:ℝ)*r)^2) (ρ:=1) (by positivity) le_rfl
    (fun _ => sq_nonneg _)
    (harmonicSkew_scaled_bound d)
    (centeringScore_scaled_bound hF x hr hlam hl hT0 hT1)
    (centeringMean_scaled_energy hF x hr hlam hl hT0 hT1)
    Ξ hder hm hlaw hab hsub n
  refine ⟨h.1,h.2.trans ?_⟩
  simp only [one_pow,mul_one]
  exact le_rfl

theorem exists_harmonic_mean_taylor_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    ∃Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y,Continuous (Ξ y) ∧ Ξ y 0=y) ∧
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) ∧
      (∀t∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y t)=
        gibbs (centeringPotential F x r T)) ∧
      ∀n : ℕ,∀a b : ℝ,0≤a → a≤b → b≤1 →
      Integrable (fun y => ‖tensorVector (centeringMeanArray F x r T) (Ξ y b)-chainTaylor
        (fun k t => tensorVector (iterTensorLie (centeringPotential F x r T)
          (harmonicSkew d)
          (centeringMeanArray F x r T) k) (Ξ y t)) n a b‖^2)
        (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖tensorVector (centeringMeanArray F x r T) (Ξ y b)-chainTaylor
        (fun k t => tensorVector (iterTensorLie (centeringPotential F x r T)
          (harmonicSkew d)
          (centeringMeanArray F x r T) k) (Ξ y t)) n a b‖^2
        ∂gibbs (centeringPotential F x r T))≤
      ((b-a)^(n+1)/(n.factorial:ℝ))^2*
        ((d*((lam:ℝ)*r)^2)*
        iterEnergyBudget (centeringGradientBound lam r T (by positivity))
          (fun _ => 2)
          (fun k => 2+normalizedTensorMajorant (k+1) (1-T^2))
          (fun k => (normalizedTensorMajorant (k+1) (1-T^2))^2) (n+1) 0) := by
  obtain ⟨Ξ,hinit,hder,hm,hlaw⟩ := exists_joint_harmonic_flow
    ((interpolationPotential_smooth hF x hr.le hl hT0 hT1).of_le (by norm_cast))
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1)
    (interpolationPotential_gradient_lipschitz hF x hr.le hl hT0 hT1)
  exact ⟨Ξ,hinit,hm,hlaw,harmonic_mean_taylor_rms hF x hr hlam hl hT0 hT1 Ξ hder hm hlaw⟩
end LogConcaveSampling

end

end

end

end OAI
