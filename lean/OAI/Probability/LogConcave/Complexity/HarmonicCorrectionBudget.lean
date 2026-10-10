import Mathlib
import OAI.Probability.LogConcave.Sampling.TransportCorrectionMajorant

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

local instance : DecidableEq Unit := Classical.decEq _

lemma jointCorrectionArray_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t : Icc (0:ℝ) T) (c : Unit → Fin (d+d)) :
    PolySmooth (jointCorrectionArray
      (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z) c) :=
  arrayCoordinateLift_polySmooth _ _ _
    (probabilityCorrection_polySmooth hF x hr hlam hl hR hRT hT0 hT1 s t) c

def harmonicCorrectionBudget (n : ℕ) : ℝ :=
  iterEnergyBudget harmonicGradientBound (fun _ => 2)
    (fun k => 2+normalizedTensorMajorant (k+1) 1)
    (fun k => (transportCorrectionMajorant k)^2) n 0

lemma harmonicCorrectionBudget_nonneg (n : ℕ) : 0≤harmonicCorrectionBudget n :=
  iterEnergyBudget_nonneg harmonicGradientBound.2 _ _ (fun _ => sq_nonneg _) n 0

def harmonicMeanBudget (n : ℕ) : ℝ :=
  iterEnergyBudget harmonicGradientBound (fun _ => 2)
    (fun k => 2+normalizedTensorMajorant (k+1) 1)
    (fun k => (normalizedTensorMajorant (k+1) 1)^2) n 0

lemma harmonicMeanBudget_nonneg (n : ℕ) : 0≤harmonicMeanBudget n :=
  iterEnergyBudget_nonneg harmonicGradientBound.2 _ _ (fun _ => sq_nonneg _) n 0

theorem harmonic_correction_taylor_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (s t u : Icc (0:ℝ) T)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r u) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r u)).map (fun y => Ξ y v)=
      gibbs (centeringPotential F x r u)) :
    let A := jointCorrectionArray (fun z => probabilityTransport hF x hr.le hl hT0 hT1 s t z-z)
    ∀n : ℕ,∀a b : ℝ,0≤a → a≤b → b≤1 →
      Integrable (fun y => ‖tensorVector A (Ξ y b)-chainTaylor
        (fun k v => tensorVector (iterTensorLie (centeringPotential F x r u)
          (harmonicSkew d) A k) (Ξ y v)) n a b‖^2) (gibbs (centeringPotential F x r u)) ∧
      (∫y,‖tensorVector A (Ξ y b)-chainTaylor
        (fun k v => tensorVector (iterTensorLie (centeringPotential F x r u)
          (harmonicSkew d) A k) (Ξ y v)) n a b‖^2 ∂gibbs (centeringPotential F x r u))≤
      ((b-a)^(n+1)/(n.factorial:ℝ))^2*
        ((d*((lam:ℝ)*r^2)^2)*(R⁻¹)^(4*(n+1))*harmonicCorrectionBudget (n+1)) := by
  have hu1 := u.2.2.trans_lt hT1
  have hRu : R^2≤1-(u:ℝ)^2 := by nlinarith [u.2.1,u.2.2]
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  have hH : PolySmooth (centeringPotential F x r u) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl u.2.1 hu1) (gaussianPotential_polySmooth d)
  have ht : HasGaussianLowerTail (centeringPotential F x r u) := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) u.2.1 hu1) (gaussianPotential_lowerTail d)
  let := probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  intro A n a b ha hab hb
  have hsub : uIcc a b⊆Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hab]
    intro v h; exact ⟨ha.trans h.1,h.2.trans hb⟩
  have h := stationary_lie_taylor_rms (S:=Unit) (d:=d+d) hH ht
    (centeringPotential_gradient_uniform hF x hr hl u.2.1 hu1)
    (harmonicSkew d) A (harmonicSkew_polySmooth d)
    (jointCorrectionArray_polySmooth hF x hr hlam hl hR hRT hT0 hT1 s t)
    (jointSkew_skew _ 1) (fun _ => 2)
    (fun k => 2+normalizedTensorMajorant (k+1) 1)
    (fun k => (transportCorrectionMajorant k)^2)
    (α:=1) (κ:=d*((lam:ℝ)*r^2)^2) (ρ:=R⁻¹) (by positivity) ((one_le_inv₀ hR).mpr hR1)
    (fun _ => sq_nonneg _) (harmonicSkew_inv_scaled hR hR1)
    (centeringScore_inv_scaled hF x hr hlam hl hR hRu u.2.1 hu1)
    (jointCorrection_inv_scaled hF x hr hlam hl hR hRT hT0 hT1 s t u)
    Ξ hder hm hlaw hab hsub n
  simpa only [one_pow,one_mul,←pow_mul,harmonicCorrectionBudget] using h

theorem harmonic_mean_taylor_uniform {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r T) (harmonicSkew d) (Ξ y t)) (Icc (0:ℝ) 1) t)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀t∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y t)=
      gibbs (centeringPotential F x r T)) :
    ∀n : ℕ,∀a b : ℝ,0≤a → a≤b → b≤1 →
      Integrable (fun y => ‖tensorVector (centeringMeanArray F x r T) (Ξ y b)-chainTaylor
        (fun k t => tensorVector (iterTensorLie (centeringPotential F x r T)
          (harmonicSkew d) (centeringMeanArray F x r T) k) (Ξ y t)) n a b‖^2)
        (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖tensorVector (centeringMeanArray F x r T) (Ξ y b)-chainTaylor
        (fun k t => tensorVector (iterTensorLie (centeringPotential F x r T)
          (harmonicSkew d) (centeringMeanArray F x r T) k) (Ξ y t)) n a b‖^2
        ∂gibbs (centeringPotential F x r T))≤
      ((b-a)^(n+1)/(n.factorial:ℝ))^2*
        ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)) := by
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  have hH : PolySmooth (centeringPotential F x r T) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht : HasGaussianLowerTail (centeringPotential F x r T) := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let := probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  intro n a b ha hab hb
  have hsub : uIcc a b⊆Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hab]
    intro t h; exact ⟨ha.trans h.1,h.2.trans hb⟩
  have h := stationary_lie_taylor_rms (S:=Unit) (d:=d+d) hH ht
    (centeringPotential_gradient_uniform hF x hr hl hT0 hT1)
    (harmonicSkew d) (centeringMeanArray F x r T)
    (harmonicSkew_polySmooth d) (centeringMeanArray_polySmooth hF x hr hlam hl hT0 hT1)
    (jointSkew_skew _ 1) (fun _ => 2)
    (fun k => 2+normalizedTensorMajorant (k+1) 1)
    (fun k => (normalizedTensorMajorant (k+1) 1)^2)
    (α:=1) (κ:=d*((lam:ℝ)*r)^2) (ρ:=R⁻¹) (by positivity) ((one_le_inv₀ hR).mpr hR1)
    (fun _ => sq_nonneg _) (harmonicSkew_inv_scaled hR hR1)
    (centeringScore_inv_scaled hF x hr hlam hl hR hRT hT0 hT1)
    (centeringMean_inv_scaled hF x hr hlam hl hR hRT hT0 hT1)
    Ξ hder hm hlaw hab hsub n
  simpa only [one_pow,one_mul,←pow_mul,harmonicMeanBudget] using h
end LogConcaveSampling

end

end

end

end OAI
