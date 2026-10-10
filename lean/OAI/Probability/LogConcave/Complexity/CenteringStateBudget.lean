import Mathlib
import OAI.Probability.LogConcave.Sampling.TransportCorrectionMajorant

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

local instance centeringStateBudgetDecidableEqUnit : DecidableEq Unit := Classical.decEq _

lemma centeringSkew_inv_scaled {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T s : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (hs : 0<s) :
    ∀k y,AllSplitBound
      (spatialTensor (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (List.finRange k) y)
      ((2*kernelMajorant k)*((lam:ℝ)*r/s)*(R⁻¹)^k) := by
  intro k y
  convert centering_jointSkew_spatial_bound hF x hr hlam hl hR hRT hT0 hT1 s y using 1
  rw [abs_of_pos (inv_pos.mpr hs)]
  simp only [inv_pow,div_eq_mul_inv]
  ring

lemma identityArray_polySmooth (d : ℕ) (c : Unit → Fin d) :
    PolySmooth (vectorArray (id : Point d → Point d) c) :=
  vectorArray_polySmooth contDiff_id LipschitzWith.id (fun _ => 1)
    (fun _ => by norm_num) (fun _ _ y => multilinearTensor_id_bound y) c

lemma identityArray_inv_energy {d k : ℕ} {H : Point d → ℝ}
    (hH : Continuous H) (ht : HasGaussianLowerTail H) {R : ℝ}
    (hR : 0<R) (hR1 : R≤1) (hk : 0<k) :
    spatialEnergy (vectorArray (id : Point d → Point d)) k (gibbs H)≤
      d*(R⁻¹)^(2*k)*1 := by
  have he := vectorArray_energy hH ht contDiff_id (identityArray_polySmooth d) hk
    (fun y => multilinearTensor_id_bound (n:=k) y)
  simp only [one_pow,mul_one] at he ⊢
  apply he.trans
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ ((one_le_inv₀ hR).mpr hR1))

def centeringStateBudget (n : ℕ) : ℝ :=
  iterEnergyBudget harmonicGradientBound (fun k => 2*kernelMajorant k)
    (fun k => 2+normalizedTensorMajorant (k+1) 1) (fun _ => 1) n 0

def centeringMeanBudget (n : ℕ) : ℝ :=
  iterEnergyBudget harmonicGradientBound (fun k => 2*kernelMajorant k)
    (fun k => 2+normalizedTensorMajorant (k+1) 1)
    (fun k => (normalizedTensorMajorant (k+1) 1)^2) n 0

theorem centering_state_taylor_uniform {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T s : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1) (hs : 0<s)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (Ξ y t)) (Icc (0:ℝ) 1) t)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀t∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y t)=
      gibbs (centeringPotential F x r T)) :
    let A := vectorArray (id : Point (d+d) → Point (d+d))
    ∀n : ℕ,∀a b : ℝ,0≤a → a≤b → b≤1 →
      Integrable (fun y => ‖tensorVector A (Ξ y b)-chainTaylor
        (fun k t => tensorVector (iterTensorLie (centeringPotential F x r T)
          (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) A k) (Ξ y t)) n a b‖^2)
        (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖tensorVector A (Ξ y b)-chainTaylor
        (fun k t => tensorVector (iterTensorLie (centeringPotential F x r T)
          (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) A k) (Ξ y t)) n a b‖^2
        ∂gibbs (centeringPotential F x r T))≤
      ((b-a)^(n+1)/(n.factorial:ℝ))^2*
        ((d+d)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+1)*centeringStateBudget (n+1)) := by
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  have hH : PolySmooth (centeringPotential F x r T) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht : HasGaussianLowerTail (centeringPotential F x r T) := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let := probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  intro A n a b ha hab hb
  have hsub : uIcc a b⊆Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hab]
    intro t h; exact ⟨ha.trans h.1,h.2.trans hb⟩
  have q := stationary_lie_taylor_rms (S:=Unit) (d:=d+d) hH ht
    (centeringPotential_gradient_uniform hF x hr hl hT0 hT1)
    (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) A
    (centeringSkew_polySmooth hF x hr hlam hl hT0 hT1 s) (identityArray_polySmooth (d+d))
    (jointSkew_skew _ s) (fun k => 2*kernelMajorant k)
    (fun k => 2+normalizedTensorMajorant (k+1) 1) (fun _ => 1)
    (α:=(lam:ℝ)*r/s) (κ:=d+d) (ρ:=R⁻¹) (by positivity) ((one_le_inv₀ hR).mpr hR1)
    (fun _ => by norm_num) (centeringSkew_inv_scaled hF x hr hlam hl hR hRT hT0 hT1 hs)
    (centeringScore_inv_scaled hF x hr hlam hl hR hRT hT0 hT1)
    (fun k hk => by simpa only [Nat.cast_add] using identityArray_inv_energy hH.smooth.continuous ht hR hR1 hk)
    Ξ hder hm hlaw hab hsub n
  simpa only [centeringStateBudget,Nat.cast_add] using q

theorem centering_mean_taylor_uniform {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T s : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1) (hs : 0<s)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (Ξ y t)) (Icc (0:ℝ) 1) t)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀t∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y t)=
      gibbs (centeringPotential F x r T)) :
    ∀n : ℕ,∀a b : ℝ,0≤a → a≤b → b≤1 →
      Integrable (fun y => ‖tensorVector (centeringMeanArray F x r T) (Ξ y b)-chainTaylor
        (fun k t => tensorVector (iterTensorLie (centeringPotential F x r T)
          (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)
          (centeringMeanArray F x r T) k) (Ξ y t)) n a b‖^2)
        (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖tensorVector (centeringMeanArray F x r T) (Ξ y b)-chainTaylor
        (fun k t => tensorVector (iterTensorLie (centeringPotential F x r T)
          (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)
          (centeringMeanArray F x r T) k) (Ξ y t)) n a b‖^2
        ∂gibbs (centeringPotential F x r T))≤
      ((b-a)^(n+1)/(n.factorial:ℝ))^2*
        ((d*((lam:ℝ)*r)^2)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+1)*centeringMeanBudget (n+1)) := by
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
  exact stationary_lie_taylor_rms (S:=Unit) (d:=d+d) hH ht
    (centeringPotential_gradient_uniform hF x hr hl hT0 hT1)
    (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (centeringMeanArray F x r T)
    (centeringSkew_polySmooth hF x hr hlam hl hT0 hT1 s)
    (centeringMeanArray_polySmooth hF x hr hlam hl hT0 hT1)
    (jointSkew_skew _ s) (fun k => 2*kernelMajorant k)
    (fun k => 2+normalizedTensorMajorant (k+1) 1)
    (fun k => (normalizedTensorMajorant (k+1) 1)^2)
    (α:=(lam:ℝ)*r/s) (κ:=d*((lam:ℝ)*r)^2) (ρ:=R⁻¹) (by positivity) ((one_le_inv₀ hR).mpr hR1)
    (fun k => sq_nonneg _) (centeringSkew_inv_scaled hF x hr hlam hl hR hRT hT0 hT1 hs)
    (centeringScore_inv_scaled hF x hr hlam hl hR hRT hT0 hT1)
    (centeringMean_inv_scaled hF x hr hlam hl hR hRT hT0 hT1)
    Ξ hder hm hlaw hab hsub n
end LogConcaveSampling

end

end

end OAI
