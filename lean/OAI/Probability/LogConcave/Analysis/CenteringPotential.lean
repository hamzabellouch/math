import Mathlib
import OAI.Probability.LogConcave.Sampling.ConditionalMeanArray
import OAI.Probability.LogConcave.Dynamics.ActualJointCenteringFlow
import OAI.Probability.LogConcave.Sampling.StationaryTensorVectorRms

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

local instance : DecidableEq Unit := Classical.decEq _

lemma gradient_gaussianPotential {d : ℕ} (y : Point d) :
    gradient (fun z : Point d => ‖z‖^2/2) y=y := by
  ext i
  rw [←directional_basis_gradient,directional_gaussianPotential]
  simp [EuclideanSpace.basisFun_apply,PiLp.inner_apply]

lemma gaussianPotential_gradient_lipschitz (d : ℕ) :
    LipschitzWith 1 (gradient (fun z : Point d => ‖z‖^2/2)) := by
  have he : gradient (fun z : Point d => ‖z‖^2/2)=id := funext gradient_gaussianPotential
  rw [he]
  exact LipschitzWith.id

def centeringPotential {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ) : Point (d+d) → ℝ :=
  productPotential (interpolationPotential F x r T) (fun z : Point d => ‖z‖^2/2)

def centeringMeanArray {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ) :
    (Unit → Fin (d+d)) → Point (d+d) → ℝ :=
  arrayCoordinateLift (leftCoordinates d d) (fun _ => leftCoordinates d d)
    (conditionalMeanArray F x r T)

def centeringGradientBound (lam : ℝ≥0) (r T : ℝ) (h : 0≤(Real.pi^2/2)*T*((lam:ℝ)*r)) : ℝ≥0 :=
  (1+‖r*T‖₊*⟨(Real.pi^2/2)*T*((lam:ℝ)*r),h⟩)+1

lemma centeringPotential_gradient_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    LipschitzWith (centeringGradientBound lam r T (by positivity))
      (gradient (centeringPotential F x r T)) :=
  productPotential_gradient_lipschitz
    ((interpolationPotential_smooth hF x hr.le hl hT0 hT1).differentiable (by simp))
    ((gaussianPotential_polySmooth d).smooth.differentiable (by simp))
    (interpolationPotential_gradient_lipschitz hF x hr.le hl hT0 hT1)
    (gaussianPotential_gradient_lipschitz d)

lemma centeringMeanArray_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (c : Unit → Fin (d+d)) : PolySmooth (centeringMeanArray F x r T c) :=
  arrayCoordinateLift_polySmooth _ _ _ (conditionalMeanArray_polySmooth hF x hr hlam hl hT0 hT1) c

lemma centeringMeanArray_energy {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)
    (hn : 0<n) :
    spatialEnergy (centeringMeanArray F x r T) n (gibbs (centeringPotential F x r T))≤
      d*((lam:ℝ)*r)^2*(normalizedTensorMajorant (n+1) (1-T^2))^2 := by
  have hH := interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1
  have ht := interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1
  let := probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  dsimp only [centeringMeanArray,centeringPotential]
  rw [spatialEnergy_leftLift hH.smooth.continuous _
    (fun c => (conditionalMeanArray_polySmooth hF x hr hlam hl hT0 hT1 c).smooth)]
  exact conditionalMeanArray_energy hF x hr hlam hl hT0 hT1 hn

lemma centeringSkew_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (s : ℝ) :
    ∀c,PolySmooth (jointSkew (centeringKernel hF x hr hl hT0 hT1) s c) := by
  apply jointSkew_polySmooth
  intro i j
  simpa only [matrixArray_apply,Sum.elim_inl,Sum.elim_inr] using
    centeringKernel_polySmooth hF x hr hlam hl hT0 hT1 (Sum.elim (fun _ => i) (fun _ => j))

lemma centeringSkew_scaled_bound {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T s : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (hs : 0<s) :
    ∀k y,AllSplitBound
      (spatialTensor (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (List.finRange k) y)
      ((2*kernelMajorant k/R^k)*((lam:ℝ)*r/s)*1^k) := by
  intro k y
  convert centering_jointSkew_spatial_bound hF x hr hlam hl hR hRT hT0 hT1 s y using 1
  rw [abs_of_pos (inv_pos.mpr hs)]
  simp only [one_pow,mul_one]
  ring

lemma centeringScore_scaled_bound {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    ∀k,0<k → ∀y,AllSplitBound
      (spatialTensor (scoreField (centeringPotential F x r T)) (List.finRange k) y)
      ((2+normalizedTensorMajorant (k+1) (1-T^2))*1^k) := by
  intro k hk y
  simpa only [centeringPotential,one_pow,mul_one] using
    centeringScore_allSplit hF x hr hlam hl hT0 hT1 hk y

lemma centeringMean_scaled_energy {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) :
    ∀k,0<k → spatialEnergy (centeringMeanArray F x r T) k
      (gibbs (centeringPotential F x r T))≤
      (d*((lam:ℝ)*r)^2)*1^(2*k)*(normalizedTensorMajorant (k+1) (1-T^2))^2 := by
  intro k hk
  simpa only [one_pow,mul_one] using centeringMeanArray_energy hF x hr hlam hl hT0 hT1 hk

theorem centering_mean_taylor_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T s : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (hs : 0<s)
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
        ((d*((lam:ℝ)*r)^2)*(((lam:ℝ)*r/s)^2)^(n+1)*
        iterEnergyBudget (centeringGradientBound lam r T (by positivity))
          (fun k => 2*kernelMajorant k/R^k)
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
    (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (centeringMeanArray F x r T)
    (centeringSkew_polySmooth hF x hr hlam hl hT0 hT1 s) (centeringMeanArray_polySmooth hF x hr hlam hl hT0 hT1)
    (jointSkew_skew _ s)
    (fun k => 2*kernelMajorant k/R^k)
    (fun k => 2+normalizedTensorMajorant (k+1) (1-T^2))
    (fun k => (normalizedTensorMajorant (k+1) (1-T^2))^2)
    (α:=(lam:ℝ)*r/s) (κ:=d*((lam:ℝ)*r)^2) (ρ:=1) (by positivity) le_rfl
    (fun _ => sq_nonneg _)
    (centeringSkew_scaled_bound hF x hr hlam hl hR hRT hT0 hT1 hs)
    (centeringScore_scaled_bound hF x hr hlam hl hT0 hT1)
    (centeringMean_scaled_energy hF x hr hlam hl hT0 hT1)
    Ξ hder hm hlaw hab hsub n
  refine ⟨h.1,h.2.trans ?_⟩
  simp only [one_pow,mul_one]
  exact le_rfl

theorem exists_centering_mean_taylor_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T s : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (hs : 0<s) :
    ∃Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y,Continuous (Ξ y) ∧ Ξ y 0=y) ∧
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) ∧
      (∀t∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y t)=
        gibbs (centeringPotential F x r T)) ∧
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
        ((d*((lam:ℝ)*r)^2)*(((lam:ℝ)*r/s)^2)^(n+1)*
        iterEnergyBudget (centeringGradientBound lam r T (by positivity))
          (fun k => 2*kernelMajorant k/R^k)
          (fun k => 2+normalizedTensorMajorant (k+1) (1-T^2))
          (fun k => (normalizedTensorMajorant (k+1) (1-T^2))^2) (n+1) 0) := by
  obtain ⟨Ξ,hinit,hder,hm,hlaw⟩ := exists_actual_joint_centering_flow hF x hr hlam hl hT0 hT1 hs
  exact ⟨Ξ,hinit,hm,hlaw,centering_mean_taylor_rms hF x hr hlam hl hR hRT hT0 hT1 hs Ξ hder hm hlaw⟩
end LogConcaveSampling

end

end

end

end OAI
