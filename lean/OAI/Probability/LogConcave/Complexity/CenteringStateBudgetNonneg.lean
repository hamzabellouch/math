import Mathlib
import OAI.Probability.LogConcave.Complexity.CenteringStateBudget

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

local instance centeringStateBudgetNonnegDecidableEqUnit : DecidableEq Unit := Classical.decEq _

lemma centeringStateBudget_nonneg (n : ℕ) : 0≤centeringStateBudget n :=
  iterEnergyBudget_nonneg harmonicGradientBound.2 _ _ (fun _ => by norm_num) n 0

lemma centeringMeanBudget_nonneg (n : ℕ) : 0≤centeringMeanBudget n :=
  iterEnergyBudget_nonneg harmonicGradientBound.2 _ _ (fun _ => sq_nonneg _) n 0

theorem centering_state_jet_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T s : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2)
    (hR : 0<R) (hRT : R^2≤1-T^2) (hT0 : 0≤T) (hT1 : T<1) (hs : 0<s)
    (Z : Point (d+d) → Point (d+d)) (hm : Measurable Z)
    (hlaw : (gibbs (centeringPotential F x r T)).map Z=gibbs (centeringPotential F x r T))
    (n : ℕ) (hn : 0<n) :
    let A := jointSkew (centeringKernel hF x hr hl hT0 hT1) s
    let I := vectorArray (id : Point (d+d) → Point (d+d))
    Integrable (fun y => ‖tensorVector (iterTensorLie (centeringPotential F x r T) A I n) (Z y)‖^2)
      (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖tensorVector (iterTensorLie (centeringPotential F x r T) A I n) (Z y)‖^2
      ∂gibbs (centeringPotential F x r T))≤
      ((d+d:ℕ):ℝ)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^n*centeringStateBudget n := by
  have hR1 : R≤1 := by nlinarith [sq_nonneg T]
  have hH : PolySmooth (centeringPotential F x r T) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht : HasGaussianLowerTail (centeringPotential F x r T) := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let := probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  intro A I
  have hp := iterTensorLie_polySmooth hH A I
    (centeringSkew_polySmooth hF x hr hlam hl hT0 hT1 s) (identityArray_polySmooth (d+d)) n
  have hz := stationary_tensorVector_rms hH.smooth.continuous ht _ hp Z hm hlaw
  refine ⟨hz.1,?_⟩
  rw [hz.2]
  have q := iterTensorLie_energy hH ht
    (centeringPotential_gradient_uniform hF x hr hl hT0 hT1) A I
    (centeringSkew_polySmooth hF x hr hlam hl hT0 hT1 s) (identityArray_polySmooth (d+d))
    (fun k => 2*kernelMajorant k) (fun k => 2+normalizedTensorMajorant (k+1) 1) (fun _ => 1)
    (α:=(lam:ℝ)*r/s) (κ:=((d+d:ℕ):ℝ)) (ρ:=R⁻¹) (by positivity) ((one_le_inv₀ hR).mpr hR1)
    (fun _ => by norm_num) (centeringSkew_inv_scaled hF x hr hlam hl hR hRT hT0 hT1 hs)
    (centeringScore_inv_scaled hF x hr hlam hl hR hRT hT0 hT1)
    (fun _ hk => identityArray_inv_energy hH.smooth.continuous ht hR hR1 hk) n 0 (Or.inl hn)
  simpa only [Nat.mul_zero,pow_zero,mul_one,centeringStateBudget] using q

theorem centering_velocity_taylor_uniform {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
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
    let A := jointSkew (centeringKernel hF x hr hl hT0 hT1) s
    let I := vectorArray (id : Point (d+d) → Point (d+d))
    let J := fun k t y => tensorVector (iterTensorLie (centeringPotential F x r T) A I k) (Ξ y t)
    ∀n : ℕ,∀a b : ℝ,0≤a → a≤b → b≤1 →
      Integrable (fun y => ‖J 1 b y-chainTaylor (fun k t => J (k+1) t y) n a b‖^2)
        (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖J 1 b y-chainTaylor (fun k t => J (k+1) t y) n a b‖^2
        ∂gibbs (centeringPotential F x r T))≤
      ((b-a)^(n+1)/(n.factorial:ℝ))^2*
        (((d+d:ℕ):ℝ)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+2)*centeringStateBudget (n+2)) := by
  have hH : PolySmooth (centeringPotential F x r T) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht : HasGaussianLowerTail (centeringPotential F x r T) := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let := probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  intro A I J n a b ha hab hb
  have hsub : uIcc a b⊆Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hab]
    intro t h; exact ⟨ha.trans h.1,h.2.trans hb⟩
  have hfin (t : ℝ) (ht : t∈Ioc a b) := centering_state_jet_rms hF x hr hlam hl hR hRT hT0 hT1 hs
    (fun y => Ξ y t) (hm.comp (measurable_const.prodMk measurable_id))
    (hlaw t (hsub (by rw [uIcc_of_le hab]; exact ⟨ht.1.le,ht.2⟩))) (n+2) (by omega)
  apply chainTaylor_remainder_rms (J:=fun k t y => J (k+1) t y) hab
    (show 0≤((d+d:ℕ):ℝ)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+2)*centeringStateBudget (n+2) from
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _)) (centeringStateBudget_nonneg _)) hsub
  · intro y k t ht
    exact lie_vector_chain hH A I (centeringSkew_polySmooth hF x hr hlam hl hT0 hT1 s)
      (identityArray_polySmooth (d+d)) (jointSkew_skew _ s) (Ξ y) (hder y) (k+1) ht
  · exact ((tensorVector_contDiff _ (fun c => (iterTensorLie_polySmooth hH A I
      (centeringSkew_polySmooth hF x hr hlam hl hT0 hT1 s) (identityArray_polySmooth (d+d)) (n+2) c).smooth)).continuous.measurable.comp hm).aestronglyMeasurable
  · exact fun t ht => (hfin t ht).1
  · exact fun t ht => (hfin t ht).2
end LogConcaveSampling

end

end

end OAI
