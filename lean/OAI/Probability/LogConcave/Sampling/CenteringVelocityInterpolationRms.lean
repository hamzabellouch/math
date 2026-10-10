import Mathlib
import OAI.Probability.LogConcave.Complexity.CenteringStateBudgetNonneg
import OAI.Probability.LogConcave.Sampling.IdentityOutputEmbedding
import OAI.Probability.LogConcave.Complexity.SingleCellBasisBudget

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature TensorEnergy
open scoped Classical BigOperators NNReal RealInnerProductSpace

local instance centeringVelocityInterpolationRmsDecidableEqUnit : DecidableEq Unit := Classical.decEq _

theorem centering_velocity_interpolation_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T s : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2)
    (hR : 0<R) (hRT : R^2 ≤ 1-T^2) (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0<s)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (Ξ y t)) (Icc (0:ℝ) 1) t)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀t∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y t)=
      gibbs (centeringPotential F x r T)) (n : ℕ) (hn : 0<n) {v : ℝ} (hv : v∈Icc (0:ℝ) 1) :
    let V := fun t y => skewLieField (centeringPotential F x r T)
      (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (Ξ y t)
    Integrable (fun y => ‖V v y-interpolation (probabilityNodes n)
      (fun i => V (probabilityNodes n i) y) v‖^2) (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖V v y-interpolation (probabilityNodes n)
      (fun i => V (probabilityNodes n i) y) v‖^2 ∂gibbs (centeringPotential F x r T)) ≤
      4*(singleCellBasisBudget n)^2*
        (((d+d:ℕ):ℝ)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+2)*centeringStateBudget (n+2)) := by
  intro V
  let A := jointSkew (centeringKernel hF x hr hl hT0 hT1) s
  let I := vectorArray (id : Point (d+d) → Point (d+d))
  let J := fun k t y => tensorVector (iterTensorLie (centeringPotential F x r T) A I (k+1)) (Ξ y t)
  have hH : PolySmooth (centeringPotential F x r T) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have hA := centeringSkew_polySmooth hF x hr hlam hl hT0 hT1 s
  have hI := identityArray_polySmooth (d+d)
  have hJ (k : ℕ) (t : ℝ) : Measurable (J k t) :=
    liePathJet_measurable hH A I hA hI Ξ hm (k+1) t
  have hb := singleCell_interpolation_rms n hn (singleCellBasisBudget n)
    (singleCellBasisBudget_spec n).1 (singleCellBasisBudget_spec n).2 J hJ
    (((d+d:ℕ):ℝ)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+2)*centeringStateBudget (n+2))
    (by positivity [centeringStateBudget_nonneg (n+2)])
    (fun t ht => by
      simpa only [sub_zero,zero_add,Nat.zero_add] using
        centering_velocity_taylor_uniform hF x hr hlam hl hR hRT hT0 hT1 hs Ξ hder hm hlaw n 0 t
          le_rfl ht.1 ht.2) v hv
  let E := fun y => J 0 v y-interpolation (probabilityNodes n) (fun i => J 0 (probabilityNodes n i) y) v
  have hE : Measurable E := (hJ 0 v).sub
    (Finset.measurable_sum _ (fun i _ => (hJ 0 _).const_smul (basis (probabilityNodes n) i v)))
  have he (y : Point (d+d)) :
      V v y-interpolation (probabilityNodes n) (fun i => V (probabilityNodes n i) y) v=
        identityOutputProjection (d+d) (E y) := by
    simp only [E,map_sub,projection_interpolation,J,Nat.zero_add]
    simp only [identityOutputProjection_lie _ A hA (jointSkew_skew _ s),V,A,I]
  simp_rw [he]
  exact projection_rms (identityOutputEmbedding (d+d)) hE hb.1 hb.2

theorem centering_mean_interpolation_rms {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T s : ℝ}
    (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2)
    (hR : 0<R) (hRT : R^2 ≤ 1-T^2) (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0<s)
    (Ξ : Point (d+d) → ℝ → Point (d+d))
    (hder : ∀y t,t∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
      (skewLieField (centeringPotential F x r T)
        (jointSkew (centeringKernel hF x hr hl hT0 hT1) s) (Ξ y t)) (Icc (0:ℝ) 1) t)
    (hm : Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1))
    (hlaw : ∀t∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y t)=
      gibbs (centeringPotential F x r T)) (n : ℕ) (hn : 0<n) {v : ℝ} (hv : v∈Icc (0:ℝ) 1) :
    let M := fun t y => conditionalFieldMean F x r T (productPointEquiv d d (Ξ y t)).1
    Integrable (fun y => ‖M v y-interpolation (probabilityNodes n)
      (fun i => M (probabilityNodes n i) y) v‖^2) (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖M v y-interpolation (probabilityNodes n)
      (fun i => M (probabilityNodes n i) y) v‖^2 ∂gibbs (centeringPotential F x r T)) ≤
      4*(singleCellBasisBudget n)^2*
        ((d*((lam:ℝ)*r)^2)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+1)*centeringMeanBudget (n+1)) := by
  intro M
  let A := jointSkew (centeringKernel hF x hr hl hT0 hT1) s
  let I := centeringMeanArray F x r T
  let J := fun k t y => tensorVector (iterTensorLie (centeringPotential F x r T) A I k) (Ξ y t)
  have hH : PolySmooth (centeringPotential F x r T) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have hA := centeringSkew_polySmooth hF x hr hlam hl hT0 hT1 s
  have hI := centeringMeanArray_polySmooth hF x hr hlam hl hT0 hT1
  have hJ (k : ℕ) (t : ℝ) : Measurable (J k t) := liePathJet_measurable hH A I hA hI Ξ hm k t
  have hb := singleCell_interpolation_rms n hn (singleCellBasisBudget n)
    (singleCellBasisBudget_spec n).1 (singleCellBasisBudget_spec n).2 J hJ
    ((d*((lam:ℝ)*r)^2)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+1)*centeringMeanBudget (n+1))
    (by positivity [centeringMeanBudget_nonneg (n+1)])
    (fun t ht => by
      simpa only [J,iterTensorLie,sub_zero] using
        centering_mean_taylor_uniform hF x hr hlam hl hR hRT hT0 hT1 hs Ξ hder hm hlaw n 0 t
          le_rfl ht.1 ht.2) v hv
  let E := fun y => J 0 v y-interpolation (probabilityNodes n) (fun i => J 0 (probabilityNodes n i) y) v
  have hE : Measurable E := (hJ 0 v).sub
    (Finset.measurable_sum _ (fun i _ => (hJ 0 _).const_smul (basis (probabilityNodes n) i v)))
  have he (y : Point (d+d)) :
      M v y-interpolation (probabilityNodes n) (fun i => M (probabilityNodes n i) y) v=
        meanOutputProjection d (E y) := by
    simp only [E,map_sub,projection_interpolation,J,iterTensorLie,I,meanOutputProjection_mean,M]
  simp_rw [he]
  exact projection_rms (meanOutputEmbedding d) hE hb.1 hb.2
end LogConcaveSampling

end

end

end OAI
