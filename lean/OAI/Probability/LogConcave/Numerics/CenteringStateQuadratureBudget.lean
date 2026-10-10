import Mathlib
import OAI.Probability.LogConcave.Sampling.CenteringVelocityInterpolationRms
import OAI.Probability.LogConcave.Dynamics.StationaryPath

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature TensorEnergy
open scoped Classical BigOperators NNReal

local instance : DecidableEq Unit := Classical.decEq _

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r R T s : ℝ}
  (hr : 0<r) (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2)
  (hR : 0<R) (hRT : R^2 ≤ 1-T^2) (hT0 : 0 ≤ T) (hT1 : T<1) (hs : 0<s)
  (X : StationaryPath (gibbs (centeringPotential F x r T))
    (skewLieField (centeringPotential F x r T) (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)))

def centeringStateQuadratureBudget (n d : ℕ) (lam : ℝ≥0) (r R s : ℝ) : ℝ :=
  4*(singleCellBasisBudget n)^2*
    (((d+d:ℕ):ℝ)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+2)*centeringStateBudget (n+2))

def centeringMeanQuadratureBudget (n d : ℕ) (lam : ℝ≥0) (r R s : ℝ) : ℝ :=
  4*(singleCellBasisBudget n)^2*
    ((d*((lam:ℝ)*r)^2)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)^(n+1)*centeringMeanBudget (n+1))

lemma centeringStateQuadratureBudget_nonneg (n d : ℕ) (lam : ℝ≥0) (r R s : ℝ) :
    0 ≤ centeringStateQuadratureBudget n d lam r R s := by
  unfold centeringStateQuadratureBudget
  positivity [centeringStateBudget_nonneg (n+2)]

lemma centeringMeanQuadratureBudget_nonneg (n d : ℕ) (lam : ℝ≥0) (r R s : ℝ) :
    0 ≤ centeringMeanQuadratureBudget n d lam r R s := by
  unfold centeringMeanQuadratureBudget
  positivity [centeringMeanBudget_nonneg (n+1)]

include hlam hR hRT hs

theorem centering_state_quadrature_rms (n : ℕ) (hn : 0<n) (i : Fin (n+1)) :
    let V := skewLieField (centeringPotential F x r T)
      (jointSkew (centeringKernel hF x hr hl hT0 hT1) s)
    let e := fun y => X.path y (probabilityNodes n i)-y-
      ∑j,centeringWeight n i j • V (X.path y (probabilityNodes n j))
    Integrable (fun y => ‖e y‖^2) (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖e y‖^2 ∂gibbs (centeringPotential F x r T)) ≤ centeringStateQuadratureBudget n d lam r R s := by
  intro V e
  have hV := centeringTrueVelocity_continuous hF x hr hlam hl hT0 hT1 s
  have hH := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let : IsProbabilityMeasure (gibbs (centeringPotential F x r T)) :=
    probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  have hh (t : ℝ) (ht : t∈Icc (0:ℝ) 1) := centering_velocity_interpolation_rms
    hF x hr hlam hl hR hRT hT0 hT1 hs X.path X.derivative X.measurable X.law n hn ht
  have hb := singleCell_quadrature_rms n (fun t y => V (X.path y t))
    (hV.measurable.comp X.measurable) (fun y => (hV.comp (X.continuous y)).continuousOn)
    (centeringStateQuadratureBudget_nonneg n d lam r R s)
    (fun t ht => (hh t ht).1) (fun t ht => (hh t ht).2) (probabilityNodes_mem hn i)
  dsimp only [V] at hb
  simp_rw [X.integral_eq hV _ (probabilityNodes_mem hn i)] at hb
  exact hb

theorem centering_mean_quadrature_rms (n : ℕ) (hn : 0<n) :
    let M := fun y => conditionalFieldMean F x r T (productPointEquiv d d y).1
    let e := fun y => (∫t in 0..1,M (X.path y t))-
      ∑j,weight (probabilityNodes n) j 0 1 • M (X.path y (probabilityNodes n j))
    Integrable (fun y => ‖e y‖^2) (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖e y‖^2 ∂gibbs (centeringPotential F x r T)) ≤ centeringMeanQuadratureBudget n d lam r R s := by
  intro M e
  have hM : Continuous M := (conditionalFieldMean_lipschitz hF x hr.le hl hT0 hT1).continuous.comp
    (productPointEquiv d d).continuous.fst
  have hH := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let : IsProbabilityMeasure (gibbs (centeringPotential F x r T)) :=
    probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  have hh (t : ℝ) (ht : t∈Icc (0:ℝ) 1) := centering_mean_interpolation_rms
    hF x hr hlam hl hR hRT hT0 hT1 hs X.path X.derivative X.measurable X.law n hn ht
  exact singleCell_quadrature_rms n (fun t y => M (X.path y t))
    (hM.measurable.comp X.measurable) (fun y => (hM.comp (X.continuous y)).continuousOn)
    (centeringMeanQuadratureBudget_nonneg n d lam r R s)
    (fun t ht => (hh t ht).1) (fun t ht => (hh t ht).2) ⟨by norm_num,le_rfl⟩

theorem centering_initial_rms {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    Integrable (fun y => ‖X.path y t-y‖^2) (gibbs (centeringPotential F x r T)) ∧
    (∫y,‖X.path y t-y‖^2 ∂gibbs (centeringPotential F x r T)) ≤
      (((d+d:ℕ):ℝ)*(((lam:ℝ)*r/s)^2*(R⁻¹)^4)*centeringStateBudget 1) := by
  have hh := centering_state_taylor_uniform hF x hr hlam hl hR hRT hT0 hT1 hs
    X.path X.derivative X.measurable X.law 0 0 t le_rfl ht.1 ht.2
  simp only [chainTaylor,Nat.zero_add,Finset.range_one,Finset.sum_singleton,Nat.factorial_zero,
    Nat.cast_one,inv_one,pow_zero,one_mul,one_smul,iterTensorLie,X.initial,
    sub_zero,pow_one,div_one] at hh
  let E := fun y => tensorVector (vectorArray (id : Point (d+d) → Point (d+d))) (X.path y t)-
    tensorVector (vectorArray (id : Point (d+d) → Point (d+d))) y
  have hc := (tensorVector_contDiff _ (fun c => (identityArray_polySmooth (d+d) c).smooth)).continuous.measurable
  have hE : Measurable E := (hc.comp (X.measurable_slice t)).sub hc
  have he (y : Point (d+d)) : X.path y t-y=identityOutputProjection (d+d) (E y) := by
    simp only [E,map_sub,identityOutputProjection_vector,id_eq]
  simp_rw [he]
  apply projection_rms (identityOutputEmbedding (d+d)) hE hh.1
  apply hh.2.trans
  simp only [Nat.cast_add]
  exact mul_le_of_le_one_left (by positivity [centeringStateBudget_nonneg 1])
    (pow_le_one₀ ht.1 ht.2)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature RMSIntegral
open scoped Classical BigOperators NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsFiniteMeasure μ] {V Vhat : E → E}

def stationaryPicard (n N : ℕ) (Vhat : E → E) (y : E) (i : Fin (n+1)) : E :=
  FinitePicard.nodes (centeringWeight n) (fun _ => Vhat) (fun y _ => y) N y i

lemma stationaryPicard_measurable (n N : ℕ) (hm : Measurable Vhat) (i : Fin (n+1)) :
    Measurable (fun y => stationaryPicard n N Vhat y i) := by
  induction N generalizing i with
  | zero => exact measurable_id
  | succ N ih =>
    exact measurable_id.add (Finset.measurable_sum _ (fun j _ =>
      (hm.comp (ih j)).const_smul (centeringWeight n i j)))

theorem stationaryPicard_rms (X : StationaryPath μ V) (hV : Continuous V)
    {K : ℝ≥0} (hhat : LipschitzWith K Vhat) (hbase : MemLp (id : E → E) 2 μ)
    (n : ℕ) (hn : 0<n) (hq : centeringRowBudget n*K ≤ 1/2)
    {Bq Bv Bi : ℝ} (hBq : 0 ≤ Bq) (hBv : 0 ≤ Bv) (hBi : 0 ≤ Bi)
    (hquad : ∀i : Fin (n+1),
      Integrable (fun y => ‖X.path y (probabilityNodes n i)-y-
        ∑j,centeringWeight n i j • V (X.path y (probabilityNodes n j))‖^2) μ ∧
      (∫y,‖X.path y (probabilityNodes n i)-y-
        ∑j,centeringWeight n i j • V (X.path y (probabilityNodes n j))‖^2 ∂μ) ≤ Bq)
    (hvint : Integrable (fun y => ‖Vhat y-V y‖^2) μ)
    (hvel : (∫y,‖Vhat y-V y‖^2 ∂μ) ≤ Bv)
    (hinit : ∀i : Fin (n+1),(∫y,‖X.path y (probabilityNodes n i)-y‖^2 ∂μ) ≤ Bi)
    (N : ℕ) (i : Fin (n+1)) :
    Integrable (fun y => ‖stationaryPicard n N Vhat y i-X.path y (probabilityNodes n i)‖^2) μ ∧
    (∫y,‖stationaryPicard n N Vhat y i-X.path y (probabilityNodes n i)‖^2 ∂μ) ≤
      (2*Real.sqrt (2*(centeringRowBudget n:ℝ)^2*Bv+2*Bq)+
        ((centeringRowBudget n*K:ℝ≥0):ℝ)^N*Real.sqrt Bi)^2 := by
  have he (j : Fin (n+1)) : MemLp (fun y => X.path y (probabilityNodes n j)) 2 μ :=
    X.memLp_slice (probabilityNodes_mem hn j) hbase
  apply FinitePicard.nodes_rms (centeringWeight n) (fun _ => Vhat) (fun _ => hhat)
    (fun _ y => y) (fun j y => X.path y (probabilityNodes n j)) (fun _ => hbase) he
    (centeringWeight_bound n hn) hq (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) _ _ N i
  · intro k
    let e := fun j y => Vhat (X.path y (probabilityNodes n j))-V (X.path y (probabilityNodes n j))
    have hem (j : Fin (n+1)) : Measurable (e j) :=
      (hhat.continuous.measurable.sub hV.measurable).comp (X.measurable_slice _)
    have heb (j : Fin (n+1)) := rms_bound_pullback (X.measurable_slice (probabilityNodes n j))
      (X.law _ (probabilityNodes_mem hn j)) (hhat.continuous.measurable.sub hV.measurable) hvint hvel
    have hsum := weighted_sum_sq (centeringWeight n k) e (fun j => (hem j).aestronglyMeasurable)
      (fun j => (heb j).1) (fun j => (heb j).2)
    let q := fun y => X.path y (probabilityNodes n k)-y-
      ∑j,centeringWeight n k j • V (X.path y (probabilityNodes n j))
    have hqm : Measurable q := ((X.measurable_slice _).sub measurable_id).sub
      (Finset.measurable_sum _ (fun j _ =>
        (hV.measurable.comp (X.measurable_slice _)).const_smul (centeringWeight n k j)))
    have hsm : Measurable (fun y => ∑j,centeringWeight n k j • e j y) :=
      Finset.measurable_sum _ (fun j _ => (hem j).const_smul _)
    have hh := sub_sq_bound hsm.aestronglyMeasurable hqm.aestronglyMeasurable
      hsum.1 (hquad k).1 hsum.2 (hquad k).2
    have hid (y : E) : FinitePicard.step (centeringWeight n) (fun _ => Vhat) (fun _ => y)
        (fun j => X.path y (probabilityNodes n j)) k-X.path y (probabilityNodes n k)=
      (∑j,centeringWeight n k j • e j y)-q y := by
      simp only [FinitePicard.step,Pi.add_apply,FinitePicard.correction,e,q,smul_sub,Finset.sum_sub_distrib]
      abel
    simp_rw [hid]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2*(centeringRowBudget n:ℝ)^2*Bv+2*Bq)]
    apply hh.2.trans
    have hw := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      (centeringWeight_bound n hn k) 2
    have hwv := mul_le_mul_of_nonneg_right hw hBv
    nlinarith
  · intro k
    rw [Real.sq_sqrt hBi]
    simpa only [norm_sub_rev] using hinit k
end LogConcaveSampling

end

end

end OAI
