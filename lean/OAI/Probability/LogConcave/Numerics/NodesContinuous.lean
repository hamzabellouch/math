import Mathlib
import OAI.Probability.LogConcave.Numerics.ReanchorWeight
import OAI.Probability.LogConcave.Sampling.ProbabilityTransportTrajectory

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory FinitePicard
open scoped Classical BigOperators NNReal

lemma FinitePicard.nodes_continuous {I E X : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace X]
    (w : I → I → ℝ) (φ : I → E → E) (a : X → I → E)
    (hφ : ∀i,Continuous (φ i)) (ha : Continuous a) (N : ℕ) :
    Continuous (nodes w φ a N) := by
  induction N with
  | zero => exact ha
  | succ N ih =>
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp ha).add (continuous_finsetSum _ (fun j _ =>
      ((hφ j).comp ((continuous_apply j).comp ih)).const_smul (w i j)))

lemma probabilityAnchored_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T h : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n : ℕ) (hn : 0<n) (N : ℕ) (s i : ProbabilityNode T h n) :
    Continuous (fun y => probabilityAnchoredPicard F x r T h n N s y i) := by
  apply (continuous_apply i).comp
  apply FinitePicard.nodes_continuous
  · intro j
    have hj := probabilityNodeTime_mem hT0 hT1 hh hn j
    exact (probabilityMeanVelocity_lipschitz hF x hr hl hj.1 (hj.2.trans_lt hT1)).continuous
  · exact continuous_pi (fun _ => continuous_id)

theorem probabilityAnchored_marginal_rms (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0<r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
      A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,∀s i : ProbabilityNode T h n,
      let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
      let I : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n i,probabilityNodeTime_mem hT0 hT1 hh hn i⟩
      Integrable (fun y => ‖probabilityAnchoredPicard F x r T h n N s y i-
        probabilityTransport hF x hr.le hl hT0.le hT1 S I y‖^2)
          (interpolationLaw F x r S) ∧
      (∫y,‖probabilityAnchoredPicard F x r T h n N s y i-
        probabilityTransport hF x hr.le hl hT0.le hT1 S I y‖^2
          ∂interpolationLaw F x r S)≤
        (4*C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1)+
          (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(2*probabilityInitialRms F x lam r))^2 := by
  obtain ⟨A,C,hC,k,h⟩ := probabilityAnchored_rms n hn
  refine ⟨A,C,hC,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T hstep hT0 hT1 hh hsmall hq N s i
  dsimp only
  let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T hstep n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
  let I : Icc (0:ℝ) T := ⟨probabilityNodeTime T hstep n i,probabilityNodeTime_mem hT0 hT1 hh hn i⟩
  let E := fun y => ‖probabilityAnchoredPicard F x r T hstep n N s y i-
    probabilityTransport hF x hr.le hl hT0.le hT1 S I y‖^2
  have hE : Continuous E := ((probabilityAnchored_continuous hF x hr.le hl hT0 hT1 hh n hn N s i).sub
    (probabilityTransport_continuous hF x hr.le hl hT0.le hT1 S I)).norm.pow 2
  have hm := fullProbabilityFlow_interpolation_closed hF x hr.le hl S.2.1 (S.2.2.trans_lt hT1)
  have hf := (fullProbabilityFlow_lipschitz hF x hr.le hl ⟨S.2.1,S.2.2.trans hT1.le⟩).continuous.measurable
  have heq (z : Point d) : E (fullProbabilityFlow hF x hr.le hl S z)=
      ‖probabilityAnchoredPicard F x r T hstep n N s
          (fullProbabilityFlow hF x hr.le hl S z) i-fullProbabilityFlow hF x hr.le hl I z‖^2 := by
    dsimp only [E]
    rw [probabilityTransport_trajectory]
  have he := h hF x hr hlam hl hd hT0 hT1 hh hsmall hq N s i
  change Integrable E (interpolationLaw F x r S) ∧ _
  constructor
  · rw [←hm]
    apply (integrable_map_measure hE.aestronglyMeasurable hf.aemeasurable).mpr
    simpa only [Function.comp_def,heq] using he.1
  · change (∫y,E y ∂interpolationLaw F x r S)≤_
    rw [←hm,integral_map hf.aemeasurable hE.aestronglyMeasurable]
    simpa only [heq] using he.2

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal

theorem harmonicPicard_stationary_rms (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∃C : ℝ,1≤C ∧ ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r R T : ℝ},
      0<r → 0<lam → (lam:ℝ)*r^2≤1/2 → 0<R → R^2≤1-T^2 → 0≤T → T<1 →
      ∀Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y,Continuous (Ξ y)) → (∀y,Ξ y 0=y) →
      (∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (centeringPotential F x r T) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v) →
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) →
      (∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y v)=
        gibbs (centeringPotential F x r T)) →
      ∀z : ℝ,0≤z → z≤1 → A*probabilityMeanLipschitz lam r≤1/2 →
      ∀N : ℕ,∀i : Fin (n+1),
      Integrable (fun y => ‖harmonicPicard F x r T z n N (productPointEquiv d d y) i-
        (productPointEquiv d d (Ξ y (z*probabilityNodes n i))).1‖^2)
          (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖harmonicPicard F x r T z n N (productPointEquiv d d y) i-
        (productPointEquiv d d (Ξ y (z*probabilityNodes n i))).1‖^2
          ∂gibbs (centeringPotential F x r T))≤
        (2*(r*T)*Real.sqrt (4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
          ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)))+
          (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(r*T)*
            Real.sqrt (harmonicStationaryMoment F x r T))^2 := by
  obtain ⟨A,hA⟩ := harmonicWeight_budget n hn
  obtain ⟨C,hC,hErr⟩ := harmonic_mean_quadrature_rms n hn
  refine ⟨A,C,hC,?_⟩
  intro d F lam hF x r R T hr hlam hl hR hRT hT0 hT1 Ξ hc hinit hder hm hlaw z hz hz1 hq N i
  have hH := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have ht := productPotential_lowerTail
    (interpolationPotential_lowerTail hF x hr.le (by linarith) hT0 hT1) (gaussianPotential_lowerTail d)
  let : IsProbabilityMeasure (gibbs (centeringPotential F x r T)) :=
    probability_gibbs_of_gaussianTail hH.smooth.continuous ht
  let B := 4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
    ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1))
  have hB : 0≤B := by dsimp [B]; positivity [harmonicMeanBudget_nonneg (n+1)]
  let D := (r*T)*Real.sqrt B
  let H := (r*T)*Real.sqrt (harmonicStationaryMoment F x r T)
  have hD : 0≤D := by dsimp [D]; positivity
  have hH0 : 0≤H := by dsimp [H]; positivity
  have ha (j : Fin (n+1)) : MemLp (fun y : Point (d+d) =>
      harmonicFree n z (productPointEquiv d d y) j) 2 (gibbs (centeringPotential F x r T)) := by
    apply centering_lipschitz_memLp hF x hr hlam hl hT0 hT1
    exact (LipschitzWith.eval j).comp ((harmonicFree_lipschitz n z).comp (productPointEquiv d d).lipschitzWith)
  have hi (j : Fin (n+1)) : z*probabilityNodes n j∈Icc (0:ℝ) 1 :=
    ⟨mul_nonneg hz (probabilityNodes_mem hn j).1,
      (mul_le_of_le_one_right hz (probabilityNodes_mem hn j).2).trans hz1⟩
  have he (j : Fin (n+1)) : MemLp (fun y : Point (d+d) =>
      (productPointEquiv d d (Ξ y (z*probabilityNodes n j))).1) 2
        (gibbs (centeringPotential F x r T)) := by
    have hproj := centering_lipschitz_memLp hF x hr hlam hl hT0 hT1
      (LipschitzWith.prod_fst.comp (productPointEquiv d d).lipschitzWith)
    exact hproj.comp_measurePreserving ⟨hm.comp (measurable_const.prodMk measurable_id),hlaw _ (hi j)⟩
  have hdef (j : Fin (n+1)) :
      (∫y,‖FinitePicard.step (harmonicWeight n z) (fun _ => harmonicMeanVelocity F x r T)
        (harmonicFree n z (productPointEquiv d d y))
        (fun j => (productPointEquiv d d (Ξ y (z*probabilityNodes n j))).1) j-
        (productPointEquiv d d (Ξ y (z*probabilityNodes n j))).1‖^2
          ∂gibbs (centeringPotential F x r T))≤D^2 := by
    simp_rw [harmonicPicard_exact_defect hF x hr.le hl hT0 hT1 Ξ hc hinit hder hz hz1 n hn,
      norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    rw [integral_const_mul]
    dsimp only [D]
    simp only [mul_pow,Real.sq_sqrt hB]
    exact mul_le_mul_of_nonneg_left
      (hErr hF x hr hlam hl hR hRT hT0 hT1 Ξ hc hder hm hlaw z hz hz1 j).2
        (mul_nonneg (sq_nonneg r) (sq_nonneg T))
  have hstart (j : Fin (n+1)) :
      (∫y,‖harmonicFree n z (productPointEquiv d d y) j-
        (productPointEquiv d d (Ξ y (z*probabilityNodes n j))).1‖^2
          ∂gibbs (centeringPotential F x r T))≤H^2 := by
    dsimp only [H]
    rw [mul_pow,Real.sq_sqrt (harmonicStationaryMoment_nonneg F x r T)]
    exact (harmonicFree_initial_rms hF x hr hlam hl hT0 hT1 Ξ hc hinit hder hm hlaw hz hz1 n hn j).2
  have hout := FinitePicard.nodes_rms (A:=A) (harmonicWeight n z)
    (fun _ => harmonicMeanVelocity F x r T)
    (fun _ => harmonicMeanVelocity_lipschitz hF x hr.le hl hT0 hT1)
    (fun j y => harmonicFree n z (productPointEquiv d d y) j)
    (fun j y => (productPointEquiv d d (Ξ y (z*probabilityNodes n j))).1)
    ha he (hA z hz hz1) hq hD hH0 hdef hstart N i
  simpa only [harmonicPicard,FinitePicard.nodes_eq_iterate,D,H,B,mul_assoc] using hout
end LogConcaveSampling

end

end

end

end OAI
