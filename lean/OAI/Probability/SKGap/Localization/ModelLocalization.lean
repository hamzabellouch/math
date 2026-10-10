import Mathlib
import OAI.Probability.SKGap.Stability.RootGrid
import OAI.Probability.SKGap.Posterior.StaticExperimentBridge

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology BigOperators ENNReal
open GaussianStep GaussianHistory ObservationBridge SKGapCutoff.Recipe SKGapCutoff.Static
noncomputable section
variable {n : ℕ}

theorem poincare_from_model_data (g : Disorder n) (hn : 0<n)
    (j Ar K ε c r₀ ρ C₀ Cmean D₀ W a aT b T : ℝ)
    (hAr : 1≤Ar) (hD₀ : 0≤D₀) (hW : 0≤W) (hCmean : 0≤Cmean)
    (ha : 0<a) (hb : 0<b) (hT : 0<T) (hlead : 4*C₀*ρ≤W)
    (hop : operatorBound K (coupling g))
    (hroot : gridFailure n j Ar K ε c r₀ T g≤exp (-a*(n:ℝ)))
    (hterminal : (gaussianChannelLaw g T).real {z | ¬∀f:Spin n→ℝ,
      variance g (fun i=>sqrt T*z i) f≤2*dirichlet g (fun i=>sqrt T*z i) f}≤exp (-aT*(n:ℝ)))
    (hcov : PosteriorCovarianceProperty j Ar ε c r₀ D₀ g)
    (hmean : StableSquareMeanProperty j c r₀ ρ C₀ Cmean (coupling g))
    (hrare : exp (-a*(n:ℝ))+exp (-aT*(n:ℝ))≤exp (-b*(n:ℝ)))
    (hmesh : 4*(n:ℝ)*gridStep T n≤1)
    (hmeshD : D₀^2*gridStep T n≤1/2)
    (hloss : localizationLoss n (gridStep T n) W (2*Cmean) a b T≤exp (-2*D₀^2*T)/2)
    (hcost : localizationCost n (2*Cmean) a b (D₀^2) 2 T≤D₀^2*T+3) :
    ∀f:Spin n→ℝ,variance g 0 f≤(2*(D₀^2*T+3)/exp (-2*D₀^2*T))*dirichlet g 0 f := by
  let t:=gridStep T n
  have ht : 0≤t:=gridStep_nonneg hT.le n
  let B : ∀k,Set (History n k):=fun k=>{h | rootBad j Ar ε c r₀ (coupling g) (GaussianHistory.field t h)}
  have hB (k : ℕ) : MeasurableSet (B k):=
    (measurable_rootFields g j Ar ε c r₀).preimage (continuous_field t k).measurable
  let F:Set (History n (gridSteps n)):= {h | ¬∀f:Spin n→ℝ,
    variance g (GaussianHistory.field t h) f≤2*dirichlet g (GaussianHistory.field t h) f}
  have hF : MeasurableSet F:=
    ((terminal_goodSet_closed g 2).measurableSet.compl).preimage (continuous_field t (gridSteps n)).measurable
  let E:Set (History n (gridSteps n)):=(goodPrefix B (gridSteps n))ᶜ∪F
  have hE : MeasurableSet E:=(measurable_goodPrefix B hB _).compl.union hF
  have hsum : (∑k∈Finset.range (gridSteps n+1),eventProbability (gibbsPrior g 0) t (B k))=
      gridFailure n j Ar K ε c r₀ T g := by
    apply Finset.sum_congr rfl
    intro k _
    exact history_root_probability g ht k j Ar K ε c r₀ hop
  have hsmall (k : ℕ) (hk : k<gridSteps n) :
      eventProbability (gibbsPrior g 0) t (B k)≤exp (-a*(n:ℝ)) := by
    exact (bad_term_le_sum (gibbsPrior g 0) t B hk.le).trans (hsum.symm ▸ hroot)
  have hFsmall : eventProbability (gibbsPrior g 0) t F≤exp (-aT*(n:ℝ)) := by
    rw [history_terminal_probability g ht (gridSteps n)]
    simpa only [t,grid_total] using hterminal
  have hEsmall : eventProbability (gibbsPrior g 0) t E≤exp (-b*(n:ℝ)) := by
    have hp:=(goodPrefix_failure_bound (gibbsPrior g 0) ht B hB (gridSteps n))
    rw [hsum] at hp
    exact (eventProbability_union_le (gibbsPrior g 0) ht _ _
      (measurable_goodPrefix B hB _).compl hF).trans ((add_le_add (hp.trans hroot) hFsmall).trans hrare)
  have hpfield {k : ℕ} (h : History n k) :
      GaussianHistory.posterior (gibbsPrior g 0) t h=gibbsPrior g (GaussianHistory.field t h) := by
    simpa only [zero_add] using posterior_gibbs_field g 0 t h
  have hD : 0≤D₀^2:=sq_nonneg D₀
  have hconst : 0≤D₀^2*T+3:=by positivity
  have H:=poincare_of_history_estimates (gibbsPrior g 0) (mass_pos g 0) hn ht hmesh
    (gridSteps n) B (goodPrefix B) hB (measurable_goodPrefix B hB) E hE
    (fun k _ h hh=>goodPrefix_previous B k h hh) subset_union_left
    (D₀^2) W (2*Cmean) a b 2 T (D₀^2*T+3) hD hW (by positivity) ha hb (by norm_num) hconst
    hmeshD (grid_total T n) hsmall hEsmall
    (fun f hf k _ h hh=>?_) (fun f k _ h hh=>?_) (fun f h hh=>?_) hloss hcost
  · intro f
    simpa only [gibbsPrior_var,gibbsPrior_energy] using H f
  · have hppos : 0<avg (gibbsPrior g (GaussianHistory.field t h)) (fun x=>(f x)^2) := by
      rw [←hpfield h]
      exact posterior_square_pos (gibbsPrior g 0) f hf t h
    have hm:=drift_square_of_stable_mean hn hAr hmean (GaussianHistory.field t h) hh f hppos
    simp only [driftSquare,GaussianHistory.squarePrior_posterior,hpfield]
    apply hm.trans
    exact add_le_add (mul_le_mul_of_nonneg_right hlead (Nat.cast_nonneg n)) le_rfl
  · rw [hpfield h]
    exact covariance_square_bound hD₀ hcov (GaussianHistory.field t h)
      (goodPrefix_not_bad B k h hh) f
  · rw [hpfield h,gibbsPrior_var,gibbsPrior_energy]
    have hnF : h∉F:=fun hhF=>hh (Or.inr hhF)
    exact (not_not.mp hnF) f

end
end SKGap.FullMain

end OAI
