import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Regularity

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators ContDiff Topology
namespace ShearFlows

theorem opposite_faces_translate (L : ℝ) (j : Fin 3) (x : Fin 2 → ℝ) :
    j.insertNth L x = j.insertNth 0 x + latticeVector L (Pi.single j (1 : ℤ)) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨k, rfl⟩
  · simp [latticeVector]
  · simp [latticeVector, Fin.succAbove_ne]

theorem integral_periodic_derivative {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {L : ℝ} (hL : 0 ≤ L)
    {g : Space → E} (hg : ContDiff ℝ ∞ g) (hp : CubePeriodic L g) (j : Fin 3) :
    (∫ x in fundamentalCube L, fderiv ℝ g x (basis j)) = 0 := by
  let F : Fin 3 → Space → E := fun k => if k = j then g else fun _ => 0
  let F' : Fin 3 → Space → Space →L[ℝ] E := fun k x => if k = j then fderiv ℝ g x else 0
  have he (x : Space) : (∑ k, F' k x (Pi.single k 1)) = fderiv ℝ g x (basis j) := by
    simp [F', basis, apply_ite, ite_apply]
  have hc : ∀ k, ContinuousOn (F k) (fundamentalCube L) := by
    intro k
    by_cases hk : k = j <;> simp only [F, hk, ite_true, ite_false]
    · exact hg.continuous.continuousOn
    · exact continuousOn_const
  have hd : ∀ x : Space, ∀ k, HasFDerivAt (F k) (F' k x) x := by
    intro x k
    by_cases hk : k = j <;> simp only [F, F', hk, ite_true, ite_false]
    · exact (hg.differentiable (by simp) x).hasFDerivAt
    · exact hasFDerivAt_const _ _
  have hi : IntegrableOn (fun x => ∑ k, F' k x (Pi.single k 1)) (fundamentalCube L) := by
    simp_rw [he]
    exact ((hg.continuous_fderiv (by simp)).clm_apply continuous_const).integrableOn_Icc
  have ht := integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Space) (fun _ => L) (fun _ => hL) F F' ∅ countable_empty hc
    (fun x _ k => hd x k) hi
  simp only [he] at ht
  change (∫ x in Icc (0 : Space) (fun _ => L), fderiv ℝ g x (basis j)) = 0
  rw [ht]
  apply Finset.sum_eq_zero
  intro k _
  have hf (x : Fin 2 → ℝ) : F k (k.insertNth L x) = F k (k.insertNth 0 x) := by
    by_cases hk : k = j
    · simp only [F, hk, ite_true]
      rw [opposite_faces_translate]
      exact hp _ _
    · simp [F, hk]
  simp only [Pi.zero_apply, hf, sub_self]

theorem laplacian_mean_zero {L : ℝ} (hL : 0 ≤ L) {V : Velocity}
    (hV : ContDiff ℝ ∞ V) (hp : SpatiallyPeriodic L V) :
    HasZeroMean L (fun y => laplacian (fun x => V (y.1,x)) y.2) := by
  intro t
  simp only [laplacian_eq_mixed hV]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro j _
    have hc := mixedDerivative_smooth hV [j.succ]
    have hp' := mixedDerivative_spatially_periodic hV hp [j.succ]
    have he (x : Space) : mixedDerivative V [j.succ,j.succ] (t,x) =
        fderiv ℝ (fun y => mixedDerivative V [j.succ] (t,y)) x (basis j) :=
      (spatialDerivative_eq_mixed hc t x j).symm
    simp_rw [he]
    exact integral_periodic_derivative hL (hc.comp (contDiff_const.prodMk contDiff_id))
      (hp' t) j
  · intro j _
    exact ((mixedDerivative_smooth hV [j.succ,j.succ]).continuous.comp
      (continuous_const.prodMk continuous_id)).integrableOn_Icc

theorem timeDerivative_pulsedSum {ι : Type*} [Fintype ι]
    (b : ι → ℝ → ℝ) (W : ι → Space → Space)
    (hb : ∀ j, Differentiable ℝ (b j)) (t : ℝ) (x : Space) :
    timeDerivative (pulsedSum b W) t x = ∑ j, deriv (b j) t • W j x := by
  exact (HasDerivAt.fun_sum (fun j _ => (hb j t).hasDerivAt.smul_const (W j x))).deriv

theorem realizingForce_mean_zero {d : Input} (hd : ValidInput d) (ν : ℝ) :
    HasZeroMean d.period (force ν d.realizingVelocity) := by
  have hV := realizingVelocity_smooth hd
  have ht : HasZeroMean d.period (fun y => timeDerivative d.realizingVelocity y.1 y.2) := by
    have he (t : ℝ) (x : Space) : timeDerivative d.realizingVelocity t x =
        pulsedSum (fun j => deriv (periodPulse j)) d.spatialFields (t,x) :=
      timeDerivative_pulsedSum _ _ (fun j => (periodPulse_smooth j).differentiable (by simp)) _ _
    simpa only [he] using pulsedSum_mean_zero (fun j => deriv (periodPulse j)) d.spatialFields
      d.period (fun j => (spatialFields_smooth hd j).continuous) (spatialFields_mean_zero hd)
  have hl := laplacian_mean_zero (show (0 : ℝ) ≤ d.period by exact_mod_cast hd.period_pos.le)
    hV (realizingVelocity_spatially_periodic d)
  intro t
  change (∫ x in fundamentalCube d.period,
    timeDerivative d.realizingVelocity t x - ν • laplacian (fun y => d.realizingVelocity (t,y)) x) = 0
  rw [integral_sub]
  · simp [integral_smul, ht t, hl t]
  · exact ((timeDerivative_smooth hV).continuous.comp
      (continuous_const.prodMk continuous_id)).integrableOn_Icc
  · exact (((laplacian_smooth hV).continuous.comp
      (continuous_const.prodMk continuous_id)).const_smul ν).integrableOn_Icc

theorem fderiv_eval_direction {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} (hg : ContDiff ℝ ∞ g)
    (x v w : E) : fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fderiv ℝ g) x w v := by
  rw [fderiv_clm_apply ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    (differentiableAt_const v)]
  simp

theorem mixedDerivative_commute {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (α : List (Fin 4)) (i j : Fin 4) :
    mixedDerivative V (i :: j :: α) = mixedDerivative V (j :: i :: α) := by
  funext x
  simp only [mixedDerivative]
  rw [fderiv_eval_direction (mixedDerivative_smooth hV α),
    fderiv_eval_direction (mixedDerivative_smooth hV α)]
  exact ((mixedDerivative_smooth hV α).contDiffAt.isSymmSndFDerivAt (by simp)) _ _

theorem fderiv_coordinate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → Space} (hg : Differentiable ℝ g) (x v : E) (j : Fin 3) :
    fderiv ℝ (fun y => g y j) x v = fderiv ℝ g x v j := by
  have hf := ((ContinuousLinearMap.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp x
    (hg x).hasFDerivAt).fderiv
  exact congrArg (fun A : E →L[ℝ] ℝ => A v) hf

theorem solenoidal_one_mixed {V : Velocity} (hV : ContDiff ℝ ∞ V)
    (hd : Solenoidal V) (a : Fin 4) : Solenoidal (mixedDerivative V [a]) := by
  have hzero : (fun x : SpaceTime => ∑ j : Fin 3, mixedDerivative V [j.succ] x j) =
      fun _ => 0 := by
    funext x
    simpa only [divergence, spatialDerivative_eq_mixed hV] using hd x.1 x.2
  have hh (j : Fin 3) := (mixedDerivative_smooth hV [j.succ]).differentiable (by simp)
  intro t x
  have he : (∑ j : Fin 3, mixedDerivative V [a,j.succ] (t,x) j) = 0 := by
    have hdif := congrArg (fun g : SpaceTime → ℝ => fderiv ℝ g (t,x) (spaceTimeDirection a)) hzero
    rw [fderiv_fun_sum (A := fun j y => mixedDerivative V [j.succ] y j)
      (fun j _ => differentiableAt_pi.mp (hh j (t,x)) j)] at hdif
    have hdcoord (j : Fin 3) := fderiv_coordinate (hh j) (t,x) (spaceTimeDirection a) j
    simp only [sum_apply, hdcoord, fderiv_fun_const, Pi.zero_apply, zero_apply] at hdif
    exact hdif
  have hc (j : Fin 3) := congrFun (mixedDerivative_commute hV [] a j.succ) (t,x)
  simp_rw [hc] at he
  unfold divergence
  simp_rw [spatialDerivative_eq_mixed (mixedDerivative_smooth hV [a])]
  exact he

theorem mixedDerivative_cons_eq (V : Velocity) (a : Fin 4) (α : List (Fin 4)) :
    mixedDerivative V (a :: α) = mixedDerivative (mixedDerivative V α) [a] := rfl

theorem solenoidal_mixed {V : Velocity} (hV : ContDiff ℝ ∞ V) (hd : Solenoidal V) :
    ∀ α, Solenoidal (mixedDerivative V α) := by
  intro α
  induction α with
  | nil => exact hd
  | cons a α ih => exact solenoidal_one_mixed (mixedDerivative_smooth hV α) ih a

theorem divergence_sub {W U : Space → Space} (hW : Differentiable ℝ W)
    (hU : Differentiable ℝ U) (x : Space) :
    divergence (fun y => W y - U y) x = divergence W x - divergence U x := by
  simp only [divergence, derivative, fderiv_fun_sub (hW x) (hU x),
    sub_apply, Pi.sub_apply, Finset.sum_sub_distrib]

theorem divergence_sum {ι : Type*} [Fintype ι] (W : ι → Space → Space)
    (hW : ∀ j, Differentiable ℝ (W j)) (x : Space) :
    divergence (fun y => ∑ j, W j y) x = ∑ j, divergence (W j) x := by
  simp only [divergence, derivative, fderiv_fun_sum (fun j _ => hW j x),
    sum_apply, Finset.sum_apply]
  exact Finset.sum_comm

theorem force_solenoidal {V : Velocity} (hV : ContDiff ℝ ∞ V) (hd : Solenoidal V) (ν : ℝ) :
    Solenoidal (force ν V) := by
  intro t x
  have he : (fun y => force ν V (t,y)) = fun y => mixedDerivative V [0] (t,y) -
      ν • ∑ j : Fin 3, mixedDerivative V [j.succ,j.succ] (t,y) :=
    funext (fun y => force_eq_mixed hV ν (t,y))
  have hc (α) : Differentiable ℝ (fun y => mixedDerivative V α (t,y)) :=
    ((mixedDerivative_smooth hV α).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hs := Differentiable.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hc [j.succ,j.succ])
  rw [he, divergence_sub (hc [0]) (hs.fun_const_smul ν),
    divergence_const_smul (hs x), divergence_sum (fun (j : Fin 3) y => mixedDerivative V [j.succ,j.succ] (t,y))
      (fun j => hc [j.succ,j.succ])]
  have hz (α) : divergence (fun y => mixedDerivative V α (t,y)) x = 0 :=
    solenoidal_mixed hV hd α t x
  simp only [hz, Finset.sum_const_zero, mul_zero, sub_self]

end ShearFlows

end

end OAI
