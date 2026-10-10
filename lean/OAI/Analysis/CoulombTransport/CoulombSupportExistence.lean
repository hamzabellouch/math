import OAI.Analysis.CoulombTransport.CoulombCharts
import OAI.Analysis.CoulombTransport.LocalCertificate
import OAI.Analysis.CoulombTransport.StateDual
import OAI.Analysis.CoulombTransport.StationaryMap

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff RealInnerProductSpace

namespace Problem356.CoulombSupportExistence

open CoulombCalculus GeometryJets LocalGeometry

/-- The two explicit conventions for the stationary field coincide. -/
theorem stationary_eq (a : E3) :
    StationaryMap.stationary a = stationaryEquation 20 a := by
  funext p
  apply Prod.ext
  · rfl
  · simp only [StationaryMap.stationary, stationaryEquation]
    have hn (x y : E3) : pairGradient (x - y) = -pairGradient (y - x) := by
      rw [← neg_sub y x, pairGradient_neg]
    rw [hn p.2.2 p.2.1, hn p.2.2 p.1]
    module

private def D (a y : E3) (s : E3 × E3) : (E3 × E3) →L[ℝ] ℝ :=
  stateDual E3 E3 (stationaryEquation 20 a (y, s))

private def H (a y : E3) (s : E3 × E3) :
    (E3 × E3) →L[ℝ] ((E3 × E3) →L[ℝ] ℝ) :=
  (stateDual E3 E3).comp
    ((fderiv ℝ (stationaryEquation 20 a) (y, s)).comp
      (ContinuousLinearMap.inr ℝ E3 (E3 × E3)))

private theorem D_eq (a y : E3) (s : E3 × E3) :
    D a y s = StationaryMap.stateDifferential a y s := by
  unfold D
  rw [← stationary_eq]
  rfl

/-- The actual Coulomb stationary charts admit a local supporting potential
with exact equality precisely on the stationary branch. -/
theorem nonempty_coulombLocalSupportingCharts (k : Fin 3) :
    Nonempty (LocalSupportingCharts
      (StationaryMap.jointPotential (axisVector k))
      (stationaryEquation 20 (axisVector k))
      (axisVector k) (0, -axisVector k)) := by
  let a : E3 := axisVector k
  have ha : ‖a‖ = 1 := norm_axisVector k
  have ha0 : a ≠ 0 := axisVector_ne_zero k
  have haminus : a ≠ -a := by
    intro h
    have hh := congrArg (fun x : E3 => x k) h
    norm_num [a, axisVector] at hh
  have hsep : ∀ᶠ q : E3 × (E3 × E3) in 𝓝 (a, (0, -a)),
      q.2.1 ≠ q.1 ∧ q.2.1 ≠ q.2.2 ∧ q.2.2 ≠ q.1 := by
    have h₁ : ∀ᶠ q : E3 × (E3 × E3) in 𝓝 (a, (0, -a)), q.2.1 ≠ q.1 :=
      (isOpen_ne_fun (f := fun q : E3 × (E3 × E3) => q.2.1)
        (g := fun q => q.1) (by fun_prop) (by fun_prop)).mem_nhds ha0.symm
    have h₂ : ∀ᶠ q : E3 × (E3 × E3) in 𝓝 (a, (0, -a)), q.2.1 ≠ q.2.2 :=
      (isOpen_ne_fun (f := fun q : E3 × (E3 × E3) => q.2.1)
        (g := fun q => q.2.2) (by fun_prop) (by fun_prop)).mem_nhds
          (neg_ne_zero.mpr ha0).symm
    have h₃ : ∀ᶠ q : E3 × (E3 × E3) in 𝓝 (a, (0, -a)), q.2.2 ≠ q.1 :=
      (isOpen_ne_fun (f := fun q : E3 × (E3 × E3) => q.2.2)
        (g := fun q => q.1) (by fun_prop) (by fun_prop)).mem_nhds haminus.symm
    exact h₁.and (h₂.and h₃)
  obtain ⟨C⟩ := CoulombCharts.nonempty_coulombCharts k
  apply nonempty_localSupportingCharts (D := D a) (H := H a) C
  · exact StationaryMap.contDiffAt_jointPotential a ha0.symm
      (neg_ne_zero.mpr ha0).symm haminus.symm
  · filter_upwards [hsep] with q hq
    change HasFDerivAt (StationaryMap.statePotential a q.1) (D a q.1 q.2) q.2
    rw [D_eq]
    exact StationaryMap.hasFDerivAt_statePotential a q.1 hq.1 hq.2.1 hq.2.2
  · filter_upwards [hsep] with q hq
    have hG := (contDiffAt_stationaryEquation (n := ω) 20 a q hq.1 hq.2.1
      hq.2.2.symm).differentiableAt (by simp)
    have hp : HasFDerivAt (fun z : E3 × E3 => (q.1, z))
        (ContinuousLinearMap.inr ℝ E3 (E3 × E3)) q.2 := by
      exact hasFDerivAt_prodMk_right q.1 q.2
    have hpartial := hG.hasFDerivAt.comp q.2 hp
    convert! hasFDerivAt_stateDual_comp E3 E3 hpartial using 1
  · have hc := (contDiffAt_stationaryEquation_center (n := ω) 20 a ha).continuousAt_fderiv
      (by simp)
    exact continuousAt_const.clm_comp (hc.clm_comp continuousAt_const)
  · intro v hv
    change 0 < ((stateDual E3 E3).comp
      ((fderiv ℝ (stationaryEquation 20 (axisVector k))
        (axisVector k, (0, -axisVector k))).comp
          (ContinuousLinearMap.inr ℝ E3 (E3 × E3)))) v v
    rw [CoulombCharts.stationary_state_partial_eq, stateDual_comp_quadratic]
    have hc := LocalHessian.stateOperator_coercive k v
    have hp : 0 < (16 : ℝ) * ‖v‖ ^ 2 := by positivity
    exact hp.trans_le hc
  · intro q hq
    simp only [D, a, Prod.eta, hq, map_zero]

/-- The supporting charts in the scalar-potential stationary convention. -/
theorem nonempty_coulombLocalSupportingCharts_stationary (k : Fin 3) :
    Nonempty (LocalSupportingCharts
      (StationaryMap.jointPotential (axisVector k))
      (StationaryMap.stationary (axisVector k))
      (axisVector k) (0, -axisVector k)) := by
  rw [stationary_eq]
  exact nonempty_coulombLocalSupportingCharts k

end Problem356.CoulombSupportExistence

end

end OAI
