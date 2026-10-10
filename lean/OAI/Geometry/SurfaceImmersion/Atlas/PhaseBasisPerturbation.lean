import OAI.Geometry.Immersion.ClosedSurface.PhaseStock

namespace OAI

/-! Actual coefficient forms for nearby phase covectors. The inverse
operator constructs the new decomposition and preserves compact positive
cone margins. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def perturbedPhaseOperator (P : PhaseBasis) (xi : Fin 3 → Base) :
    PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor :=
  ∑ i, (P.Q i).smulRight (covectorSquare (xi i))

lemma perturbedPhaseOperator_apply (P : PhaseBasis) (xi : Fin 3 → Base)
    (H : PhaseMean.Tensor) :
    perturbedPhaseOperator P xi H = ∑ i, P.Q i H • covectorSquare (xi i) := by
  simp only [perturbedPhaseOperator, sum_apply, ContinuousLinearMap.smulRight_apply]

lemma perturbedPhaseOperator_self (P : PhaseBasis) :
    perturbedPhaseOperator P P.ξ = ContinuousLinearMap.id ℝ PhaseMean.Tensor := by
  apply ContinuousLinearMap.ext
  intro H
  exact (perturbedPhaseOperator_apply P P.ξ H).trans (P.decomposition H)

lemma perturbedPhaseOperator_smooth (P : PhaseBasis) :
    ContDiff ℝ ∞ (perturbedPhaseOperator P) := by
  apply ContDiff.sum
  intro i _
  apply contDiff_const.smulRight
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> simp only [covectorSquare, Matrix.cons_val_zero',
    Matrix.cons_val_succ'] <;> fun_prop

def perturbedPhaseCoefficient (P : PhaseBasis) (xi : Fin 3 → Base) (i : Fin 3) :
    PhaseMean.Tensor →L[ℝ] ℝ :=
  (P.Q i).comp (perturbedPhaseOperator P xi).inverse

lemma perturbedPhaseCoefficient_self (P : PhaseBasis) (i : Fin 3) :
    perturbedPhaseCoefficient P P.ξ i = P.Q i := by
  simp only [perturbedPhaseCoefficient, perturbedPhaseOperator_self,
    ContinuousLinearMap.inverse_id, ContinuousLinearMap.comp_id]

lemma perturbedPhase_decomposition (P : PhaseBasis) {xi : Fin 3 → Base}
    (hxi : (perturbedPhaseOperator P xi).IsInvertible) (H : PhaseMean.Tensor) :
    ∑ i, perturbedPhaseCoefficient P xi i H • covectorSquare (xi i) = H := by
  calc
    _ = perturbedPhaseOperator P xi ((perturbedPhaseOperator P xi).inverse H) :=
      (perturbedPhaseOperator_apply P xi _).symm
    _ = H := hxi.self_apply_inverse H

lemma perturbedPhaseCoefficient_smoothAt (P : PhaseBasis) {xi : Fin 3 → Base}
    (hxi : (perturbedPhaseOperator P xi).IsInvertible) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun z => perturbedPhaseCoefficient P z i) xi :=
  contDiffAt_const.clm_comp
    (hxi.contDiffAt_map_inverse.comp xi (perturbedPhaseOperator_smooth P).contDiffAt)

def positivePhaseParameters (P : PhaseBasis) : Set ((Fin 3 → Base) × PhaseMean.Tensor) :=
  {z | (perturbedPhaseOperator P z.1).IsInvertible ∧
    (∀ i, z.1 i ≠ 0) ∧ ∀ i, 0 < perturbedPhaseCoefficient P z.1 i z.2}

lemma positivePhaseParameters_open (P : PhaseBasis) : IsOpen (positivePhaseParameters P) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hA : ∀ᶠ w in 𝓝 z, (perturbedPhaseOperator P w.1).IsInvertible :=
    ((perturbedPhaseOperator_smooth P).continuous.comp continuous_fst).continuousAt.eventually
      hz.1.eventually_nhds
  have hxi : ∀ᶠ w in 𝓝 z, ∀ i, w.1 i ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact ((continuous_apply i).comp continuous_fst).continuousAt.eventually_ne (hz.2.1 i)
  have hQ : ∀ᶠ w in 𝓝 z, ∀ i, 0 < perturbedPhaseCoefficient P w.1 i w.2 := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (fun w : (Fin 3 → Base) × PhaseMean.Tensor =>
        perturbedPhaseCoefficient P w.1 i w.2) z :=
      (((perturbedPhaseCoefficient_smoothAt P hz.1 i).comp z contDiffAt_fst).clm_apply
        contDiffAt_snd).continuousAt
    exact hc.eventually (lt_mem_nhds (hz.2.2 i))
  exact hA.and (hxi.and hQ)

/-- Nearby covectors admit actual smooth inverse coefficient forms, positive
uniformly over the fixed compact collection of target tensor values. -/
theorem compact_positive_phase_perturbation (P : PhaseBasis) {K : Set PhaseMean.Tensor}
    (hK : IsCompact K) (hpos : ∀ H ∈ K, ∀ i, 0 < P.Q i H) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ xi : Fin 3 → Base, ‖xi-P.ξ‖ < eps →
      (perturbedPhaseOperator P xi).IsInvertible ∧ (∀ i, xi i ≠ 0) ∧
        ∀ H ∈ K, ∀ i, 0 < perturbedPhaseCoefficient P xi i H := by
  have hA0 : (perturbedPhaseOperator P P.ξ).IsInvertible := by
    rw [perturbedPhaseOperator_self]
    exact ⟨ContinuousLinearEquiv.refl ℝ PhaseMean.Tensor,rfl⟩
  have hbase : ∀ᶠ xi in 𝓝 P.ξ,
      (perturbedPhaseOperator P xi).IsInvertible ∧ ∀ i, xi i ≠ 0 := by
    apply Filter.Eventually.and
    · exact (perturbedPhaseOperator_smooth P).continuous.continuousAt.eventually hA0.eventually_nhds
    · rw [Filter.eventually_all]
      intro i
      exact (continuous_apply i).continuousAt.eventually_ne (P.nonzero i)
  have hpositive : ∀ᶠ xi in 𝓝 P.ξ, ∀ H ∈ K, ∀ i,
      0 < perturbedPhaseCoefficient P xi i H := by
    apply hK.eventually_forall_of_forall_eventually
    intro H hH
    have hmem : (P.ξ,H) ∈ positivePhaseParameters P := by
      refine ⟨hA0,P.nonzero,?_⟩
      intro i
      simpa only [perturbedPhaseCoefficient_self] using hpos H hH i
    exact ((positivePhaseParameters_open P).eventually_mem hmem).mono
      (fun z hz => hz.2.2)
  obtain ⟨eps,heps,hsmall⟩ := Metric.eventually_nhds_iff.mp (hbase.and hpositive)
  refine ⟨eps,heps,fun xi hnear => ?_⟩
  have hxi := hsmall (y := xi) (by simpa only [dist_eq_norm] using hnear)
  exact ⟨hxi.1.1,hxi.1.2,hxi.2⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
