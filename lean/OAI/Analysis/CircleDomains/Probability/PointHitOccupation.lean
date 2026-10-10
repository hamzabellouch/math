import OAI.Analysis.CircleDomains.Selection.PhysicalExitPenalty
import OAI.Analysis.CircleDomains.Probability.CodeLawMixtures

namespace OAI

/-! A visit to a fixed interior point forces physical occupation of each
surrounding region before the path can end outside it. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

omit [BorelSpace C(PathTime, X)] in
theorem point_hit_occupation_lower_bound
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (π : Y → X) (hπ : Continuous π)
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (p : Y) (hp : p ∈ d.physicalDomain)
    (O : Set X) (hO : IsOpen O) (hOU : closure O ⊆ d.quotientDomain) (hpO : π p ∈ O)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) (hδfin : δ ≠ ∞)
    (hsep : ∀ b ∉ π ⁻¹' O, δ ≤ edist p b)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint)
    (hend : γ.val ⊤ ∉ O) (hhit : π p ∈ range γ.val) :
    δ ≤ dyadicPhysicalOccupation d.domainEquiv d.basePoint γ (π ⁻¹' O) := by
  obtain ⟨t, ht⟩ := hhit
  have htt : t < ⊤ := lt_top_iff_ne_top.mpr (by
    intro h
    subst t
    exact hend (ht ▸ hpO))
  let ρ := affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ htt
  have hstart : ρ.val ⊥ = π p := by
    change γ.val (affinePathTime t ⊤ ⊥) = π p
    rwa [affinePathTime_zero]
  have hend' : ρ.val ⊤ ∉ O := by
    change γ.val (affinePathTime t ⊤ ⊤) ∉ O
    rwa [affinePathTime_one]
  have hpre : (d.domainEquiv.symm
      ⟨ρ.val ⊥, hOU (subset_closure (hstart ▸ hpO))⟩).val = p := by
    have hs : (⟨ρ.val ⊥, hOU (subset_closure (hstart ▸ hpO))⟩ : d.quotientDomain) =
        d.domainEquiv ⟨p, hp⟩ := Subtype.ext (hstart.trans (he ⟨p, hp⟩).symm)
    rw [hs, d.domainEquiv.symm_apply_apply]
  let w : Y → ℝ≥0∞ := (π ⁻¹' O).indicator (fun _ => δ⁻¹)
  have hw : Measurable w := measurable_const.indicator (hO.preimage hπ).measurableSet
  have hpay := first_exit_indicator_cost_lower_bound d hU π hπ he O hO hOU {p} hδ hδfin
    (by intro a ha b hb; simpa only [mem_singleton_iff.mp ha] using hsep b hb)
    ρ (hstart ▸ hpO) hend' (by exact hpre) (fun _ => 0)
  have hfull : 1 ≤ physicalTollCost d w (fun _ => 0) γ :=
    hpay.trans (physicalTollCost_affine_le d hU γ htt w hw (fun _ => 0))
  have hmass : 1 ≤ δ⁻¹ *
      dyadicPhysicalOccupation d.domainEquiv d.basePoint γ (π ⁻¹' O) := by
    simpa only [physicalTollCost, boundaryToll, tsum_zero, add_zero, w,
      lintegral_indicator_const (hO.preimage hπ).measurableSet] using hfull
  calc
    δ = δ * 1 := (mul_one _).symm
    _ ≤ δ * (δ⁻¹ * dyadicPhysicalOccupation d.domainEquiv d.basePoint γ (π ⁻¹' O)) :=
      mul_le_mul' le_rfl hmass
    _ = _ := by rw [← mul_assoc, ENNReal.mul_inv_cancel hδ hδfin, one_mul]

variable [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem mean_occupation_ge_point_hit
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (π : Y → X) (hπ : Continuous π)
    (he : ∀ y : d.physicalDomain, (d.domainEquiv y).val = π y.val)
    (p : Y) (hp : p ∈ d.physicalDomain)
    (O : Set X) (hO : IsOpen O) (hOU : closure O ⊆ d.quotientDomain) (hpO : π p ∈ O)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) (hδfin : δ ≠ ∞)
    (hsep : ∀ b ∉ π ⁻¹' O, δ ≤ edist p b)
    (P : ProbabilityMeasure (BasePathCode d)) (hend : d.target ∉ O) :
    δ * pathHitProbability (codePathLaw d P) (π p) ≤ meanCodeOccupation d P (π ⁻¹' O) := by
  let H : Set (BasePathCode d) := {Γ | π p ∈ range (codePath d Γ)}
  have hH : MeasurableSet H :=
    (measurable_codePath d) (isClosed_paths_hitting (π p)).measurableSet
  have heq : pathHitProbability (codePathLaw d P) (π p) = (P : Measure _) H :=
    pathHitProbability_codePathLaw d P (π p)
  rw [heq, ← lintegral_indicator_const hH δ]
  rw [meanCodeOccupation, Measure.bind_apply (hO.preimage hπ).measurableSet
    (measurable_baseCodeOccupation d hU).aemeasurable]
  apply lintegral_mono
  intro Γ
  by_cases hΓ : Γ ∈ H
  · rw [indicator_of_mem hΓ]
    apply point_hit_occupation_lower_bound d hU π hπ he p hp O hO hOU hpO hδ hδfin hsep
      (baseCodePhysicalPath d Γ)
    · change Γ.val.1 ⊤ ∉ O
      rw [Γ.property.2.1.2.1]
      exact hend
    · exact hΓ
  · simp only [indicator_of_notMem hΓ]
    exact bot_le

end CircleDomainRigidity

end

end OAI
