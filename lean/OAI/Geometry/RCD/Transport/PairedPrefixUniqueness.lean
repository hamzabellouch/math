import OAI.Geometry.RCD.Transport.NoResolvedBranchWindow

namespace OAI

/-! # A common positive prefix determines a compressed optimal path -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem paired_common_prefix_point (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (σ : Measure (C(Time,X)×C(Time,X))) [IsFiniteMeasure σ]
    (hl : σ.map Prod.fst ≤ π) (hr : σ.map Prod.snd ≤ π)
    (T q : Time) (hT : 0 < T) (hq : q < 1)
    (hpast : ∀ᵐ z ∂σ, z ∈ pathAgreement (T:ℝ)) :
    ∀ᵐ z ∂σ, z.1 q=z.2 q := by
  by_cases hqT : q ≤ T
  · exact hpast.mono fun z hz => hz q hqT
  have hTq : T < q := lt_of_not_ge hqT
  by_contra hbad
  let F : Set (C(Time,X)×C(Time,X)) := {z | z.1 q ≠ z.2 q}
  have hF : MeasurableSet F := (measurableSet_eq_fun
    ((measurable_path_eval q).comp measurable_fst)
    ((measurable_path_eval q).comp measurable_snd)).compl
  have hFpos : σ F ≠ 0 := by
    simpa only [ae_iff,F] using hbad
  let ρ := σ.restrict F
  have hρ0 : ρ univ ≠ 0 := by simpa only [ρ,Measure.restrict_apply_univ] using hFpos
  have hρpast : ∀ᵐ z ∂ρ, z ∈ pathAgreement (T:ℝ) :=
    hpast.filter_mono Measure.restrict_le_self.absolutelyContinuous.ae_le
  have hρdiff : ∀ᵐ z ∂ρ, z.1 q ≠ z.2 q := ae_restrict_mem hF
  obtain ⟨S,hTS,hSq,hA,hA0,_⟩ := exists_resolved_branch_window ρ hρ0 T q hTq.le hρpast hρdiff
  let A : Set (C(Time,X)×C(Time,X)) := {z | (lastPathAgreement q z:ℝ) < (S:ℝ)}
  let κ := ρ.restrict A
  have hκσ : κ ≤ σ := Measure.restrict_le_self.trans Measure.restrict_le_self
  have hκpast : ∀ᵐ z ∂κ, z ∈ pathAgreement (T:ℝ) :=
    hpast.filter_mono hκσ.absolutelyContinuous.ae_le
  have hκroot : ∀ᵐ z ∂κ, (T:ℝ) ≤ (lastPathAgreement q z:ℝ) ∧
      (lastPathAgreement q z:ℝ) < (S:ℝ) := by
    filter_upwards [hκpast,ae_restrict_mem hA] with z hz ha
    exact ⟨(lastPathAgreement_isGreatest q z).2 (Or.inr ⟨hTq.le,hz T le_rfl⟩),ha⟩
  exact hX.no_resolved_branch_window hn p hR π hg hp hC hc hs₀ hs₁ κ hA0
    ((Measure.map_mono hκσ measurable_fst).trans hl)
    ((Measure.map_mono hκσ measurable_snd).trans hr) T S q hT hTS (hSq.trans hq) hSq.le
    (hκpast.mono fun z hz => hz 0 T.property.1) hκroot

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
