import OAI.Geometry.RCD.Transport.PairedEntropyDeficit
import OAI.Geometry.RCD.Transport.ResolvedBranchSelection
import OAI.Geometry.RCD.Transport.BranchMeshObstruction

namespace OAI

/-! # No positive resolved branch window in a compressed optimal RCD plan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X] {K : ℝ} {n : ℕ}
  [IsLocallyFiniteMeasure (hausdorff n X)] (hX : NoncollapsedRCD K n X)
include hX
attribute [local instance] pathBorel pathBorelSpace

theorem no_resolved_branch_window (hn : 2 ≤ n) (p : X) {R : ℝ} (hR : 0 ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0} (hC : 0 < C)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ ENNReal.ofReal C • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x p ≤ R)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x p ≤ R)
    (σ : Measure (C(Time,X)×C(Time,X))) [IsFiniteMeasure σ] (hσ : σ univ ≠ 0)
    (hl : σ.map Prod.fst ≤ π) (hr : σ.map Prod.snd ≤ π)
    (T S q : Time) (hT : 0 < T) (hTS : T < S) (hS : S < 1) (hSq : S ≤ q)
    (h0 : ∀ᵐ z ∂σ, z.1 0=z.2 0)
    (hroot : ∀ᵐ z ∂σ, (T:ℝ) ≤ (lastPathAgreement q z:ℝ) ∧
      (lastPathAgreement q z:ℝ) < (S:ℝ)) : False := by
  let c := σ.real univ/(5*((S:ℝ)-(T:ℝ)))
  have hmass : 0 < σ.real univ := ENNReal.toReal_pos hσ (measure_ne_top _ _)
  have hST : 0 < (S:ℝ)-(T:ℝ) := sub_pos.mpr hTS
  have hc0 : 0 < c := div_pos hmass (mul_pos (by norm_num) hST)
  have hA : 0 ≤ (|K|/2)*(2*R)^2 := mul_nonneg (div_nonneg (abs_nonneg K) (by norm_num)) (sq_nonneg _)
  obtain ⟨N,hN,hob⟩ := exists_branch_mesh_obstruction
    (show (0:ℝ) < T from hT) (show (S:ℝ) < 1 from hS)
    (show (T:ℝ) < S from hTS) hc0 (show (0:ℝ) < C from hC) hA
    (B := -Real.log ((hausdorff n X).real (closedBall p (3*R))))
  obtain ⟨s,t,κ,hTs,hst,htS,hstep,hκ,hκmass,hcommon,hsing⟩ :=
    select_resolved_branches σ hσ T S q hTS.le hSq h0 hroot hN
  let : IsFiniteMeasure κ := isFiniteMeasure_of_le σ hκ
  have hκpos : 0 < κ.real univ := lt_trans (div_pos hmass (by positivity)) hκmass
  have hκ0 : κ univ ≠ 0 := by
    intro he
    have hz : κ.real univ=0 := by simp only [Measure.real,he,ENNReal.toReal_zero]
    linarith
  have hst' : s < t := by
    change (s:ℝ) < (t:ℝ)
    have hstep0 : 0 < (t:ℝ)-(s:ℝ) := by rw [hstep]; exact div_pos hST (Nat.cast_pos.mpr hN)
    linarith
  have hle0 : κ.map Prod.fst ≤ π := (Measure.map_mono hκ measurable_fst).trans hl
  have hle1 : κ.map Prod.snd ≤ π := (Measure.map_mono hκ measurable_snd).trans hr
  have hdef := hX.paired_entropy_deficit hn p hR π hg hp hC hc hs₀ hs₁ κ hκ0 hle0 hle1 q s t
    (hT.trans_le hTs) hst' (htS.trans_lt hS) hcommon hsing
  have hcm : c*(((S:ℝ)-(T:ℝ))/(N:ℝ)) ≤ κ.real univ := by
    have he : c*(((S:ℝ)-(T:ℝ))/(N:ℝ))=σ.real univ/(5*(N:ℝ)) := by
      dsimp only [c]
      field_simp
    rw [he]
    exact hκmass.le
  apply hob (s:ℝ) (κ.real univ) hTs (hst.trans htS) hcm
  rw [hstep] at hdef
  simpa only [sub_neg_eq_add] using hdef

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
