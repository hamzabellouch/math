import OAI.Analysis.CircleDomains.Topology.RegularJordanCollar
import OAI.Analysis.CircleDomains.Topology.PerturbedCurveTangent

namespace OAI

/-! Explicit assembly of an inward collar from a small smooth ambient
field. Compact retention follows from the actual inverse displacement bound. -/
open Set Function Filter Metric
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

lemma exists_inward_collar_of_field
    (H : ℂ ≃ₜ ℂ) {γ : ℝ → ℂ} (hγ : PositiveJordanParametrization H γ)
    (V : ℂ → ℂ) (hs : ContDiff ℝ ∞ V) (hc : HasCompactSupport V)
    {L : ℝ≥0} (hV : LipschitzWith L V) (hL : L < 1)
    (hin : ∀ ρ ∈ Ioc (0 : ℝ) 1, ∀ z ∈ frontier (jordanInterior H),
      z+ρ • V z ∈ jordanInterior H) : Nonempty (RegularJordanInwardCollar H) := by
  let disk : ℝ → ℂ ≃ₜ ℂ := fun ρ => if hρ : ρ ∈ Icc (0 : ℝ) 1 then
    H.trans (scaledPerturbationHomeomorph V hV hL ⟨ρ,hρ⟩) else H
  let curve : ℝ → ℝ → ℂ := fun ρ t => γ t+ρ • V (γ t)
  have hdisk (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
      disk ρ = H.trans (scaledPerturbationHomeomorph V hV hL ⟨ρ,hρ⟩) := by
    simp only [disk, dite_eq_left hρ]
  have hcurve (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
      curve ρ = scaledPerturbationHomeomorph V hV hL ⟨ρ,hρ⟩ ∘ γ := rfl
  have hpar (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
      PositiveJordanParametrization (disk ρ) (curve ρ) := by
    rw [hdisk ρ hρ, hcurve ρ hρ]
    exact positiveJordanParametrization_smallPerturbation hV hL hs hγ _
  refine ⟨⟨1, zero_lt_one, curve, disk, ?_, ?_, ?_, hpar, ?_, ?_⟩⟩
  · rw [hdisk 0 (by norm_num), scaledPerturbationHomeomorph_zero]
    rfl
  · exact ((hγ.smooth.continuous.comp continuous_snd).add
      (continuous_fst.smul (hs.continuous.comp (hγ.smooth.continuous.comp continuous_snd)))).continuousOn
  · exact (perturbedCurve_tangent_continuous hs hγ.smooth).continuousOn
  · intro ρ hρ
    apply closed_jordanInterior_subset_of_frontier_subset
    rw [hdisk ρ ⟨hρ.1.le,hρ.2⟩, jordanInterior_trans,
      ← (scaledPerturbationHomeomorph V hV hL ⟨ρ, hρ.1.le,hρ.2⟩).image_frontier]
    rintro z ⟨w, hw, rfl⟩
    exact hin ρ hρ w hw
  · intro K hK hKH
    obtain ⟨d, hd, hthick⟩ := hK.exists_cthickening_subset_open (jordanInterior_isOpen H) hKH
    obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hs.continuous
    have hM0 : 0 ≤ M := (norm_nonneg (V 0)).trans (hM 0)
    let η := min 1 (d/(M+1))
    have hη : 0 < η := lt_min zero_lt_one (div_pos hd (by linarith))
    refine ⟨η, hη, min_le_left _ _, ?_⟩
    intro ρ hρ y hy
    have hρ1 : ρ ∈ Icc (0 : ℝ) 1 := ⟨hρ.1.le,hρ.2.trans (min_le_left _ _)⟩
    let T := scaledPerturbationHomeomorph V hV hL ⟨ρ,hρ1⟩
    have hdist : dist (T.symm y) y ≤ ρ*M := by
      have he : T.symm y+ρ • V (T.symm y) = y := T.apply_symm_apply y
      have hv : T.symm y-y = -(ρ • V (T.symm y)) := by
        calc
          _ = T.symm y-(T.symm y+ρ • V (T.symm y)) := congrArg (fun w => T.symm y-w) he.symm
          _ = _ := by abel
      rw [dist_eq_norm, hv, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ.1.le]
      exact mul_le_mul_of_nonneg_left (hM _) hρ.1.le
    have hpay : ρ*M ≤ d := by
      have hbound : ρ ≤ d/(M+1) := hρ.2.trans (min_le_right _ _)
      have hmul := (le_div_iff₀ (show 0 < M+1 by linarith)).mp hbound
      nlinarith [hρ.1]
    have hback : T.symm y ∈ jordanInterior H :=
      hthick (mem_cthickening_of_dist_le (T.symm y) y d K hy (hdist.trans hpay))
    rw [hdisk ρ hρ1, jordanInterior_trans]
    exact ⟨T.symm y, hback, T.apply_symm_apply y⟩

end CircleDomainRigidity

end

end OAI
