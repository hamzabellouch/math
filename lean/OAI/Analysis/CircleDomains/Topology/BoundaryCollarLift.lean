import OAI.Analysis.CircleDomains.Topology.LogarithmicDiskLift
import OAI.Analysis.CircleDomains.Selection.LiftedMeanBands
import OAI.Analysis.CircleDomains.Selection.GeometricIndexPeriod
import OAI.Analysis.CircleDomains.Transfer.PeriodicFilling
import Mathlib.Topology.UniformSpace.HeineCantor

namespace OAI

/-! Normalize one logarithmic lift of a punctured-disk collar by its
boundary parametrization. Joint continuity then gives uniform convergence
to the boundary lift, not merely pointwise convergence of angles. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_boundary_normalized_logarithmic_lift
    {δ : ℝ} (hδ : 0 < δ) (w : ℝ × ℝ → ℂ)
    (hw : ContinuousOn w (Ioo (-δ) δ ×ˢ univ))
    (hw0 : ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ), w p ≠ 0)
    (hw1 : ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ), ‖w p‖ ≤ 1)
    (q : ℝ → ℝ) (hq : Continuous q) (hq0 : q 0 = 0)
    (hboundary : ∀ t, w (0, t) = diskRayProjection (q t : ℂ)) :
    ∃ L : ℝ × ℝ → ClosedUpperHalfPlane,
      ContinuousOn L (Ioo (-δ) δ ×ˢ univ) ∧
      (∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ), diskRayProjection (L p).val = w p) ∧
      (∀ t, (L (0, t)).val = (q t : ℂ)) := by
  let D : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ univ
  have hzero : (0, 0) ∈ D := ⟨⟨by linarith, hδ⟩, mem_univ _⟩
  have hD : IsOpen D := isOpen_Ioo.prod isOpen_univ
  let : ContractibleSpace D :=
    ((convex_Ioo (-δ) δ).prod convex_univ).contractibleSpace ⟨_, hzero⟩
  let : LocallyPathConnectedSpace D := hD.locallyPathConnectedSpace
  have ha : ContinuousOn (normalizedArgument ∘ w) D := fun p hp =>
    (continuousAt_normalizedArgument (hw0 p hp)).comp_continuousWithinAt (hw p hp)
  obtain ⟨u, hu, hu0, hup⟩ := exists_continuous_circle_lift (normalizedArgument ∘ w) ha hzero 0 (by
    change (0 : UnitAddCircle) = normalizedArgument (w (0, 0))
    rw [hboundary, diskRayProjection_argument]
    simp only [Complex.ofReal_re, hq0, AddCircle.coe_zero])
  have huB : Continuous (fun t : ℝ => u (0, t)) :=
    hu.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨hzero.1, mem_univ _⟩)
  have hdiff := isLocallyConstant_real_lift_difference huB hq (fun t => by
    rw [hup (0, t) ⟨hzero.1, mem_univ _⟩]
    change normalizedArgument (w (0, t)) = (q t : UnitAddCircle)
    rw [hboundary, diskRayProjection_argument, Complex.ofReal_re])
  have huBq (t : ℝ) : u (0, t) = q t := by
    have he := hdiff.apply_eq_of_preconnectedSpace t 0
    rw [hu0, hq0] at he
    linarith
  let Ψ : ℝ × ℝ → ℂ := fun p => (u p : ℂ) + ((-Real.log ‖w p‖ : ℝ) : ℂ) * Complex.I
  have him (p) : (Ψ p).im = -Real.log ‖w p‖ := by simp [Ψ]
  have hre (p) : (Ψ p).re = u p := by simp [Ψ]
  have hc : ContinuousOn Ψ D :=
    (Complex.continuous_ofReal.comp_continuousOn hu).add
      ((Complex.continuous_ofReal.comp_continuousOn
        ((hw.norm.log (fun p hp => norm_ne_zero_iff.mpr (hw0 p hp))).neg)).mul_const _)
  have hn (p) (hp : p ∈ D) : 0 ≤ (Ψ p).im := by
    rw [him]
    exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (hw1 p hp))
  let L : ℝ × ℝ → ClosedUpperHalfPlane := fun p => upperHalfPlaneClamp (Ψ p)
  have hLv (p) (hp : p ∈ D) : (L p).val = Ψ p := upperHalfPlaneClamp_val (hn p hp)
  refine ⟨L, continuous_upperHalfPlaneClamp.comp_continuousOn hc, ?_, ?_⟩
  · intro p hp
    rw [hLv p hp]
    apply Complex.ext_norm_arg
    · rw [diskRayProjection_norm, him, neg_neg,
        Real.exp_log (norm_pos_iff.mpr (hw0 p hp))]
    · apply Complex.arg_coe_angle_eq_iff.mp
      apply (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective
      change normalizedArgument (diskRayProjection (Ψ p)) = normalizedArgument (w p)
      rw [diskRayProjection_argument, hre]
      exact hup p hp
  · intro t
    rw [hLv (0, t) ⟨hzero.1, mem_univ _⟩]
    apply Complex.ext
    · simpa only [Complex.ofReal_re, hre] using huBq t
    · rw [him, hboundary, diskRayProjection_norm]
      simp

 theorem uniform_collar_lift_approach
    {δ : ℝ} (hδ : 0 < δ) (L : ℝ × ℝ → ClosedUpperHalfPlane)
    (hL : ContinuousOn L (Ioo (-δ) δ ×ˢ univ))
    (q : ℝ → ℝ) (hboundary : ∀ t, (L (0, t)).val = (q t : ℂ)) :
    ∀ ε > 0, ∃ η > 0, η < δ ∧ ∀ ρ ∈ Ioo (-η) η,
      ∀ t ∈ Icc (0 : ℝ) 1, dist (L (ρ, t)).val (q t : ℂ) < ε := by
  let K : Set (ℝ × ℝ) := Icc (-δ / 2) (δ / 2) ×ˢ Icc 0 1
  have hKD : K ⊆ Ioo (-δ) δ ×ˢ (univ : Set ℝ) := by
    rintro ⟨ρ, t⟩ ⟨hρ, _⟩
    exact ⟨⟨by linarith [hρ.1], by linarith [hρ.2]⟩, mem_univ _⟩
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    ((continuous_subtype_val.comp_continuousOn hL).mono hKD)
  intro ε hε
  obtain ⟨d, hd, hdist⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  let η := min (δ / 4) (d / 2)
  have hη : 0 < η := lt_min (by linarith) (half_pos hd)
  refine ⟨η, hη, (min_le_left _ _).trans_lt (by linarith), ?_⟩
  intro ρ hρ t ht
  have hr : |ρ| < η := abs_lt.mpr hρ
  have hρK : (ρ, t) ∈ K := by
    refine ⟨⟨?_, ?_⟩, ht⟩ <;> dsimp only [η] at hr <;>
      have hh := min_le_left (δ / 4) (d / 2) <;> linarith [(abs_lt.mp hr).1, (abs_lt.mp hr).2]
  have h0K : (0, t) ∈ K := ⟨⟨by linarith, by linarith⟩, ht⟩
  have hp : dist (ρ, t) (0, t) < d := by
    rw [Prod.dist_eq, dist_self, max_eq_left (show (0 : ℝ) ≤ dist ρ 0 from dist_nonneg), Real.dist_eq, sub_zero]
    exact hr.trans_le ((show η ≤ d / 2 from min_le_right _ _).trans (by linarith))
  simpa only [Function.comp_apply, hboundary] using hdist (ρ, t) hρK (0, t) h0K hp

 theorem boundary_normalized_collar_lift_period
    {δ : ℝ} (hδ : 0 < δ) (w : ℝ × ℝ → ℂ)
    (L : ℝ × ℝ → ClosedUpperHalfPlane)
    (hL : ContinuousOn L (Ioo (-δ) δ ×ˢ univ))
    (hproj : ∀ p ∈ Ioo (-δ) δ ×ˢ (univ : Set ℝ), diskRayProjection (L p).val = w p)
    (hloop : ∀ ρ ∈ Ioo (-δ) δ, w (ρ, 1) = w (ρ, 0))
    (q : ℝ → ℝ) (hq : q 1 = q 0 + 1)
    (hboundary : ∀ t, (L (0, t)).val = (q t : ℂ)) :
    ∀ ρ ∈ Ioo (-δ) δ, L (ρ, 1) = (L (ρ, 0)).translate 1 := by
  let A := Ioo (-δ) δ
  let : PreconnectedSpace A := Subtype.preconnectedSpace (convex_Ioo (-δ) δ).isPreconnected
  let u₁ : A → ℝ := fun ρ => (L (ρ, 1)).val.re
  let u₀ : A → ℝ := fun ρ => (L (ρ, 0)).val.re
  have hu₁ : Continuous u₁ := Complex.continuous_re.comp
    (continuous_subtype_val.comp (hL.comp_continuous
      (continuous_subtype_val.prodMk continuous_const) (fun ρ => ⟨ρ.property, mem_univ _⟩)))
  have hu₀ : Continuous u₀ := Complex.continuous_re.comp
    (continuous_subtype_val.comp (hL.comp_continuous
      (continuous_subtype_val.prodMk continuous_const) (fun ρ => ⟨ρ.property, mem_univ _⟩)))
  have hc := isLocallyConstant_real_lift_difference hu₁ hu₀ (fun ρ => by
    change ((L (ρ, 1)).val.re : UnitAddCircle) = ((L (ρ, 0)).val.re : UnitAddCircle)
    rw [← diskRayProjection_argument, ← diskRayProjection_argument,
      hproj (ρ, 1) ⟨ρ.property, mem_univ _⟩,
      hproj (ρ, 0) ⟨ρ.property, mem_univ _⟩, hloop ρ ρ.property])
  have hz : (0 : ℝ) ∈ A := ⟨by linarith, hδ⟩
  intro ρ hρ
  have hreal := hc.apply_eq_of_preconnectedSpace ⟨ρ, hρ⟩ ⟨0, hz⟩
  change (L (ρ, 1)).val.re - (L (ρ, 0)).val.re =
    (L (0, 1)).val.re - (L (0, 0)).val.re at hreal
  rw [hboundary, hboundary, Complex.ofReal_re, Complex.ofReal_re, hq] at hreal
  have hp : diskRayProjection (L (ρ, 1)).val = diskRayProjection (L (ρ, 0)).val := by
    rw [hproj (ρ, 1) ⟨hρ, mem_univ _⟩, hproj (ρ, 0) ⟨hρ, mem_univ _⟩, hloop ρ hρ]
  have him := congrArg norm hp
  rw [diskRayProjection_norm, diskRayProjection_norm] at him
  have him' := Real.exp_injective him
  apply Subtype.ext
  apply Complex.ext
  · change (L (ρ, 1)).val.re = ((L (ρ, 0)).val + (1 : ℤ)).re
    simp only [Int.cast_one, Complex.add_re, Complex.one_re]
    linarith
  · change (L (ρ, 1)).val.im = ((L (ρ, 0)).val + (1 : ℤ)).im
    simp only [Int.cast_one, Complex.add_im, Complex.one_im, add_zero]
    linarith

end CircleDomainRigidity

end

end OAI
