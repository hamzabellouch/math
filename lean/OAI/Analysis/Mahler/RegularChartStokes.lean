import OAI.Analysis.Mahler.ChartExtension
import OAI.Analysis.Mahler.RegularStokesAssembly

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

 theorem setIntegral_extDeriv_congr_support {n : ℕ} {s t : Set (Fin (n+1) → ℝ)}
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (he : ∀ x ∈ tsupport ω, x ∈ s ↔ x ∈ t) :
    (∫ x in s, extDeriv ω x (coordinateBasis (n+1))) =
      ∫ x in t, extDeriv ω x (coordinateBasis (n+1)) := by
  rw [← integral_indicator hs, ← integral_indicator ht]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport ω
  · by_cases hxs : x ∈ s
    · simp [hxs, (he x hx).mp hxs]
    · have hxt : x ∉ t := fun h => hxs ((he x hx).mpr h)
      simp [hxs, hxt]
  · have hz : extDeriv ω x (coordinateBasis (n+1)) = 0 := by
      rw [extDeriv_zero_off_tsupport ω hx]
      simp
    simp [Set.indicator, hz]

 lemma chart_image_target_inter {d : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ)) (H : Set (Fin d → ℝ)) :
    e.symm '' (e.target ∩ H) = e.source ∩ e ⁻¹' H := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyt, hyH⟩, rfl⟩
    refine ⟨e.map_target hyt, ?_⟩
    change e (e.symm y) ∈ H
    rw [e.right_inv hyt]
    exact hyH
  · rintro ⟨hxs, hxH⟩
    exact ⟨e x, ⟨e.map_source hxs, hxH⟩, e.left_inv hxs⟩

/-- Actual oriented boundary-chart integral in the level coordinates. -/
def chartBoundaryFlux {n : ℕ}
    (e : OpenPartialHomeomorph (Fin (n+1) → ℝ) (Fin (n+1) → ℝ))
    (k : Fin (n+1)) (R : ℝ)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ) : ℝ :=
  (-1 : ℝ)^k.val * ∫ y : Fin n → ℝ,
    extendedChartForm e ω (k.insertNth R y) (k.removeNth (coordinateBasis (n+1)))

/-- Stokes for a localized form in a genuine boundary chart. All pullback
regularity, zero extension, Jacobian and outward signs are derived. -/
theorem integral_extDeriv_chart {n : ℕ} {D : Set (Fin (n+1) → ℝ)}
    (e : OpenPartialHomeomorph (Fin (n+1) → ℝ) (Fin (n+1) → ℝ))
    (k : Fin (n+1)) (R : ℝ)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hD : MeasurableSet D) (he : ContDiffOn ℝ 2 e e.source)
    (hi : ContDiffOn ℝ 2 e.symm e.target) (hω : ContDiff ℝ 1 ω)
    (hc : HasCompactSupport ω) (hs : tsupport ω ⊆ e.source)
    (hflat : ∀ x ∈ tsupport ω, x ∈ D ↔ e x k < R) :
    (∫ x in D, extDeriv ω x (coordinateBasis (n+1))) = chartBoundaryFlux e k R ω := by
  let S := e.target ∩ lowerHalfspace k R
  let T := e.symm '' S
  let β := extendedChartForm e ω
  have hHo : IsOpen (lowerHalfspace k R) := isOpen_lt (continuous_apply k) continuous_const
  have hSo : IsOpen S := e.open_target.inter hHo
  have hTo : IsOpen T := by
    rw [show T = e.source ∩ e ⁻¹' lowerHalfspace k R from chart_image_target_inter e _]
    exact e.continuousOn.isOpen_inter_preimage e.open_source hHo
  have hβs : tsupport β ⊆ e.target := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := tsupport_extendedChartForm e ω hc hs hy
    exact e.map_source (hs hx)
  have hdet (y) (hy : y ∈ e.target) := chart_inverse_det_ne_zero e
    (fun x hx => (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp))
    (fun x hx => (hi.contDiffAt (e.open_target.mem_nhds hx)).differentiableAt (by simp)) hy
  calc
    _ = ∫ x in T, extDeriv ω x (coordinateBasis (n+1)) := by
      apply setIntegral_extDeriv_congr_support ω hD hTo.measurableSet
      intro x hx
      rw [show T = e.source ∩ e ⁻¹' lowerHalfspace k R from chart_image_target_inter e _]
      simpa only [mem_inter_iff, mem_preimage, lowerHalfspace, mem_ofPred_eq, hs hx, true_and]
        using hflat x hx
    _ = ∫ y in S, jacobianOrientation (fderiv ℝ e.symm y).det *
        extDeriv ω (e.symm y) (fun i => fderiv ℝ e.symm y (coordinateBasis (n+1) i)) :=
      integral_image_topForm e.symm (extDeriv ω) hSo.measurableSet
        (fun y hy => (hi.contDiffAt (e.open_target.mem_nhds hy.1)).differentiableAt (by simp))
        (e.symm.injOn.mono inter_subset_left)
    _ = ∫ y in S, extDeriv β y (coordinateBasis (n+1)) := by
      apply setIntegral_congr_fun hSo.measurableSet
      intro y hy
      dsimp only
      rw [show extDeriv β y = _ from extDeriv_extendedChartForm e ω hy.1
        (hi.contDiffAt (e.open_target.mem_nhds hy.1)) (hdet y hy.1)
        (hω.differentiable one_ne_zero _)]
      rfl
    _ = ∫ y in lowerHalfspace k R, extDeriv β y (coordinateBasis (n+1)) :=
      setIntegral_extDeriv_congr_support β hSo.measurableSet hHo.measurableSet
        (fun y hy => ⟨fun h => h.2, fun h => ⟨hβs hy, h⟩⟩)
    _ = _ := integral_extDeriv_lowerHalfspace k R β
      (contDiff_extendedChartForm e ω he hi hω hc hs)
      (hasCompactSupport_extendedChartForm e ω hc hs)

/-- Stokes with a fixed admissible atlas and partition. The same boundary
representation can therefore be used for two different forms. -/
theorem integral_extDeriv_regular_partition {n : ℕ} {U : Set (Fin (n+1) → ℝ)}
    {g : (Fin (n+1) → ℝ) → ℝ} {R : ℝ}
    (hU : IsOpen U) (hg : ContinuousOn g U)
    (a : RegularBoundaryAtlas (n+1) U g (frontier (regularSublevel U g R)))
    {W : Set (Fin (n+1) → ℝ)}
    (ρ : SmoothPartitionOfUnity (Option a.Index) 𝓘(ℝ, Fin (n+1) → ℝ)
      (Fin (n+1) → ℝ) (closure W))
    (hWo : IsOpen W) (hCW : closure (regularSublevel U g R) ⊆ W)
    (hρc : ∀ i, HasCompactSupport (ρ i)) (hρsub : ρ.IsSubordinate (sublevelPatchDomain a))
    (hsum : ∀ x ∈ W, ∑ i, ρ i x = 1)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiffOn ℝ 1 ω U) :
    (∫ x in regularSublevel U g R, extDeriv ω x (coordinateBasis (n+1))) =
      ∑ i : a.Index, chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R
        (fun z => ρ (some i) z • ω z) := by
  have hρU (i : Option a.Index) : tsupport (ρ i) ⊆ U := by
    apply (hρsub i).trans
    cases i with
    | none => exact inter_subset_left
    | some i => exact (a.patch i).domain_U
  have hvolume := integral_extDeriv_boundary_patches ρ ω hWo (subset_closure.trans hCW)
    (isOpen_regularSublevel hU hg).measurableSet hsum hρc
    (fun i x hx => hω.contDiffAt (hU.mem_nhds (hρU i hx))) (hρsub none)
  apply hvolume.trans
  apply Finset.sum_congr rfl
  intro i _
  have hsi : tsupport (fun z => ρ (some i) z • ω z) ⊆ (a.patch i).domain :=
    (tsupport_smul_subset_left _ _).trans (hρsub (some i))
  exact integral_extDeriv_chart (a.patch i).chart (a.patch i).coordinate R _
    (isOpen_regularSublevel hU hg).measurableSet
    (a.patch i).smooth_chart (a.patch i).smooth_inverse
    (contDiff_localized_form ρ ω (some i) (fun x hx => hω.contDiffAt
      (hU.mem_nhds (hρU (some i) hx))))
    (hasCompactSupport_localized_form (fun i x => ρ i x) ω (some i) (hρc (some i)))
    (hsi.trans (a.patch i).domain_source)
    (fun x hx => (a.patch i).sublevel_iff (hsi hx))

/-- General regular-sublevel Stokes for actual C1 differential forms.
Compactness supplies the finite charts and smooth cutoffs, whose oriented
boundary integrals are assembled here. -/
theorem exists_regular_sublevel_stokes {n : ℕ} {U : Set (Fin (n+1) → ℝ)}
    {g : (Fin (n+1) → ℝ) → ℝ} {R : ℝ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (hc : IsCompact (closure (regularSublevel U g R)))
    (hcl : closure (regularSublevel U g R) ⊆ U)
    (hreg : ∀ x ∈ U, g x = R → fderiv ℝ g x ≠ 0)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiffOn ℝ 1 ω U) :
    ∃ (a : RegularBoundaryAtlas (n+1) U g (frontier (regularSublevel U g R)))
      (W : Set (Fin (n+1) → ℝ))
      (ρ : SmoothPartitionOfUnity (Option a.Index) 𝓘(ℝ, Fin (n+1) → ℝ)
        (Fin (n+1) → ℝ) (closure W)),
      IsOpen W ∧ closure (regularSublevel U g R) ⊆ W ∧
      (∀ i, HasCompactSupport (ρ i)) ∧
      (∀ i, tsupport (ρ (some i)) ⊆ (a.patch i).domain) ∧
      (∀ x ∈ W, ∑ i, ρ i x = 1) ∧
      (∫ x in regularSublevel U g R, extDeriv ω x (coordinateBasis (n+1))) =
        ∑ i : a.Index, chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R
          (fun z => ρ (some i) z • ω z) := by
  obtain ⟨a⟩ := exists_sublevelBoundaryAtlas hU hg hc hcl hreg
  obtain ⟨W, ρ, hWo, hCW, _, hρsub, hρc, hsum⟩ :=
    exists_sublevel_partition hU hg.continuousOn hc a
  exact ⟨a, W, ρ, hWo, hCW, hρc, (fun i => hρsub (some i)), hsum,
    integral_extDeriv_regular_partition hU hg.continuousOn a ρ hWo hCW hρc hρsub hsum ω hω⟩

end MahlerStokes

end

end OAI
