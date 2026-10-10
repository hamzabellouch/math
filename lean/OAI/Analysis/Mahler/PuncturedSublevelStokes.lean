import OAI.Analysis.Mahler.PunctureCutoff

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Manifold
namespace MahlerStokes

/-- Punctured Stokes for a fixed atlas and partition, allowing comparison
with another form on the very same oriented boundary representation. -/
theorem punctured_sublevel_stokes_of_partition {n : ℕ} {U : Set (Fin (n+1) → ℝ)}
    {g : (Fin (n+1) → ℝ) → ℝ} {R r : ℝ}
    (hU : IsOpen U) (hg : ContinuousOn g U)
    (hc : IsCompact (closure (regularSublevel U g R)))
    (hcl : closure (regularSublevel U g R) ⊆ U)
    (hr : 0 < r) (hB : coordClosedBall (n+1) r ⊆ regularSublevel U g R)
    (a : RegularBoundaryAtlas (n+1) U g (frontier (regularSublevel U g R)))
    {W : Set (Fin (n+1) → ℝ)}
    (ρ : SmoothPartitionOfUnity (Option a.Index) 𝓘(ℝ, Fin (n+1) → ℝ)
      (Fin (n+1) → ℝ) (closure W))
    (hWo : IsOpen W) (hCW : closure (regularSublevel U g R) ⊆ W)
    (hρc : ∀ i, HasCompactSupport (ρ i)) (hρsub : ρ.IsSubordinate (sublevelPatchDomain a))
    (hsum : ∀ x ∈ W, ∑ i, ρ i x = 1)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiffOn ℝ 1 ω (U \ {0})) :
    (∑ i : a.Index, chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R
      (fun z => ρ (some i) z • ω z)) - sphereFlux r ω =
      ∫ x in regularSublevel U g R \ coordClosedBall (n+1) r,
        extDeriv ω x (coordinateBasis (n+1)) := by
  obtain ⟨η, hη, hηeq⟩ := exists_puncture_regularization hU hr ω hω
  have hstokes := integral_extDeriv_regular_partition hU hg a ρ hWo hCW hρc hρsub hsum η hη
  have hD : MeasurableSet (regularSublevel U g R) :=
    (isOpen_regularSublevel hU hg).measurableSet
  have hCB : MeasurableSet (coordClosedBall (n+1) r) :=
    (isCompact_coordClosedBall (n+1) r).measurableSet
  have htrace (i : a.Index) :
      chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R (fun z => ρ (some i) z • η z) =
      chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R (fun z => ρ (some i) z • ω z) := by
    apply chartBoundaryFlux_congr
    intro x _ hxlevel
    by_cases hz : ρ (some i) x = 0
    · simp [hz]
    · have hxU : x ∈ U := (a.patch i).domain_U (hρsub (some i) (subset_tsupport (ρ (some i)) hz))
      have hxg : g x = R := by
        simpa [RegularBoundaryPatch.chart_eq, levelCoordinates] using hxlevel
      have hxB : x ∉ coordBall (n+1) r := by
        intro h
        have hlt := (hB (show x ∈ coordClosedBall (n+1) r from (show radiusSq x < r^2 from h).le)).2
        exact (ne_of_lt hlt) hxg
      rw [(hηeq x hxB).self_of_nhds]
  have hsphere : sphereFlux r η = sphereFlux r ω := by
    apply sphereFlux_congr
    intro x hx
    exact (hηeq x (by change ¬radiusSq x < r^2; rw [hx]; exact lt_irrefl _)).self_of_nhds
  have hball : (∫ x in coordClosedBall (n+1) r, extDeriv η x (coordinateBasis (n+1))) =
      sphereFlux r η := by
    rw [integral_closedBall_eq_ball]
    exact integral_extDeriv_ball_local r η hU hη (hB.trans inter_subset_left)
  have hvolume :
      (∫ x in regularSublevel U g R \ coordClosedBall (n+1) r,
        extDeriv ω x (coordinateBasis (n+1))) =
      (∫ x in regularSublevel U g R, extDeriv η x (coordinateBasis (n+1))) - sphereFlux r η := by
    calc
      _ = ∫ x in regularSublevel U g R \ coordClosedBall (n+1) r,
          extDeriv η x (coordinateBasis (n+1)) := by
        apply setIntegral_congr_fun (hD.diff hCB)
        intro x hx
        have hxB : x ∉ coordBall (n+1) r := fun h => hx.2 (show x ∈ coordClosedBall (n+1) r from (show radiusSq x < r^2 from h).le)
        dsimp only
        rw [(hηeq x hxB).extDeriv_eq]
      _ = _ := (setIntegral_sdiff hCB
        (integrableOn_extDeriv_compact_closure hU hη hc hcl) hB).trans (by rw [hball])
  rw [hstokes, hsphere] at hvolume
  simp_rw [htrace] at hvolume
  exact hvolume.symm

/-- General punctured regular-sublevel Stokes. The original form is C1 only
away from zero. The inner sphere is oriented outward from the ball and is
subtracted exactly once. All terms are actual Lebesgue chart integrals. -/
theorem exists_punctured_sublevel_stokes {n : ℕ} {U : Set (Fin (n+1) → ℝ)}
    {g : (Fin (n+1) → ℝ) → ℝ} {R r : ℝ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (hc : IsCompact (closure (regularSublevel U g R)))
    (hcl : closure (regularSublevel U g R) ⊆ U)
    (hreg : ∀ x ∈ U, g x = R → fderiv ℝ g x ≠ 0)
    (hr : 0 < r) (hB : coordClosedBall (n+1) r ⊆ regularSublevel U g R)
    (ω : (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hω : ContDiffOn ℝ 1 ω (U \ {0})) :
    ∃ (a : RegularBoundaryAtlas (n+1) U g (frontier (regularSublevel U g R)))
      (W : Set (Fin (n+1) → ℝ))
      (ρ : SmoothPartitionOfUnity (Option a.Index) 𝓘(ℝ, Fin (n+1) → ℝ)
        (Fin (n+1) → ℝ) (closure W)),
      IsOpen W ∧ closure (regularSublevel U g R) ⊆ W ∧
      (∀ i, HasCompactSupport (ρ i)) ∧
      (∀ i, tsupport (ρ (some i)) ⊆ (a.patch i).domain) ∧
      (∀ x ∈ W, ∑ i, ρ i x = 1) ∧
      (∑ i : a.Index, chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R
        (fun z => ρ (some i) z • ω z)) - sphereFlux r ω =
        ∫ x in regularSublevel U g R \ coordClosedBall (n+1) r,
          extDeriv ω x (coordinateBasis (n+1)) := by
  obtain ⟨a⟩ := exists_sublevelBoundaryAtlas hU hg hc hcl hreg
  obtain ⟨W, ρ, hWo, hCW, _, hρsub, hρc, hsum⟩ :=
    exists_sublevel_partition hU hg.continuousOn hc a
  exact ⟨a, W, ρ, hWo, hCW, hρc, (fun i => hρsub (some i)), hsum,
    punctured_sublevel_stokes_of_partition hU hg.continuousOn hc hcl hr hB
      a ρ hWo hCW hρc hρsub hsum ω hω⟩

end MahlerStokes

end

end OAI
