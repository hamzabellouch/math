import OAI.Analysis.Mahler.SourceCoordinateForms

namespace OAI

open Set Filter MeasureTheory ContinuousAlternatingMap MahlerStokes
open scoped Topology Manifold

namespace Mahler
noncomputable section
variable {n N m : ℕ} {U : Set (ComplexEuclidean n)}
  {f : Fin N → ComplexEuclidean n → ℂ} {G : Fin N → MvPolynomial (Fin n) ℂ}

theorem MassHypotheses.contDiffAt_tau (h : MassHypotheses n N m U f G)
    {x : ComplexEuclidean n} (hx : x ∈ U) (r : ℕ) : ContDiffAt ℝ r (tau f) x := by
  have he : (fun z => (energy f z).re) = tau f := by
    funext z; simp only [energy_eq_tau, Complex.ofReal_re]
  rw [← he]
  exact Complex.reCLM.contDiff.contDiffAt.comp x (h.contDiffAt_energy hx r)

theorem MassHypotheses.contDiffOn_coordinateTau (h : MassHypotheses n N m U f G)
    {d : ℕ} (Ψ : (Fin d → ℝ) ≃L[ℝ] ComplexEuclidean n) (r : ℕ) :
    ContDiffOn ℝ r (fun x => tau f (Ψ x)) (Ψ ⁻¹' U) := by
  intro x hx
  exact ((h.contDiffAt_tau hx r).comp x Ψ.contDiff.contDiffAt).contDiffWithinAt

lemma source_sublevel_preimage {d : ℕ} (Ψ : (Fin d → ℝ) ≃L[ℝ] ComplexEuclidean n) (R : ℝ) :
    regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R =
      Ψ ⁻¹' (U ∩ {x | tau f x < R}) := rfl

theorem MassHypotheses.coordinate_compact_sublevels (h : MassHypotheses n N m U f G)
    {d : ℕ} (Ψ : (Fin d → ℝ) ≃L[ℝ] ComplexEuclidean n)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) :
    IsCompact (closure (regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R)) ∧
      closure (regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R) ⊆ Ψ ⁻¹' U := by
  have he : closure (Ψ ⁻¹' (U ∩ {x | tau f x < R})) =
      Ψ ⁻¹' closure (U ∩ {x | tau f x < R}) :=
    (Ψ.toHomeomorph.preimage_closure (U ∩ {x | tau f x < R})).symm
  rw [source_sublevel_preimage, he]
  obtain ⟨hc, hs⟩ := h.compact_sublevels R hR hR1
  exact ⟨Ψ.toHomeomorph.isCompact_preimage.mpr hc, preimage_mono hs⟩

theorem MassHypotheses.coordinate_regular (h : MassHypotheses n N m U f G)
    {d : ℕ} (Ψ : (Fin d → ℝ) ≃L[ℝ] ComplexEuclidean n) {R : ℝ}
    (hreg : ∀ x ∈ U, tau f x = R → fderiv ℝ (tau f) x ≠ 0) :
    ∀ x ∈ Ψ ⁻¹' U, tau f (Ψ x) = R → fderiv ℝ (fun y => tau f (Ψ y)) x ≠ 0 := by
  intro x hx he hz
  have hd := ((h.contDiffAt_tau hx 1).differentiableAt (by norm_num)).hasFDerivAt.comp x Ψ.hasFDerivAt
  change HasFDerivAt (fun y => tau f (Ψ y)) _ x at hd
  rw [hd.fderiv] at hz
  apply hreg (Ψ x) hx he
  ext v
  have hv := congrArg (fun L : (Fin d → ℝ) →L[ℝ] ℝ => L (Ψ.symm v)) hz
  simpa using hv

/-- A single regular-level atlas and partition yield
Stokes identities for both coordinate forms. The punctured identity holds for every
admissible inner radius with that same outer representation. No differential
identity or positivity is a premise. Identification of the
integrands with top wedge powers is not asserted here. -/
theorem exists_source_stokes_partition (h : MassHypotheses n N m U f G) (k : ℕ)
    (Ψ : (Fin ((2*k+1)+1) → ℝ) ≃L[ℝ] ComplexEuclidean n)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hreg : ∀ x ∈ U, tau f x = R → fderiv ℝ (tau f) x ≠ 0) :
    ∃ (a : RegularBoundaryAtlas ((2*k+1)+1) (Ψ ⁻¹' U) (fun x => tau f (Ψ x))
        (frontier (regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R)))
      (W : Set (Fin ((2*k+1)+1) → ℝ))
      (ρ : SmoothPartitionOfUnity (Option a.Index) 𝓘(ℝ, Fin ((2*k+1)+1) → ℝ)
        (Fin ((2*k+1)+1) → ℝ) (closure W)),
      IsOpen W ∧ closure (regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R) ⊆ W ∧
      (∀ i, HasCompactSupport (ρ i)) ∧ ρ.IsSubordinate (sublevelPatchDomain a) ∧
      (∀ x ∈ W, ∑ i, ρ i x = 1) ∧
      (∫ x in regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R,
        extDeriv (sourceCoordinateForm Ψ (energy f) k) x (coordinateBasis ((2*k+1)+1))) =
        (∑ i : a.Index, chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R
          (fun z => ρ (some i) z • sourceCoordinateForm Ψ (energy f) k z)) ∧
      (∀ r : ℝ, 0 < r →
        coordClosedBall ((2*k+1)+1) r ⊆ regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R →
        (∑ i : a.Index, chartBoundaryFlux (a.patch i).chart (a.patch i).coordinate R
          (fun z => ρ (some i) z • sourceCoordinateForm Ψ (logTau f) k z)) -
            sphereFlux r (sourceCoordinateForm Ψ (logTau f) k) =
          ∫ x in regularSublevel (Ψ ⁻¹' U) (fun x => tau f (Ψ x)) R \ coordClosedBall ((2*k+1)+1) r,
            extDeriv (sourceCoordinateForm Ψ (logTau f) k) x (coordinateBasis ((2*k+1)+1))) := by
  have ho : IsOpen (Ψ ⁻¹' U) := h.open_domain.preimage Ψ.continuous
  have hg := h.contDiffOn_coordinateTau Ψ 2
  obtain ⟨hc, hcl⟩ := h.coordinate_compact_sublevels Ψ hR hR1
  obtain ⟨a⟩ := exists_sublevelBoundaryAtlas ho hg hc hcl (h.coordinate_regular Ψ hreg)
  obtain ⟨W, ρ, hWo, hCW, _, hρsub, hρc, hsum⟩ :=
    exists_sublevel_partition ho hg.continuousOn hc a
  refine ⟨a, W, ρ, hWo, hCW, hρc, hρsub, hsum, ?_, ?_⟩
  · exact integral_extDeriv_regular_partition ho hg.continuousOn a ρ hWo hCW hρc hρsub hsum
      (sourceCoordinateForm Ψ (energy f) k) (h.contDiffOn_coordinateEnergy Ψ k)
  · intro r hr hB
    exact punctured_sublevel_stokes_of_partition ho hg.continuousOn hc hcl hr hB
      a ρ hWo hCW hρc hρsub hsum (sourceCoordinateForm Ψ (logTau f) k)
      (h.contDiffOn_coordinateLog Ψ k)

end
end Mahler

end OAI
