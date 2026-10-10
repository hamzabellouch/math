import OAI.Analysis.CircleDomains.Selection.UpperPairs
import OAI.Analysis.CircleDomains.Sobolev.FixedWidthIntegrability

namespace OAI

/-!
# Grid selection for the actual cutoff coordinate differentials

All fixed-width spatial integrability follows from the original L²
covectors. The selected random cost is exactly the integral of the
unordered wedge sum of the actual modified scalar coordinates.
-/

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def cutoffCoordinateFamily {n : ℕ}
    (u : Fin n → (ℝ × ℝ) → ℝ) (χ : (ℝ × ℝ) → ℝ)
    (h δ : ℝ) (θ : Fin n → ℝ) : Fin n → (ℝ × ℝ) → ℝ :=
  fun i => cutoffStaircase (u i) χ (shiftedStaircase h δ (θ i))

theorem cutoff_wedges_integrable_and_eq_cost
    {μ : Measure (ℝ × ℝ)} {n : ℕ}
    (u : Fin n → (ℝ × ℝ) → ℝ) (χ : (ℝ × ℝ) → ℝ)
    (hu : ∀ i, Measurable (u i)) (hχ : Measurable χ)
    (hdu : ∀ i, Measurable (planarGradient (u i))) (hdχ : Measurable (planarGradient χ))
    (hu2 : ∀ i, MemLp (planarGradient (u i)) 2 μ) (hχ2 : MemLp (planarGradient χ) 2 μ)
    (hd : ∀ᵐ z ∂μ, DifferentiableAt ℝ χ z ∧ ∀ i, DifferentiableAt ℝ (u i) z)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1) (θ : Fin n → ℝ) :
    Integrable (coordinateWedges (natCoordinateFamily (cutoffCoordinateFamily u χ h δ θ)) n) μ ∧
      (∫ z, coordinateWedges (natCoordinateFamily (cutoffCoordinateFamily u χ h δ θ)) n z ∂μ) =
        staircaseWedgeCost μ upperPair (fun i => planarGradient (u i))
          (planarGradient χ) u χ h δ θ := by
  let d : UpperPairs n → (ℝ × ℝ) → ℝ := fun p z => |planarWedge
    (staircaseCovector h δ (χ z) (θ (upperPair p).1) (u (upperPair p).1 z)
      (planarGradient (u (upperPair p).1) z) (planarGradient χ z))
    (staircaseCovector h δ (χ z) (θ (upperPair p).2) (u (upperPair p).2 z)
      (planarGradient (u (upperPair p).2) z) (planarGradient χ z))|
  have hi (p : UpperPairs n) : Integrable (d p) μ :=
    integrable_staircase_pair_at_shifts_of_memLp _ _ _ _ _ _
      (hdu _) (hdu _) hdχ (hu _) (hu _) hχ (hu2 _) (hu2 _) hχ2
      hh hδ hδh hχ0 hχ1 _ _
  have heq : coordinateWedges (natCoordinateFamily (cutoffCoordinateFamily u χ h δ θ)) n
      =ᵐ[μ] fun z => ∑ p, d p z := by
    filter_upwards [hd] with z hz
    rw [coordinateWedges_eq_sum_upperPairs]
    apply Finset.sum_congr rfl
    intro p _
    dsimp only [cutoffCoordinateFamily, d]
    rw [planarGradient_cutoffStaircase (hz.2 _) hz.1 hh hδ hδh,
      planarGradient_cutoffStaircase (hz.2 _) hz.1 hh hδ hδh]
  refine ⟨(integrable_finsetSum _ (fun p _ => hi p)).congr heq.symm, ?_⟩
  exact integral_cutoff_wedges_eq_staircaseWedgeCost u χ hh hδ hδh θ hd hi

/-- The selected spacing and shifts control actual coordinate gradients,
and every width has an integrable spatial wedge sum. -/
theorem exists_grid_for_actual_coordinate_wedges
    {μ : Measure (ℝ × ℝ)} [SFinite μ] {n : ℕ} {S : Type*} [Countable S]
    (u : Fin n → (ℝ × ℝ) → ℝ) (χ : (ℝ × ℝ) → ℝ)
    (hu : ∀ i, Measurable (u i)) (hχ : Measurable χ)
    (hdu : ∀ i, Measurable (planarGradient (u i))) (hdχ : Measurable (planarGradient χ))
    (hu2 : ∀ i, MemLp (planarGradient (u i)) 2 μ) (hχ2 : MemLp (planarGradient χ) 2 μ)
    (hd : ∀ᵐ z ∂μ, DifferentiableAt ℝ χ z ∧ ∀ i, DifferentiableAt ℝ (u i) z)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (F : Set S) (hF : F.Finite) (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2))
    (Q : ℕ → (Fin n → ℝ) → Prop)
    (hQ : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, Q N θ)
    {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ)
    (hsmall : (∑ p : UpperPairs n, ∫ z,
      |planarWedge (planarGradient (u (upperPair p).1) z)
        (planarGradient (u (upperPair p).2) z)| ∂μ) < η / 4) :
    ∃ (N : ℕ) (θ : Fin n → ℝ), reciprocalGridStep N < ρ ∧ Q N θ ∧
      (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).Finite ∧
      reciprocalGridStep N *
        Real.sqrt ((gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).ncard : ℝ) < η ∧
      (∀ k, Integrable (coordinateWedges (natCoordinateFamily
        (cutoffCoordinateFamily u χ (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) k) θ)) n) μ) ∧
      ∃ᶠ k in atTop, (∫ z, coordinateWedges (natCoordinateFamily
        (cutoffCoordinateFamily u χ (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) k) θ)) n z ∂μ) < η := by
  obtain ⟨N, θ, hN, hQθ, hfin, hcard, hgood⟩ :=
    exists_grid_for_actual_wedge_cost upperPair upperPair_ne
      (fun i => planarGradient (u i)) (planarGradient χ) u χ
      hdu hdχ hu hχ hu2 hχ2 hχ0 hχ1 F hF a b hwidth hwidth2 Q hQ hη hρ hsmall
  have hcost (k : ℕ) := cutoff_wedges_integrable_and_eq_cost u χ hu hχ hdu hdχ hu2 hχ2 hd
    (reciprocalGridStep_pos N) (staircaseWidth_pos (reciprocalGridStep_pos N) k)
    (staircaseWidth_lt (reciprocalGridStep_pos N) k) hχ0 hχ1 θ
  refine ⟨N, θ, hN, hQθ, hfin, hcard, fun k => (hcost k).1, ?_⟩
  exact hgood.mono (fun k hk => (hcost k).2.trans_lt hk)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
