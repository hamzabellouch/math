import OAI.Analysis.CircleDomains.Transfer.FilledMetric
import OAI.Analysis.CircleDomains.Sobolev.StaircaseGradient

namespace OAI

/-!
# The actual finite wedge sum and its pair indexing

Each unordered coordinate pair occurs exactly once. This identifies the
spatial cost selected by the random-grid argument with the wedge sum of
the actual cutoff staircase differentials.
-/

open Set MeasureTheory Finset Filter

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

abbrev UpperPairs (n : ℕ) := (j : Fin n) × Fin j.val

def upperPair {n : ℕ} (p : UpperPairs n) : Fin n × Fin n :=
  (⟨p.2.val, p.2.isLt.trans p.1.isLt⟩, p.1)

theorem upperPair_ne {n : ℕ} (p : UpperPairs n) : (upperPair p).1 ≠ (upperPair p).2 := by
  intro heq
  have h := congrArg Fin.val heq
  exact (Nat.ne_of_lt p.2.isLt) h

theorem upperPair_covers {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ∃ p : UpperPairs n, upperPair p = (i,j) ∨ upperPair p = (j,i) := by
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨⟨j, ⟨i.val, h⟩⟩, Or.inl ?_⟩
    rfl
  · refine ⟨⟨i, ⟨j.val, h⟩⟩, Or.inr ?_⟩
    rfl

theorem covectorWedges_eq_sum_upperPairs (x y : ℕ → ℝ) (n : ℕ) :
    covectorWedges x y n =
      ∑ p : UpperPairs n, |x p.2.val * y p.1.val - x p.1.val * y p.2.val| := by
  rw [Fintype.sum_sigma]
  unfold covectorWedges
  rw [Finset.sum_range]
  apply sum_congr rfl
  intro j _
  exact Finset.sum_range (fun i : ℕ => |x i * y j.val - x j.val * y i|)

theorem coordinateWedges_eq_sum_upperPairs
    {n : ℕ} (f : Fin n → (ℝ × ℝ) → ℝ) (z : ℝ × ℝ) :
    coordinateWedges (natCoordinateFamily f) n z =
      ∑ p : UpperPairs n,
        |planarWedge (planarGradient (f (upperPair p).1) z)
          (planarGradient (f (upperPair p).2) z)| := by
  rw [coordinateWedges, covectorWedges_eq_sum_upperPairs]
  apply sum_congr rfl
  intro p _
  have h₁ := p.2.isLt.trans p.1.isLt
  have h₂ := p.1.isLt
  simp only [natCoordinateFamily, dite_eq_left h₁, dite_eq_left h₂, upperPair,
    planarWedge, mul_comm]

/-- Exact identity with the random-grid cost; the integrability
hypotheses concern only the finitely many selected spatial pair costs. -/
theorem integral_cutoff_wedges_eq_staircaseWedgeCost
    {μ : Measure (ℝ × ℝ)} {n : ℕ}
    (u : Fin n → (ℝ × ℝ) → ℝ) (χ : (ℝ × ℝ) → ℝ)
    {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ < h / 4) (θ : Fin n → ℝ)
    (hd : ∀ᵐ z ∂μ, DifferentiableAt ℝ χ z ∧ ∀ i, DifferentiableAt ℝ (u i) z)
    (hi : ∀ p : UpperPairs n, Integrable (fun z => |planarWedge
      (staircaseCovector h δ (χ z) (θ (upperPair p).1) (u (upperPair p).1 z)
        (planarGradient (u (upperPair p).1) z) (planarGradient χ z))
      (staircaseCovector h δ (χ z) (θ (upperPair p).2) (u (upperPair p).2 z)
        (planarGradient (u (upperPair p).2) z) (planarGradient χ z))|) μ) :
    (∫ z, coordinateWedges (natCoordinateFamily
      (fun i => cutoffStaircase (u i) χ (shiftedStaircase h δ (θ i)))) n z ∂μ) =
      staircaseWedgeCost μ upperPair (fun i => planarGradient (u i)) (planarGradient χ)
        u χ h δ θ := by
  unfold staircaseWedgeCost staircasePairCost
  rw [← integral_finsetSum _ (fun p _ => hi p)]
  apply integral_congr_ae
  filter_upwards [hd] with z hz
  rw [coordinateWedges_eq_sum_upperPairs]
  apply sum_congr rfl
  intro p _
  rw [planarGradient_cutoffStaircase (hz.2 _) hz.1 hh hδ hδh,
    planarGradient_cutoffStaircase (hz.2 _) hz.1 hh hδ hδh]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
