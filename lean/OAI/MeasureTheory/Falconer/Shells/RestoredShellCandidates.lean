import OAI.MeasureTheory.Falconer.Recursion.RetainedPairMasks
import OAI.MeasureTheory.Falconer.Estimates.ActualClassFamilies

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem weightedProductInput_finite (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r) (hsep : ∀ᵐ z ∂μ.prod ν, r ≤ dist z.1 z.2) :
    IsFiniteMeasure ((μ.prod ν).withDensity distanceWeight) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  apply lt_of_le_of_lt (b := ENNReal.ofReal (r^(-1/2:ℝ))) _ ENNReal.ofReal_lt_top
  calc
    _ ≤ ∫⁻ _ : Plane × Plane, ENNReal.ofReal (r^(-1/2:ℝ)) ∂μ.prod ν := by
      apply lintegral_mono_ae
      filter_upwards [hsep] with z hz
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hr hz (by norm_num))
    _ = _ := by simp

noncomputable def restoredShellCandidate (Q : DyadicSquare) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) : Measure ℝ :=
  ((μ.prod ν).withDensity (fun z => distanceWeight z*restoredShellMask Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β z)).map
    (fun z => dist z.1 z.2)

noncomputable def restoredShellRemoved (Q : DyadicSquare) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) : Measure ℝ :=
  ((μ.prod ν).withDensity (fun z => distanceWeight z*(1-restoredShellMask Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β z))).map
    (fun z => dist z.1 z.2)

theorem restoredShellCandidate_decomposition (Q : DyadicSquare) (hQ : 0 < Q.side) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) :
    weightedDistance (μ.prod ν) = restoredShellCandidate Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β+
      restoredShellRemoved Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β := by
  exact masked_pushforward_decomposition (μ.prod ν) (fun z => dist z.1 z.2) (by fun_prop)
    distanceWeight (restoredShellMask Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β) (by unfold distanceWeight; fun_prop)
    (measurable_restoredShellMask _ _ _ _ _ _ _ _ _ _ _ _)
    (restoredShellMask_le_one Q hQ _ _ _ _ _ _ _ _ _ _ _)

theorem restoredShellCandidate_finite (Q : DyadicSquare) (hQ : 0 < Q.side) (μ ν : Measure Plane)
    [IsFiniteMeasure ((μ.prod ν).withDensity distanceWeight)]
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) :
    IsFiniteMeasure (restoredShellCandidate Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β) ∧
      IsFiniteMeasure (restoredShellRemoved Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β) :=
  finite_summands _ _ _ (restoredShellCandidate_decomposition Q hQ μ ν m₁ m₂ N B₁ B₂ lam sig kap β)

theorem restoredShellCandidate_totalVariation (Q : DyadicSquare) (hQ : 0 < Q.side) (μ ν : Measure Plane)
    [IsFiniteMeasure ((μ.prod ν).withDensity distanceWeight)]
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) :
    let h := restoredShellCandidate_finite Q hQ μ ν m₁ m₂ N B₁ B₂ lam sig kap β
    letI := h.1
    letI := h.2
    ((weightedDistance (μ.prod ν)).toSignedMeasure-
      (restoredShellCandidate Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β).toSignedMeasure).totalVariation =
      restoredShellRemoved Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β := by
  let := (restoredShellCandidate_finite Q hQ μ ν m₁ m₂ N B₁ B₂ lam sig kap β).1
  let := (restoredShellCandidate_finite Q hQ μ ν m₁ m₂ N B₁ B₂ lam sig kap β).2
  exact totalVariation_sub_of_add _ _ _ (restoredShellCandidate_decomposition Q hQ μ ν m₁ m₂ N B₁ B₂ lam sig kap β)

theorem actual_candidate_construction (Q : DyadicSquare) (hQ : Q.side = 1)
    (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμQ : μ Q.carrierᶜ = 0) (hνQ : ν Q.carrierᶜ = 0)
    {δ C₁ C₂ lam sig r : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hlam : 0 < lam) (hsig : 0 < sig)
    (hμball : ∀ x : Plane, ∀ s > 0, μ (ball x s) ≤ ENNReal.ofReal (C₁*s^(1+δ)))
    (hνball : ∀ x : Plane, ∀ s > 0, ν (ball x s) ≤ ENNReal.ofReal (C₂*s^(1+δ)))
    (hr : 0 < r) (hsep : ∀ᵐ z ∂μ.prod ν, r ≤ dist z.1 z.2) :
    ∃ H₁ H₂ N₀ : ℕ, 0 < H₁ ∧ 0 < H₂ ∧ (H₁:ℝ) ≤ 1/lam+2 ∧ (H₂:ℝ) ≤ 1/lam+2 ∧
      ∀ N ≥ N₀, ∃ m₁ m₂ : List ℕ → ℝ → ℝ,
        ActualClassFamily Q μ N H₁ δ lam sig m₁ ∧ ActualClassFamily Q ν N H₂ δ lam sig m₂ ∧
        ∀ kap β : ℝ, IsFiniteMeasure (restoredShellCandidate Q μ ν m₁ m₂ N (N/H₁) (N/H₂) lam sig kap β) := by
  obtain ⟨H₁,N₁,hH₁,hB₁,hF₁⟩ := actual_class_family Q hQ μ hμQ hC₁ hlam hsig hμball
  obtain ⟨H₂,N₂,hH₂,hB₂,hF₂⟩ := actual_class_family Q hQ ν hνQ hC₂ hlam hsig hνball
  let := weightedProductInput_finite μ ν hr hsep
  refine ⟨H₁,H₂,max N₁ N₂,hH₁,hH₂,hB₁,hB₂,?_⟩
  intro N hN
  obtain ⟨m₁,hm₁⟩ := hF₁ N (by omega)
  obtain ⟨m₂,hm₂⟩ := hF₂ N (by omega)
  refine ⟨m₁,m₂,hm₁,hm₂,?_⟩
  intro kap β
  exact (restoredShellCandidate_finite Q (by rw [hQ]; norm_num) μ ν m₁ m₂ N (N/H₁) (N/H₂) lam sig kap β).1

end PlanarFalconer

end OAI
