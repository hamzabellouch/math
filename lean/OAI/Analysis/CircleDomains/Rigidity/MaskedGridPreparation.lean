import OAI.Analysis.CircleDomains.Rigidity.MaskedCorePreparation
import OAI.Analysis.CircleDomains.Transfer.GridPreparation

namespace OAI

/-!
# Preparing the actual masked circle transfer

The regular core contains every mask boundary, the cutoff is constructed,
and the actual reciprocal grid and good widths are selected from the
original masked L² data. No modified-coordinate integrability is assumed.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem integral_maskedCircleWedges_eq_intersections
    {μ : Measure (ℝ × ℝ)} {n : ℕ}
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, MeasurableSet (M i))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, MemLp (circleGradient (f i)) 2 (μ.restrict (M i))) :
    (∫ z, maskedCircleWedges M f z ∂μ) =
      ∑ p : UpperPairs n, ∫ z in M (upperPair p).1 ∩ M (upperPair p).2,
        |planarWedge (circleGradient (f (upperPair p).1) z)
          (circleGradient (f (upperPair p).2) z)| ∂μ := by
  have hi (i : Fin n) : MemLp ((M i).indicator (circleGradient (f i))) 2 μ :=
    (memLp_indicator_iff_restrict (hM i)).mpr (hf i)
  unfold maskedCircleWedges
  rw [integral_finsetSum _ (fun p _ =>
    integrable_abs_planarWedge_of_memLp (hi (upperPair p).1) (hi (upperPair p).2))]
  apply sum_congr rfl
  intro p _
  exact integral_abs_wedge_indicators μ (hM _) (hM _) _ _

theorem exists_regular_masked_core_cutoff_and_grid
    (hsard : SmoothPlanarSard) {G K₀ : Set (ℝ × ℝ)}
    (hG : IsOpen G) (hGc : IsCompact Gᶜ) (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ G)
    {n : ℕ} {S : Type*} [Countable S]
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, MeasurableSet (M i))
    (hboundaryG : ∀ i, frontier (M i) ⊆ G)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, SmoothCircleOn (f i) (G ∩ interior (M i)))
    (hmf : ∀ i, Measurable (f i)) (hdf : ∀ i, Measurable (circleGradient (f i)))
    (hf2 : ∀ i, MemLp (circleGradient (f i)) 2 ((volume.restrict G).restrict (M i)))
    (F : Set S) (hF : F.Finite) (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2))
    (P : ℕ → (Fin n → ℝ) → Prop) (hP : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, P N θ)
    {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ (ψ : (ℝ × ℝ) → ℝ) (t : ℝ) (K : Set (ℝ × ℝ))
      (χ : (ℝ × ℝ) → ℝ) (N : ℕ) (θ : Fin n → ℝ),
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ t ∈ Set.Ioo 0 1 ∧
      (∀ z, ψ z = t → fderiv ℝ ψ z ≠ 0) ∧ K = {z | ψ z ≤ t} ∧
      IsClosed K ∧ K₀ ⊆ interior K ∧ K ⊆ G ∧ IsCompact (closure Kᶜ) ∧
      (∀ i, frontier (M i) ⊆ interior K) ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ z, χ z ∈ Set.Icc 0 1) ∧
      (∀ᶠ z in 𝓝ˢ K, χ z = 0) ∧ (∀ᶠ z in 𝓝ˢ Gᶜ, χ z = 1) ∧
      reciprocalGridStep N < ρ ∧ P N θ ∧
      (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).Finite ∧
      reciprocalGridStep N *
        Real.sqrt ((gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).ncard : ℝ) < η ∧
      (∀ k, IntegrableOn (maskedCircleWedges M (circleCutoffFamily f χ N
        (staircaseWidth (reciprocalGridStep N) k) θ)) (G \ K)) ∧
      ∃ᶠ k in atTop, (∫ z in G \ K, maskedCircleWedges M (circleCutoffFamily f χ N
        (staircaseWidth (reciprocalGridStep N) k) θ) z) < η := by
  obtain ⟨ψ, t, K, χ, hψ, hψc, ht, hreg, hKeq, hK, hK₀K, hKG, hKc,
      hbd, hsmall, hχ, hχc, hχrange, hχzero, hχone, hχ2⟩ :=
    exists_regular_masked_core_and_cutoff hsard hG hGc hK₀ hK₀G M hM hboundaryG f hf2
      (η := η / 4) (div_pos hη (by norm_num))
  have hftail (i : Fin n) : MemLp (circleGradient (f i)) 2
      ((volume.restrict (G \ K)).restrict (M i)) :=
    (hf2 i).mono_measure (Measure.restrict_mono_measure
      (Measure.restrict_mono_set volume Set.sdiff_subset) (M i))
  have hsum : (∑ p : UpperPairs n, ∫ z in M (upperPair p).1 ∩ M (upperPair p).2,
      |planarWedge (circleGradient (f (upperPair p).1) z)
        (circleGradient (f (upperPair p).2) z)| ∂volume.restrict (G \ K)) < η / 4 := by
    rw [← integral_maskedCircleWedges_eq_intersections M hM f hftail]
    exact hsmall
  obtain ⟨N, θ, hN, hPθ, hfin, hcard, hvi, hgood⟩ :=
    exists_grid_for_actual_masked_circle_wedges hG hK.measurableSet M hM
      (fun i => (hbd i).trans interior_subset) f χ hf hmf hdf hftail hχ
      (measurable_planarGradient χ) (hχ2.mono_measure Measure.restrict_le_self)
      (fun z => (hχrange z).1) (fun z => (hχrange z).2)
      F hF a b hwidth hwidth2 P hP hη hρ hsum
  exact ⟨ψ, t, K, χ, N, θ, hψ, hψc, ht, hreg, hKeq, hK, hK₀K, hKG, hKc, hbd,
    hχ, hχc, hχrange, hχzero, hχone, hN, hPθ, hfin, hcard, hvi, hgood⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
