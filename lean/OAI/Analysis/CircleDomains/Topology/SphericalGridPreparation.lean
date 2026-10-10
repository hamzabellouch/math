import OAI.Analysis.CircleDomains.Transfer.GridPreparation
import OAI.Analysis.CircleDomains.Transfer.RegularCore

namespace OAI

/-!
# Grid preparation while retaining a neighborhood of infinity

The physical domain has compact complement in the finite chart. The
retained core is an actual regular sublevel, contains every prescribed
closed part of the domain, and has compact complement. Its compactly
supported cutoff leaves the coordinates unchanged near infinity.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_regular_core_cutoff_and_grid
    (hsard : SmoothPlanarSard)
    {G K₀ : Set (ℝ × ℝ)} (hG : IsOpen G) (hGc : IsCompact Gᶜ)
    (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ G)
    {n : ℕ} (u : Fin n → (ℝ × ℝ) → ℝ) (huM : ∀ i, Measurable (u i))
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) G)
    (hu2 : ∀ i, MemLp (planarGradient (u i)) 2 (volume.restrict G))
    {S : Type*} [Countable S] (F : Set S) (hF : F.Finite) (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2))
    (P : ℕ → (Fin n → ℝ) → Prop)
    (hP : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, P N θ)
    {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ (K : Set (ℝ × ℝ)) (ψ χ : (ℝ × ℝ) → ℝ) (t : ℝ) (N : ℕ) (θ : Fin n → ℝ),
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ t ∈ Ioo 0 1 ∧
      (∀ z, ψ z = t → fderiv ℝ ψ z ≠ 0) ∧ K = {z | ψ z ≤ t} ∧
      IsClosed K ∧ K₀ ⊆ interior K ∧ K ⊆ G ∧ IsCompact (closure Kᶜ) ∧
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ z, χ z ∈ Icc 0 1) ∧
      (∀ᶠ z in 𝓝ˢ K, χ z = 0) ∧ (∀ᶠ z in 𝓝ˢ Gᶜ, χ z = 1) ∧
      reciprocalGridStep N < ρ ∧ P N θ ∧
      (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).Finite ∧
      reciprocalGridStep N *
        Real.sqrt ((gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).ncard : ℝ) < η ∧
      (∀ k, IntegrableOn (coordinateWedges (natCoordinateFamily
        (cutoffCoordinateFamily u χ (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) k) θ)) n) (G \ K)) ∧
      ∃ᶠ k in atTop, (∫ z in G \ K, coordinateWedges (natCoordinateFamily
        (cutoffCoordinateFamily u χ (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) k) θ)) n z) < η := by
  obtain ⟨ψ, t, K, hψ, hψc, ht, hreg, hKdef, hK, hK₀K, hKG, hKc, hcost⟩ :=
    exists_regular_core_small_tail hsard hG hGc hK₀ hK₀G
      (integrable_coordinateWedges_of_memLp u hu2) (coordinateWedges_nonneg _ _)
      (ε := η / 4) (div_pos hη (by norm_num))
  obtain ⟨χ, hχ, hχc, hχrange, hχzero, hχone, hχ2⟩ :=
    exists_cutoff_near_complement hGc hK hKG
  have hu2' (i : Fin n) : MemLp (planarGradient (u i)) 2 (volume.restrict (G \ K)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume sdiff_subset) (hu2 i)
  have hχ2' : MemLp (planarGradient χ) 2 (volume.restrict (G \ K)) :=
    MemLp.mono_measure Measure.restrict_le_self hχ2
  have hd : ∀ᵐ z ∂volume.restrict (G \ K),
      DifferentiableAt ℝ χ z ∧ ∀ i, DifferentiableAt ℝ (u i) z := by
    filter_upwards [ae_restrict_mem (hG.measurableSet.diff hK.measurableSet)] with z hz
    exact ⟨hχ.differentiable (by simp) z,
      fun i => ((hu i).contDiffAt (hG.mem_nhds hz.1)).differentiableAt (by simp)⟩
  have hsmall : (∑ p : UpperPairs n, ∫ z in G \ K,
      |planarWedge (planarGradient (u (upperPair p).1) z)
        (planarGradient (u (upperPair p).2) z)|) < η / 4 :=
    (integral_coordinateWedges_eq_sum u hu2').symm.trans_lt hcost
  obtain ⟨N, θ, hN, hPθ, hfin, hcard, hint, hgood⟩ :=
    exists_grid_for_actual_coordinate_wedges u χ huM hχ.continuous.measurable
      (fun i => measurable_planarGradient (u i)) (measurable_planarGradient χ)
      hu2' hχ2' hd (fun z => (hχrange z).1) (fun z => (hχrange z).2)
      F hF a b hwidth hwidth2 P hP hη hρ hsmall
  exact ⟨K, ψ, χ, t, N, θ, hψ, hψc, ht, hreg, hKdef, hK, hK₀K, hKG, hKc,
    hχ, hχc, hχrange, hχzero, hχone, hN, hPθ, hfin, hcard, hint, hgood⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
