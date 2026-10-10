import OAI.Analysis.CircleDomains.Topology.CoreCutoff
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace OAI

/-!
# Preparing the actual random grid from finite-energy coordinates

The retained core, cutoff, cutoff energy and small original wedge sum
are all constructed. The only grid event supplied to the selection is
an explicitly conull event, as in the separate compatibility argument.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem measurable_planarGradient (f : (ℝ × ℝ) → ℝ) : Measurable (planarGradient f) :=
  (measurable_fderiv_apply_const ℝ f (1, 0)).prodMk
    (measurable_fderiv_apply_const ℝ f (0, 1))

theorem integral_coordinateWedges_eq_sum
    {μ : Measure (ℝ × ℝ)} {n : ℕ} (u : Fin n → (ℝ × ℝ) → ℝ)
    (hu : ∀ i, MemLp (planarGradient (u i)) 2 μ) :
    (∫ z, coordinateWedges (natCoordinateFamily u) n z ∂μ) =
      ∑ p : UpperPairs n, ∫ z, |planarWedge (planarGradient (u (upperPair p).1) z)
        (planarGradient (u (upperPair p).2) z)| ∂μ := by
  have hi (p : UpperPairs n) :=
    integrable_abs_planarWedge_of_memLp (hu (upperPair p).1) (hu (upperPair p).2)
  calc
    _ = ∫ z, ∑ p : UpperPairs n, |planarWedge
        (planarGradient (u (upperPair p).1) z) (planarGradient (u (upperPair p).2) z)| ∂μ :=
      integral_congr_ae (Eventually.of_forall (coordinateWedges_eq_sum_upperPairs u))
    _ = _ := integral_finsetSum _ (fun p _ => hi p)

/-- Finite-energy smooth coordinates produce an actual core, cutoff,
spacing, shifts, terminal-count estimate and frequently small modified
wedge cost. No small-tail or cutoff-integrability premise is left over. -/
theorem exists_core_cutoff_and_grid
    {G K₀ : Set (ℝ × ℝ)} (hG : IsOpen G) (hK₀ : IsCompact K₀) (hK₀G : K₀ ⊆ G)
    {n : ℕ} (u : Fin n → (ℝ × ℝ) → ℝ) (huM : ∀ i, Measurable (u i))
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) G)
    (hu2 : ∀ i, MemLp (planarGradient (u i)) 2 (volume.restrict G))
    {S : Type*} [Countable S] (F : Set S) (hF : F.Finite) (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2))
    (P : ℕ → (Fin n → ℝ) → Prop)
    (hP : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, P N θ)
    {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ (K L : Set (ℝ × ℝ)) (χ : (ℝ × ℝ) → ℝ) (N : ℕ) (θ : Fin n → ℝ),
      IsCompact K ∧ K₀ ⊆ interior K ∧ K ⊆ G ∧
      IsCompact L ∧ L ⊆ G ∧ ContDiff ℝ ∞ χ ∧
      (∀ z, χ z ∈ Icc 0 1) ∧ (∀ᶠ z in 𝓝ˢ K, χ z = 0) ∧ (∀ z ∉ L, χ z = 1) ∧
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
  obtain ⟨K, hK, hK₀K, hKG, hcost⟩ :=
    exists_compact_core_small_wedges hG hK₀ hK₀G u hu2 (ε := η / 4)
      (div_pos hη (by norm_num))
  obtain ⟨χ, L, hχ, hL, hLG, hχrange, hχzero, hχone, hχ2⟩ := exists_core_cutoff hG hK hKG
  have hu2' (i : Fin n) : MemLp (planarGradient (u i)) 2 (volume.restrict (G \ K)) :=
    MemLp.mono_measure (Measure.restrict_mono_set volume sdiff_subset) (hu2 i)
  have hχ2' : MemLp (planarGradient χ) 2 (volume.restrict (G \ K)) :=
    MemLp.mono_measure Measure.restrict_le_self hχ2
  have hd : ∀ᵐ z ∂volume.restrict (G \ K),
      DifferentiableAt ℝ χ z ∧ ∀ i, DifferentiableAt ℝ (u i) z := by
    filter_upwards [ae_restrict_mem (hG.measurableSet.diff hK.isClosed.measurableSet)] with z hz
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
  exact ⟨K, L, χ, N, θ, hK, hK₀K, hKG, hL, hLG, hχ, hχrange, hχzero, hχone,
    hN, hPθ, hfin, hcard, hint, hgood⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
