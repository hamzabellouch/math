import OAI.Analysis.CircleDomains.Rigidity.MaskedGridSelection
import OAI.Analysis.CircleDomains.Modulus.CircleWedgeCost

namespace OAI

/-!
# Actual masked circle cost away from the retained core

Mask boundaries lie inside the core. On its complement every active
mask is locally present, so the circle cutoff formula holds there.
This identifies the masked random cost with the actual spatial wedge
sum and proves integrability from each coordinate's own masked L² norm.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem masked_circle_cutoff_wedges_integrable_and_eq_cost
    {n : ℕ} {G K : Set (ℝ × ℝ)} (hG : IsOpen G) (hK : MeasurableSet K)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, MeasurableSet (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ K)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (χ : (ℝ × ℝ) → ℝ)
    (hf : ∀ i, SmoothCircleOn (f i) (G ∩ interior (M i)))
    (hmf : ∀ i, Measurable (f i)) (hdf : ∀ i, Measurable (circleGradient (f i)))
    (hf2 : ∀ i, MemLp (circleGradient (f i)) 2
      ((volume.restrict (G \ K)).restrict (M i)))
    (hχ : ContDiff ℝ ∞ χ) (hdχ : Measurable (planarGradient χ))
    (hχ2 : MemLp (planarGradient χ) 2 (volume.restrict (G \ K)))
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1) (θ : Fin n → ℝ) :
    IntegrableOn (maskedCircleWedges M (circleCutoffFamily f χ N δ θ)) (G \ K) ∧
      (∫ z in G \ K, maskedCircleWedges M (circleCutoffFamily f χ N δ θ) z) =
        maskedStaircaseCost (volume.restrict (G \ K)) upperPair M
          (fun i => circleGradient (f i)) (planarGradient χ)
          (fun i z => circleRepresentative (f i z)) χ (reciprocalGridStep N) δ θ := by
  let μ := volume.restrict (G \ K)
  let d : UpperPairs n → (ℝ × ℝ) → ℝ := fun p z => |planarWedge
    (staircaseCovector (reciprocalGridStep N) δ (χ z) (θ (upperPair p).1)
      (circleRepresentative (f (upperPair p).1 z)) (circleGradient (f (upperPair p).1) z)
      (planarGradient χ z))
    (staircaseCovector (reciprocalGridStep N) δ (χ z) (θ (upperPair p).2)
      (circleRepresentative (f (upperPair p).2 z)) (circleGradient (f (upperPair p).2) z)
      (planarGradient χ z))|
  let e : UpperPairs n → (ℝ × ℝ) → ℝ := fun p z => |planarWedge
    ((M (upperPair p).1).indicator (circleGradient (circleCutoffFamily f χ N δ θ (upperPair p).1)) z)
    ((M (upperPair p).2).indicator (circleGradient (circleCutoffFamily f χ N δ θ (upperPair p).2)) z)|
  have hformula (z : ℝ × ℝ) (hz : z ∈ G \ K) (i : Fin n) (hzM : z ∈ M i) :
      circleGradient (circleCutoffFamily f χ N δ θ i) z =
        staircaseCovector (reciprocalGridStep N) δ (χ z) (θ i)
          (circleRepresentative (f i z)) (circleGradient (f i) z) (planarGradient χ z) := by
    have hzi : z ∈ interior (M i) :=
      (mem_interior_iff_notMem_frontier hzM).mpr (fun hb => hz.2 (hboundary i hb))
    exact circleGradient_reciprocal_cutoff
      ((hf i).continuousOn.continuousAt ((hG.inter isOpen_interior).mem_nhds ⟨hz.1, hzi⟩))
      (hf i z ⟨hz.1, hzi⟩ _ (circleCut_ne (f i) z)) hχ.contDiffAt
      (Filter.Eventually.of_forall (coe_circleBranch (f i) (circleCut (f i) z)))
      N hδ hδh (θ i)
  have heq (p : UpperPairs n) : e p =ᵐ[μ] (M (upperPair p).1 ∩ M (upperPair p).2).indicator (d p) := by
    filter_upwards [ae_restrict_mem (hG.measurableSet.diff hK)] with z hz
    dsimp only [e]
    rw [abs_wedge_indicators]
    by_cases hm : z ∈ M (upperPair p).1 ∩ M (upperPair p).2
    · simp only [indicator_of_mem hm]
      rw [hformula z hz _ hm.1, hformula z hz _ hm.2]
    · simp only [indicator_of_notMem hm]
  have hi (p : UpperPairs n) : Integrable (d p)
      (μ.restrict (M (upperPair p).1 ∩ M (upperPair p).2)) := by
    apply integrable_staircase_pair_at_shifts_of_memLp _ _ _ _ _ _
      (hdf _) (hdf _) hdχ (measurable_circleRepresentative.comp (hmf _))
      (measurable_circleRepresentative.comp (hmf _)) hχ.continuous.measurable
      ((hf2 _).mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
      ((hf2 _).mono_measure (Measure.restrict_mono inter_subset_right le_rfl))
      (hχ2.mono_measure Measure.restrict_le_self)
      (reciprocalGridStep_pos N) hδ hδh hχ0 hχ1
  have hei (p : UpperPairs n) : Integrable (e p) μ :=
    ((integrable_indicator_iff ((hM _).inter (hM _))).2 (hi p)).congr (heq p).symm
  refine ⟨integrable_finsetSum _ (fun p _ => hei p), ?_⟩
  change (∫ z, ∑ p, e p z ∂μ) = ∑ p, ∫ z, d p z ∂μ.restrict (M (upperPair p).1 ∩ M (upperPair p).2)
  rw [integral_finsetSum _ (fun p _ => hei p)]
  apply Finset.sum_congr rfl
  intro p _
  rw [integral_congr_ae (heq p), integral_indicator ((hM _).inter (hM _))]

/-- Grid selection for the actual masked circle cutoff, with finite
terminal indices and an arbitrarily late good width. -/
theorem exists_grid_for_actual_masked_circle_wedges
    {n : ℕ} {S : Type*} [Countable S] {G K : Set (ℝ × ℝ)}
    (hG : IsOpen G) (hK : MeasurableSet K)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, MeasurableSet (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ K)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (χ : (ℝ × ℝ) → ℝ)
    (hf : ∀ i, SmoothCircleOn (f i) (G ∩ interior (M i)))
    (hmf : ∀ i, Measurable (f i)) (hdf : ∀ i, Measurable (circleGradient (f i)))
    (hf2 : ∀ i, MemLp (circleGradient (f i)) 2
      ((volume.restrict (G \ K)).restrict (M i)))
    (hχ : ContDiff ℝ ∞ χ) (hdχ : Measurable (planarGradient χ))
    (hχ2 : MemLp (planarGradient χ) 2 (volume.restrict (G \ K)))
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (F : Set S) (hF : F.Finite) (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2))
    (P : ℕ → (Fin n → ℝ) → Prop) (hP : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, P N θ)
    {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ)
    (hsmall : (∑ p : UpperPairs n, ∫ z in M (upperPair p).1 ∩ M (upperPair p).2,
      |planarWedge (circleGradient (f (upperPair p).1) z)
        (circleGradient (f (upperPair p).2) z)| ∂volume.restrict (G \ K)) < η / 4) :
    ∃ (N : ℕ) (θ : Fin n → ℝ), reciprocalGridStep N < ρ ∧ P N θ ∧
      (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).Finite ∧
      reciprocalGridStep N *
        Real.sqrt ((gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).ncard : ℝ) < η ∧
      (∀ k, IntegrableOn (maskedCircleWedges M (circleCutoffFamily f χ N
        (staircaseWidth (reciprocalGridStep N) k) θ)) (G \ K)) ∧
      ∃ᶠ k in atTop, (∫ z in G \ K, maskedCircleWedges M (circleCutoffFamily f χ N
        (staircaseWidth (reciprocalGridStep N) k) θ) z) < η := by
  obtain ⟨N, θ, hN, hPθ, hfin, hcard, hgood⟩ :=
    exists_grid_for_masked_wedge_cost upperPair upperPair_ne M
      (fun i => circleGradient (f i)) (planarGradient χ)
      (fun i z => circleRepresentative (f i z)) χ hdf hdχ
      (fun i => measurable_circleRepresentative.comp (hmf i)) hχ.continuous.measurable
      hf2 hχ2 hχ0 hχ1 F hF a b hwidth hwidth2 P hP hη hρ hsmall
  have hcost (k : ℕ) := masked_circle_cutoff_wedges_integrable_and_eq_cost hG hK M hM hboundary
    f χ hf hmf hdf hf2 hχ hdχ hχ2 N (staircaseWidth_pos (reciprocalGridStep_pos N) k)
      (staircaseWidth_lt (reciprocalGridStep_pos N) k) hχ0 hχ1 θ
  refine ⟨N, θ, hN, hPθ, hfin, hcard, fun k => (hcost k).1, ?_⟩
  exact hgood.mono (fun k hk => (hcost k).2.trans_lt hk)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
