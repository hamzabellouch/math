import OAI.Analysis.CircleDomains.Sobolev.CircleStaircaseGradient
import OAI.Analysis.CircleDomains.Rigidity.MaskedCircleMetric

namespace OAI

/-!
# Actual random wedge cost for circle coordinates

The random covectors are exactly the intrinsic differentials of the
modified circle maps. Fixed-width integrability follows from the
original L² differentials and the cutoff, just as in the real case.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem measurable_circleRepresentative : Measurable circleRepresentative := by
  apply measurable_of_continuousOn_compl_singleton (0 : UnitAddCircle)
  intro t ht
  exact (continuous_subtype_val.continuousAt.comp
    (AddCircle.continuousAt_equivIco 1 0 ht)).continuousWithinAt

def circleCutoffFamily {n : ℕ} (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (χ : (ℝ × ℝ) → ℝ) (N : ℕ) (δ : ℝ) (θ : Fin n → ℝ) :
    Fin n → (ℝ × ℝ) → UnitAddCircle :=
  fun i => circleCutoff (f i) χ (shiftedStaircase (reciprocalGridStep N) δ (θ i))

def circleWedges {n : ℕ} (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (z : ℝ × ℝ) : ℝ :=
  fieldWedges (natCovectorFamily (fun i => circleGradient (f i))) n z

theorem cutoff_circle_wedges_integrable_and_eq_cost
    {n : ℕ} {G : Set (ℝ × ℝ)} (hG : IsOpen G)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (χ : (ℝ × ℝ) → ℝ)
    (hf : ∀ i, SmoothCircleOn (f i) G) (hmf : ∀ i, Measurable (f i))
    (hdf : ∀ i, Measurable (circleGradient (f i)))
    (hf2 : ∀ i, MemLp (circleGradient (f i)) 2 (volume.restrict G))
    (hχ : ContDiff ℝ ∞ χ) (hdχ : Measurable (planarGradient χ))
    (hχ2 : MemLp (planarGradient χ) 2 (volume.restrict G))
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4)
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1) (θ : Fin n → ℝ) :
    IntegrableOn (circleWedges (circleCutoffFamily f χ N δ θ)) G ∧
      (∫ z in G, circleWedges (circleCutoffFamily f χ N δ θ) z) =
        staircaseWedgeCost (volume.restrict G) upperPair (fun i => circleGradient (f i))
          (planarGradient χ) (fun i z => circleRepresentative (f i z))
          χ (reciprocalGridStep N) δ θ := by
  let d : UpperPairs n → (ℝ × ℝ) → ℝ := fun p z => |planarWedge
    (staircaseCovector (reciprocalGridStep N) δ (χ z) (θ (upperPair p).1)
      (circleRepresentative (f (upperPair p).1 z))
      (circleGradient (f (upperPair p).1) z) (planarGradient χ z))
    (staircaseCovector (reciprocalGridStep N) δ (χ z) (θ (upperPair p).2)
      (circleRepresentative (f (upperPair p).2 z))
      (circleGradient (f (upperPair p).2) z) (planarGradient χ z))|
  have hi (p : UpperPairs n) : Integrable (d p) (volume.restrict G) :=
    integrable_staircase_pair_at_shifts_of_memLp _ _ _ _ _ _
      (hdf _) (hdf _) hdχ
      (measurable_circleRepresentative.comp (hmf _))
      (measurable_circleRepresentative.comp (hmf _)) hχ.continuous.measurable
      (hf2 _) (hf2 _) hχ2 (reciprocalGridStep_pos N) hδ hδh hχ0 hχ1 _ _
  have hformula (z : ℝ × ℝ) (hz : z ∈ G) (i : Fin n) :
      circleGradient (circleCutoffFamily f χ N δ θ i) z =
        staircaseCovector (reciprocalGridStep N) δ (χ z) (θ i)
          (circleRepresentative (f i z)) (circleGradient (f i) z) (planarGradient χ z) := by
    exact circleGradient_reciprocal_cutoff
      ((hf i).continuousOn.continuousAt (hG.mem_nhds hz))
      (hf i z hz _ (circleCut_ne (f i) z)) hχ.contDiffAt
      (Filter.Eventually.of_forall (coe_circleBranch (f i) (circleCut (f i) z)))
      N hδ hδh (θ i)
  have heq : circleWedges (circleCutoffFamily f χ N δ θ) =ᵐ[volume.restrict G]
      fun z => ∑ p, d p z := by
    filter_upwards [ae_restrict_mem hG.measurableSet] with z hz
    rw [circleWedges, fieldWedges_eq_sum_upperPairs]
    apply Finset.sum_congr rfl
    intro p _
    rw [hformula z hz _, hformula z hz _]
  refine ⟨(integrable_finsetSum _ (fun p _ => hi p)).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  exact integral_finsetSum _ (fun p _ => hi p)

/-- The actual reciprocal grid selection applies to periodic coordinates
with their intrinsic L² differentials and bounded circle representatives. -/
theorem exists_grid_for_actual_circle_wedges
    {n : ℕ} {S : Type*} [Countable S] {G : Set (ℝ × ℝ)} (hG : IsOpen G)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle) (χ : (ℝ × ℝ) → ℝ)
    (hf : ∀ i, SmoothCircleOn (f i) G) (hmf : ∀ i, Measurable (f i))
    (hdf : ∀ i, Measurable (circleGradient (f i)))
    (hf2 : ∀ i, MemLp (circleGradient (f i)) 2 (volume.restrict G))
    (hχ : ContDiff ℝ ∞ χ) (hdχ : Measurable (planarGradient χ))
    (hχ2 : MemLp (planarGradient χ) 2 (volume.restrict G))
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (F : Set S) (hF : F.Finite) (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2))
    (P : ℕ → (Fin n → ℝ) → Prop)
    (hP : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, P N θ)
    {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ)
    (hsmall : (∑ p : UpperPairs n, ∫ z in G,
      |planarWedge (circleGradient (f (upperPair p).1) z)
        (circleGradient (f (upperPair p).2) z)|) < η / 4) :
    ∃ (N : ℕ) (θ : Fin n → ℝ), reciprocalGridStep N < ρ ∧ P N θ ∧
      (gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).Finite ∧
      reciprocalGridStep N *
        Real.sqrt ((gridTerminalIndices F (reciprocalGridStep N) upperPair a b θ).ncard : ℝ) < η ∧
      (∀ k, IntegrableOn (circleWedges (circleCutoffFamily f χ N
        (staircaseWidth (reciprocalGridStep N) k) θ)) G) ∧
      ∃ᶠ k in atTop, (∫ z in G, circleWedges (circleCutoffFamily f χ N
        (staircaseWidth (reciprocalGridStep N) k) θ) z) < η := by
  obtain ⟨N, θ, hN, hPθ, hfin, hcard, hgood⟩ :=
    exists_grid_for_actual_wedge_cost upperPair upperPair_ne
      (fun i => circleGradient (f i)) (planarGradient χ)
      (fun i z => circleRepresentative (f i z)) χ hdf hdχ
      (fun i => measurable_circleRepresentative.comp (hmf i)) hχ.continuous.measurable
      hf2 hχ2 hχ0 hχ1 F hF a b hwidth hwidth2 P hP hη hρ hsmall
  have hcost (k : ℕ) := cutoff_circle_wedges_integrable_and_eq_cost hG f χ hf hmf hdf
    hf2 hχ hdχ hχ2 N (staircaseWidth_pos (reciprocalGridStep_pos N) k)
      (staircaseWidth_lt (reciprocalGridStep_pos N) k) hχ0 hχ1 θ
  refine ⟨N, θ, hN, hPθ, hfin, hcard, fun k => (hcost k).1, ?_⟩
  exact hgood.mono (fun k hk => (hcost k).2.trans_lt hk)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
