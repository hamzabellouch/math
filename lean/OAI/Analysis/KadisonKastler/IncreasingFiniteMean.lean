import OAI.Analysis.KadisonKastler.FiniteGroupAverage
import OAI.Analysis.KadisonKastler.InvariantOperatorMean

namespace OAI

/-! # Invariant means from increasing finite subgroups

Normalized counting averages have a simultaneous scalar ultralimit. Every
fixed group translation preserves all sufficiently late averages.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators BoundedContinuousFunction

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

private theorem finiteAverage_positive [Fintype G] (f : G →ᵇ ℂ)
    (hf : ∀ g, (f g).im = 0 ∧ 0 ≤ (f g).re) :
    (finiteGroupAverage f).im = 0 ∧ 0 ≤ (finiteGroupAverage f).re := by
  have hi : (∑ g, f g).im = 0 := by
    change Complex.imLm (∑ g, f g) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero (fun g _ => (hf g).1)
  have hr : 0 ≤ (∑ g, f g).re := by
    change 0 ≤ Complex.reLm (∑ g, f g)
    rw [map_sum]
    exact Finset.sum_nonneg (fun g _ => (hf g).2)
  rw [finiteGroupAverage_apply]
  simp only [Complex.real_smul, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, hi, mul_zero, zero_mul, add_zero, sub_zero]
  exact ⟨trivial, mul_nonneg (by positivity) hr⟩

private def subgroupRestriction (K : Subgroup G) : (G →ᵇ ℂ) →L[ℂ] (K →ᵇ ℂ) :=
  BoundedContinuousFunction.compContinuousCLM ℂ ℂ ⟨Subtype.val, continuous_subtype_val⟩

private def finiteSubgroupFunctional (K : Subgroup G) [Finite K] : (G →ᵇ ℂ) →L[ℂ] ℂ := by
  let := Fintype.ofFinite K
  exact finiteGroupAverage.comp (subgroupRestriction K)

private theorem finiteSubgroupFunctional_apply (K : Subgroup G) [Finite K] (f : G →ᵇ ℂ) :
    finiteSubgroupFunctional K f =
      let := Fintype.ofFinite K
      finiteGroupAverage (subgroupRestriction K f) := rfl

private theorem finiteSubgroupFunctional_norm (K : Subgroup G) [Finite K] (f : G →ᵇ ℂ) :
    ‖finiteSubgroupFunctional K f‖ ≤ ‖f‖ := by
  let := Fintype.ofFinite K
  change ‖finiteGroupAverage (subgroupRestriction K f)‖ ≤ ‖f‖
  exact (finiteGroupAverage_norm_le _).trans
    (BoundedContinuousFunction.norm_compContinuous_le f _)

private theorem finiteSubgroupFunctional_const (K : Subgroup G) [Finite K] (c : ℂ) :
    finiteSubgroupFunctional K (BoundedContinuousFunction.const G c) = c := by
  let := Fintype.ofFinite K
  change finiteGroupAverage (BoundedContinuousFunction.const K c) = c
  exact finiteGroupAverage_const c

private theorem finiteSubgroupFunctional_positive (K : Subgroup G) [Finite K]
    (f : G →ᵇ ℂ) (hf : ∀ g, (f g).im = 0 ∧ 0 ≤ (f g).re) :
    (finiteSubgroupFunctional K f).im = 0 ∧ 0 ≤ (finiteSubgroupFunctional K f).re := by
  let := Fintype.ofFinite K
  exact finiteAverage_positive (subgroupRestriction K f) (fun g : K => hf g.val)

private theorem finiteSubgroupFunctional_invariant [DiscreteTopology G] (K : Subgroup G) [Finite K]
    (g : G) (hg : g ∈ K) (f : G →ᵇ ℂ) :
    finiteSubgroupFunctional K (scalarMeanTranslate g f) = finiteSubgroupFunctional K f := by
  let := Fintype.ofFinite K
  let k : K := ⟨g, hg⟩
  have he : subgroupRestriction K (scalarMeanTranslate g f) =
      boundaryTranslate (1 : K →* (ℂ ≃⋆ₐ[ℂ] ℂ)) k (subgroupRestriction K f) := by
    ext t
    rfl
  change finiteGroupAverage (subgroupRestriction K (scalarMeanTranslate g f)) =
    finiteGroupAverage (subgroupRestriction K f)
  rw [he, finiteGroupAverage_translate]

variable (K : ℕ → Subgroup G) [∀ n, Finite (K n)]

private def finiteChainUltrafilter : Ultrafilter ℕ := Ultrafilter.of atTop

private theorem finiteChainUltrafilter_le :
    (finiteChainUltrafilter : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop

private theorem exists_finiteChainMeanValue (f : G →ᵇ ℂ) :
    ∃ z : ℂ, ‖z‖ ≤ ‖f‖ ∧ Tendsto (fun n => finiteSubgroupFunctional (K n) f)
      (finiteChainUltrafilter : Filter ℕ) (𝓝 z) := by
  obtain ⟨z, hz, ht⟩ := (isCompact_closedBall (0 : ℂ) ‖f‖).ultrafilter_le_nhds
    (finiteChainUltrafilter.map (fun n : ℕ => finiteSubgroupFunctional (K n) f)) (by
      apply le_principal_iff.mpr
      change ∀ᶠ n in (finiteChainUltrafilter : Filter ℕ),
        finiteSubgroupFunctional (K n) f ∈ Metric.closedBall (0 : ℂ) ‖f‖
      exact Eventually.of_forall (fun n : ℕ => by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          finiteSubgroupFunctional_norm (K n) f))
  exact ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, ht⟩

private def finiteChainMeanValue (f : G →ᵇ ℂ) : ℂ :=
  Classical.choose (exists_finiteChainMeanValue K f)

private theorem finiteChainMeanValue_norm (f : G →ᵇ ℂ) :
    ‖finiteChainMeanValue K f‖ ≤ ‖f‖ :=
  (Classical.choose_spec (exists_finiteChainMeanValue K f)).1

private theorem finiteChainMeanValue_tendsto (f : G →ᵇ ℂ) :
    Tendsto (fun n => finiteSubgroupFunctional (K n) f)
      (finiteChainUltrafilter : Filter ℕ) (𝓝 (finiteChainMeanValue K f)) :=
  (Classical.choose_spec (exists_finiteChainMeanValue K f)).2

private theorem finiteChainMeanValue_add (f h : G →ᵇ ℂ) :
    finiteChainMeanValue K (f + h) = finiteChainMeanValue K f + finiteChainMeanValue K h := by
  apply tendsto_nhds_unique (finiteChainMeanValue_tendsto K (f + h))
  simpa only [map_add] using (finiteChainMeanValue_tendsto K f).add
    (finiteChainMeanValue_tendsto K h)

private theorem finiteChainMeanValue_smul (c : ℂ) (f : G →ᵇ ℂ) :
    finiteChainMeanValue K (c • f) = c • finiteChainMeanValue K f := by
  apply tendsto_nhds_unique (finiteChainMeanValue_tendsto K (c • f))
  simpa only [map_smul] using (finiteChainMeanValue_tendsto K f).const_smul c

private theorem finiteChainMeanValue_const (c : ℂ) :
    finiteChainMeanValue K (BoundedContinuousFunction.const G c) = c := by
  apply tendsto_nhds_unique (finiteChainMeanValue_tendsto K _)
  simpa only [finiteSubgroupFunctional_const] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) (finiteChainUltrafilter : Filter ℕ) (𝓝 c))

private theorem finiteChainMeanValue_positive (f : G →ᵇ ℂ)
    (hf : ∀ g, (f g).im = 0 ∧ 0 ≤ (f g).re) :
    (finiteChainMeanValue K f).im = 0 ∧ 0 ≤ (finiteChainMeanValue K f).re := by
  constructor
  · apply tendsto_nhds_unique ((Complex.continuous_im.tendsto _).comp
      (finiteChainMeanValue_tendsto K f))
    have hi : (fun n : ℕ => (finiteSubgroupFunctional (K n) f).im) = fun _ => 0 :=
      funext (fun n => (finiteSubgroupFunctional_positive (K n) f hf).1)
    change Tendsto (fun n => (finiteSubgroupFunctional (K n) f).im)
      (finiteChainUltrafilter : Filter ℕ) (𝓝 0)
    rw [hi]
    exact tendsto_const_nhds
  · exact ge_of_tendsto ((Complex.continuous_re.tendsto _).comp
      (finiteChainMeanValue_tendsto K f))
      (Eventually.of_forall (fun n => (finiteSubgroupFunctional_positive (K n) f hf).2))

private theorem finiteChainMeanValue_invariant [DiscreteTopology G] (hmono : Monotone K)
    (hcover : ∀ g : G, ∃ n, g ∈ K n) (g : G) (f : G →ᵇ ℂ) :
    finiteChainMeanValue K (scalarMeanTranslate g f) = finiteChainMeanValue K f := by
  obtain ⟨n, hn⟩ := hcover g
  apply tendsto_nhds_unique (finiteChainMeanValue_tendsto K _)
  apply (finiteChainMeanValue_tendsto K f).congr'
  apply Filter.Eventually.filter_mono finiteChainUltrafilter_le
  filter_upwards [eventually_ge_atTop n] with k hk
  exact (finiteSubgroupFunctional_invariant (K k) g (hmono hk hn) f).symm

/-- The scalar invariant mean for a group exhausted by an increasing sequence
of finite subgroups. -/
def increasingFiniteScalarInvariantMean [DiscreteTopology G] (hmono : Monotone K)
    (hcover : ∀ g : G, ∃ n, g ∈ K n) : ScalarInvariantMean G where
  toCLM := LinearMap.mkContinuous
    { toFun := finiteChainMeanValue K
      map_add' := finiteChainMeanValue_add K
      map_smul' := finiteChainMeanValue_smul K }
    1 (fun f => by
      change ‖finiteChainMeanValue K f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using finiteChainMeanValue_norm K f)
  map_const_one := finiteChainMeanValue_const K 1
  norm_le := finiteChainMeanValue_norm K
  positive := finiteChainMeanValue_positive K
  invariant := finiteChainMeanValue_invariant K hmono hcover

end

end KadisonKastler

end OAI
