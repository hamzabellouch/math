import OAI.Geometry.SurfaceImmersion.Correction.SmoothingTransition

namespace OAI

/-! Fixed-atlas weighted norms and bounds for the actual restoration operator. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsManifold planeModel ∞ M] in
lemma localize_sum {ι : Type*} (b : Finset ι) (p : M) (ψ : M → ℝ) (f : ι → M → V) :
    localize p ψ (∑ i ∈ b, f i) = fun x => ∑ i ∈ b, localize p ψ (f i) x := by
  funext x
  by_cases hx : x ∈ (chart p).target <;>
    simp [localize, hx, Finset.sum_apply, Finset.smul_sum]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- A fixed finite family of localized coordinate norms. -/
def WeightedBound (t : ℝ) (m : ℕ) (C : ℝ) (f : M → V) : Prop :=
  ∀ i : A.centers, WeightedEstimates.WeightedBound Set.univ t m C
    (localize (i : M) (A.weight i) f)

variable [CompactSpace M]

/-- Restoring finitely many coordinate functions is bounded in every fixed
weighted atlas norm, uniformly in the input and the scale. -/
theorem restoration_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : A.centers → Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (h i)) →
      (∀ i, WeightedEstimates.WeightedBound Set.univ s m C (h i)) →
      A.WeightedBound s m (D * C) (∑ i : A.centers, restore (i : M) (A.outer i) (h i)) := by
  classical
  choose D hD hbound using fun i j : A.centers => A.pair_weighted_bound (V := V) i j m
  refine ⟨∑ i : A.centers, ∑ j : A.centers, D i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)), ?_⟩
  intro h s C hs hs1 hC hh hb i
  have hf (j : A.centers) : ContDiff ℝ ∞
      (localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j))) :=
    localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j) (hh j))
  have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
    (Finset.univ : Finset A.centers) (fun j => D i j * C)
    (fun j => localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j)))
    (fun j _ => (hf j).contDiffOn)
    (fun j _ => hbound i j (h j) s C hs hs1 hC (hh j) (hb j))
  rw [localize_sum]
  apply hsum.mono_const
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ hC
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg (fun j _ => hD k j)) (Finset.mem_univ i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
