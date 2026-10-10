import OAI.Geometry.SurfaceImmersion.Correction.BundleSmoothingTransition

namespace OAI

/-! Weighted atlas bounds for section restoration. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {E : M → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable (e : A.centers → Trivialization F (TotalSpace.proj : TotalSpace F E → M))
  [∀ i, MemTrivializationAtlas (e i)]

def BundleWeightedBound (s : ℝ) (m : ℕ) (C : ℝ) (u : ∀ x, E x) : Prop :=
  ∀ i : A.centers, WeightedBound univ s m C (A.bundleLocalize e i u)

lemma bundleLocalize_sum {ι : Type*} (b : Finset ι) (i : A.centers) (u : ι → ∀ x, E x) :
    A.bundleLocalize e i (fun x => ∑ k ∈ b, u k x) =
      fun x => ∑ k ∈ b, A.bundleLocalize e i (u k) x := by
  funext x
  by_cases hx : x ∈ (chart (i : M)).target <;>
    simp [bundleLocalize, localize, bundleComponent, hx, Finset.smul_sum]

variable [ContMDiffVectorBundle ∞ F E planeModel] [CompactSpace M]
variable (hdomain : ∀ i : A.centers, (chart (i : M)).source ⊆ (e i).baseSet)
include hdomain

/-- A finite family of local sections can be restored with fixed weighted
bounds at every order. -/
theorem bundle_restoration_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : A.centers → Base → F) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (h i)) →
      (∀ i, WeightedBound univ s m C (h i)) →
      A.BundleWeightedBound e s m (D * C)
        (fun x => ∑ i : A.centers, A.bundleRestore e i (h i) x) := by
  classical
  choose D hD hbound using fun i j : A.centers => A.bundle_pair_weighted_bound e hdomain i j m
  refine ⟨∑ i : A.centers, ∑ j : A.centers, D i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)), ?_⟩
  intro h s C hs hs1 hC hh hb i
  have hf (j : A.centers) : ContDiff ℝ ∞
      (A.bundleLocalize e i (A.bundleRestore e j (h j))) :=
    A.bundleLocalize_smooth e hdomain i (A.bundleRestore_smooth e hdomain j (hh j))
  have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
    (Finset.univ : Finset A.centers) (fun j => D i j * C)
    (fun j => A.bundleLocalize e i (A.bundleRestore e j (h j)))
    (fun j _ => (hf j).contDiffOn)
    (fun j _ => hbound i j (h j) s C hs hs1 hC (hh j) (hb j))
  rw [A.bundleLocalize_sum]
  apply hsum.mono_const
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ hC
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg (fun j _ => hD k j)) (Finset.mem_univ i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
