import Mathlib

namespace OAI

/-!
# Whitney immersion and Sard regular-value statements for surfaces

The compact surface specialization of Whitney's immersion theorem and
the equal-dimensional surface case of Sard's theorem provide the
initial immersion and the regular parameters of the construction.
-/

noncomputable section

namespace ClosedSurfaceR4.PublishedInputs

open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)

/-- Whitney, *The Singularities of a Smooth n-Manifold in (2n-1)-Space*,
Ann. Math. 45 (1944), Theorem 8, p.274, specialized to compact surfaces:
existence of a C1 immersion into Euclidean three-space. -/
def WhitneySurfaceInput (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace Plane M] [IsManifold 𝓘(ℝ, Plane) ∞ M] : Prop :=
  ∃ f : M → ThreeSpace, ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ, ThreeSpace) 1 f ∧
    ∀ x, Function.Injective (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, ThreeSpace) f x)

/-- Critical values of a map between two-dimensional coordinate spaces. -/
def criticalValues (f : Plane → Plane) : Set Plane :=
  f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}

/-- Sard, *The measure of the critical values of differentiable maps*,
Bull. AMS 48 (1942), Theorem 4.1, p.885: the smooth equal-dimensional
surface case in coordinates. This is the sole critical-value input needed
for the manuscript's countable coordinate charts. -/
def SardSurfaceInput : Prop :=
  ∀ f : Plane → Plane, ContDiff ℝ ∞ f → volume (criticalValues f) = 0

/-- The critical values of a smooth map between planes have zero volume. -/
theorem sardSurfaceInput : SardSurfaceInput := by
  intro f hf
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fun x => fderiv ℝ f x)
  · intro x _
    exact (hf.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    change ¬ Function.Surjective (fderiv ℝ f x) at hx
    change LinearMap.det (fderiv ℝ f x).toLinearMap = 0
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq, LinearMap.ker_eq_bot]
    exact fun hinj => hx (LinearMap.injective_iff_surjective.mp hinj)

lemma not_mem_criticalValues_iff (f : Plane → Plane) (y : Plane) :
    y ∉ criticalValues f ↔ ∀ x, f x = y → Function.Surjective (fderiv ℝ f x) := by
  simp only [criticalValues, mem_image, mem_ofPred_eq, not_exists, not_and]
  constructor
  · intro h x hxy
    by_contra hn
    exact h x hn hxy
  · intro h x hn hxy
    exact hn (h x hxy)

/-- Countably many exceptional sets can be avoided densely. This is the
selection step used after applying Sard in the coordinate charts of a
parameter projection. -/
theorem dense_simultaneous_regular_values (hSard : SardSurfaceInput)
    {ι : Type*} [Countable ι] (f : ι → Plane → Plane)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    Dense {y | ∀ i x, f i x = y → Function.Surjective (fderiv ℝ (f i) x)} := by
  have hnull : volume (⋃ i, criticalValues (f i)) = 0 :=
    measure_iUnion_null (fun i => hSard (f i) (hf i))
  have hae : ∀ᵐ y ∂volume, y ∉ ⋃ i, criticalValues (f i) := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using hnull
  have hd := Measure.dense_of_ae hae
  simpa only [mem_iUnion, not_exists, not_mem_criticalValues_iff] using hd

/-- Countably many smooth plane maps have simultaneous regular values in
every nonempty open parameter set. -/
theorem exists_simultaneous_regular_value (hSard : SardSurfaceInput)
    {ι : Type*} [Countable ι] (f : ι → Plane → Plane)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (U : Set Plane)
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ y ∈ U, ∀ i x, f i x = y → Function.Surjective (fderiv ℝ (f i) x) := by
  obtain ⟨y, hy, hyU⟩ := (dense_simultaneous_regular_values hSard f hf).inter_open_nonempty U hU hne
  exact ⟨y, hy, hyU⟩

/-- Simultaneous regular-value selection from the fixed-dimensional Sard theorem. -/
theorem exists_simultaneous_regular_value_unconditional
    {ι : Type*} [Countable ι] (f : ι → Plane → Plane)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (U : Set Plane)
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ y ∈ U, ∀ i x, f i x = y → Function.Surjective (fderiv ℝ (f i) x) :=
  exists_simultaneous_regular_value sardSurfaceInput f hf U hU hne

end ClosedSurfaceR4.PublishedInputs

end

end OAI
