import OAI.NumberTheory.DukePrimeDegree.Geometry.GoodSetFiberCorrection
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Algebra.Monoid

namespace OAI

/-!
# Fixed compact patches for varying stabilizer corrections

The pair correction tends to identity. Two fixed compact patches then
suffice: small corrections send the smaller patch into the larger one.
Positive Haar mass and finite larger-patch mass give the two constants
used in the fiber-good-set estimate.
-/

noncomputable section
open MeasureTheory Set Filter
open MeasureTheory.Measure
open scoped Topology Pointwise ENNReal

namespace DukePrimeDegree

theorem exists_compact_correction_patches
    {H : Type*} [Group H] [TopologicalSpace H] [ContinuousMul H]
    [WeaklyLocallyCompactSpace H] [MeasurableSpace H] [OpensMeasurableSpace H]
    (ρ : Measure H) [IsOpenPosMeasure ρ] [IsFiniteMeasureOnCompacts ρ] :
    ∃ W K₀ K₁ : Set H, IsOpen W ∧ 1 ∈ W ∧
      IsCompact K₀ ∧ IsCompact K₁ ∧ K₀ ⊆ K₁ ∧
      0 < ρ K₀ ∧ ρ K₁ < ⊤ ∧
      ∀ b ∈ W, ∀ h ∈ K₀, b * h ∈ K₁ := by
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds (1 : H)
  have h1 : (1 : H) ∈ K := mem_of_mem_nhds hK
  refine ⟨interior K, K, K * K, isOpen_interior,
    mem_interior_iff_mem_nhds.mpr hK, hKc, hKc.mul hKc, ?_,
    measure_pos_of_mem_nhds ρ hK, (hKc.mul hKc).measure_lt_top, ?_⟩
  · intro h hh
    exact ⟨1, h1, h, hh, one_mul h⟩
  · intro b hb h hh
    exact ⟨b, interior_subset hb, h, hh, rfl⟩

/-- A fixed patch works eventually for an arbitrary sequence of
identity-converging corrections. No rate is compared with the orbit
window length. -/
theorem eventually_maps_compact_correction_patch
    {H I : Type*} [Group H] [TopologicalSpace H]
    {l : Filter I} (b : I → H) (hb : Tendsto b l (𝓝 1))
    (W K₀ K₁ : Set H) (hW : IsOpen W) (h1 : 1 ∈ W)
    (hpatch : ∀ a ∈ W, ∀ h ∈ K₀, a * h ∈ K₁) :
    ∀ᶠ i in l, ∀ h ∈ K₀, b i * h ∈ K₁ := by
  exact (hb.eventually (hW.mem_nhds h1)).mono fun i hi => hpatch (b i) hi

end DukePrimeDegree

end

end OAI
