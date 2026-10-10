import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory MeasureTheory.Measure Filter
open scoped Topology ENNReal

namespace CylinderCovering.OpenEnlargement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem measureReal_interior_homothety (μ : Measure E) [IsAddHaarMeasure μ]
    {K : Set E} (hK : Convex ℝ K) (c : E) (r : ℝ) :
    μ.real (interior (AffineMap.homothety c r '' K)) =
      |r ^ Module.finrank ℝ E| * μ.real K := by
  have hconv : Convex ℝ (AffineMap.homothety c r '' K) := hK.affine_image _
  have hae : interior (AffineMap.homothety c r '' K) =ᵐ[μ]
      AffineMap.homothety c r '' K := by
    apply measure_symmDiff_eq_zero_iff.mp
    exact measure_mono_null (by
      intro x hx
      simp only [Set.mem_symmDiff] at hx
      rcases hx with hx | hx
      · exact False.elim (hx.2 (interior_subset hx.1))
      · exact ⟨subset_closure hx.1, hx.2⟩) (hconv.addHaar_frontier μ)
  rw [measureReal_congr hae, Measure.real, addHaar_image_homothety,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

theorem exists_homothetic_open_enlargement (μ : Measure E) [IsAddHaarMeasure μ]
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    {c : E} (hc : c ∈ interior K) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 1 < r ∧
      K ⊆ interior (AffineMap.homothety c r '' K) ∧
      IsOpen (interior (AffineMap.homothety c r '' K)) ∧
      Bornology.IsBounded (interior (AffineMap.homothety c r '' K)) ∧
      MeasurableSet (interior (AffineMap.homothety c r '' K)) ∧
      μ.real (interior (AffineMap.homothety c r '' K)) < μ.real K + ε := by
  have hcont : Continuous (fun r : ℝ => |r ^ Module.finrank ℝ E| * μ.real K) := by
    fun_prop
  have hnear : ∀ᶠ r : ℝ in 𝓝 (1 : ℝ),
      |r ^ Module.finrank ℝ E| * μ.real K < μ.real K + ε :=
    hcont.continuousAt.eventually (gt_mem_nhds (by simpa using hε))
  have hgt : ∀ᶠ r : ℝ in 𝓝[>] (1 : ℝ), 1 < r := self_mem_nhdsWithin
  have hright : ∀ᶠ r : ℝ in 𝓝[>] (1 : ℝ),
      1 < r ∧ |r ^ Module.finrank ℝ E| * μ.real K < μ.real K + ε :=
    hgt.and (hnear.filter_mono nhdsWithin_le_nhds)
  obtain ⟨r, hr, harea⟩ := hright.exists
  refine ⟨r, hr, hconv.subset_interior_image_homothety_of_one_lt hc r hr,
    isOpen_interior, ?_, isOpen_interior.measurableSet, ?_⟩
  · exact (hK.image (AffineMap.homothety c r).continuous_of_finiteDimensional).isBounded.subset
      interior_subset
  · rwa [measureReal_interior_homothety μ hconv c r]

end CylinderCovering.OpenEnlargement

end

end OAI
