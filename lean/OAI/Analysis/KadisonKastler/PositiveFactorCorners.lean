import OAI.Analysis.KadisonKastler.FactorSpatialSplit
import OAI.Analysis.KadisonSimilarity.Representation.SpectralCutBounds

namespace OAI

/-! # Positive norms in faithful factor corners -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem cornerCompression_nonneg (E : Submodule ℂ H) [CompleteSpace E]
    (T : H →L[ℂ] H) (hT : 0 ≤ T) : 0 ≤ cornerCompression E T := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  simpa only [cornerCompression, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_assoc] using
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).orthogonalProjectionOnto_comp E

omit [CompleteSpace H] in
theorem cornerCompression_mono (E : Submodule ℂ H) [CompleteSpace E] :
    Monotone (cornerCompression E) := by
  intro S T h
  have hh := cornerCompression_nonneg E (T - S) (sub_nonneg.mpr h)
  rwa [map_sub, sub_nonneg] at hh

theorem norm_cornerCompression_of_factor (E : Submodule ℂ H) [CompleteSpace E]
    (M : VonNeumannAlgebra H) (hM : ScalarCenter M)
    (hE : E.starProjection ∈ M.commutant) (hE0 : E.starProjection ≠ 0)
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    ‖cornerCompression E a‖ = ‖a‖ := by
  exact NonUnitalStarAlgHom.norm_map (commutantReducingHom E M hE)
    (commutantReducingHom_injective E M hE hE0 (scalarCenter_commutant M hM)) ⟨a, ha⟩

theorem norm_add_nonneg_scalar [Nontrivial H] (a : H →L[ℂ] H) (ha : 0 ≤ a)
    (t : ℝ) (ht : 0 ≤ t) : ‖a + t • 1‖ = ‖a‖ + t := by
  apply le_antisymm
  · calc
      ‖a + t • 1‖ ≤ ‖a‖ + ‖t • (1 : H →L[ℂ] H)‖ := norm_add_le _ _
      _ = ‖a‖ + t := by rw [norm_smul, Real.norm_of_nonneg ht, norm_one, mul_one]
  · have hs : ‖a‖ + t ∈ spectrum ℝ (algebraMap ℝ (H →L[ℂ] H) t + a) :=
      spectrum.add_mem_add_iff.mpr (CStarAlgebra.norm_mem_spectrum_of_nonneg a ha)
    have hn := spectrum.norm_le_norm_of_mem hs
    have hn' : ‖a‖ + t ≤ ‖t • (1 : H →L[ℂ] H) + a‖ := by
      simpa only [Real.norm_of_nonneg (add_nonneg (norm_nonneg a) ht),
        Algebra.algebraMap_eq_smul_one] using hn
    simpa only [add_comm] using hn'

theorem nontrivial_projection_range (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (hp0 : p ≠ 0) : Nontrivial p.range := by
  let : CompleteSpace p.range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range hp.isIdempotentElem).completeSpace_coe
  have hpe : p = p.range.starProjection := (isStarProjection_iff_eq_starProjection_range.mp hp).2
  have hE0 : p.range.starProjection ≠ 0 := hpe ▸ hp0
  have hn := representedCorner_nonzero_of_projection_ne_zero hE0
  by_contra h
  have : Subsingleton p.range := not_nontrivial_iff_subsingleton.mp h
  exact hn (Subsingleton.elim _ _)

theorem norm_add_scalar_le_of_order [Nontrivial H]
    (a b : H →L[ℂ] H) (ha : 0 ≤ a) (t : ℝ) (ht : 0 ≤ t)
    (hle : a + t • 1 ≤ b) : ‖a‖ + t ≤ ‖b‖ := by
  have hp : 0 ≤ a + t • (1 : H →L[ℂ] H) :=
    add_nonneg ha (smul_nonneg ht zero_le_one)
  have hn : ‖a + t • (1 : H →L[ℂ] H)‖ ≤ ‖b‖ :=
    CStarAlgebra.norm_le_norm_of_le_of_nonneg hle hp
  rwa [norm_add_nonneg_scalar a ha t ht] at hn

theorem norm_add_le_of_compressed_lower (E : Submodule ℂ H) [CompleteSpace E]
    [Nontrivial E] (M : VonNeumannAlgebra H) (hM : ScalarCenter M)
    (hE : E.starProjection ∈ M.commutant) (hE0 : E.starProjection ≠ 0)
    (x y : H →L[ℂ] H) (hxM : x ∈ M) (hx : 0 ≤ x)
    (t : ℝ) (ht : 0 ≤ t) (hcy : t • (1 : E →L[ℂ] E) ≤ cornerCompression E y) :
    ‖x‖ + t ≤ ‖x + y‖ := by
  have hcx : 0 ≤ cornerCompression E x := cornerCompression_nonneg E x hx
  have hle : cornerCompression E x + t • (1 : E →L[ℂ] E) ≤
      cornerCompression E x + cornerCompression E y :=
    add_le_add le_rfl hcy
  have hn : ‖cornerCompression E x‖ + t ≤
      ‖cornerCompression E x + cornerCompression E y‖ :=
    norm_add_scalar_le_of_order (H := E) (cornerCompression E x)
      (cornerCompression E x + cornerCompression E y) hcx t ht hle
  rw [norm_cornerCompression_of_factor E M hM hE hE0 x hxM,
    ← (cornerCompression E).map_add x y] at hn
  exact hn.trans (norm_cornerCompression_le E (x + y))

end

end KadisonKastler

end OAI
