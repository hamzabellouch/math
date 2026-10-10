import OAI.Analysis.LipschitzHilbert.Fourier.GeneralAnnularComparison
import OAI.Analysis.LipschitzHilbert.Geometry.GeometricSpectralOverlap
import OAI.Analysis.LipschitzHilbert.Fourier.HilbertAnnularVariation

namespace OAI

/-! Whole-line annular variation with arbitrary fixed inner and outer
frequency constants. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem general_scalar_annular_variation (hL : LepingleInput) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (f : Fin N → SchwartzMap ℝ ℂ),
      (∀ j ξ, |ξ| < a * (4 : ℝ) ^ j.val → 𝓕 (f j) ξ = 0) →
      (∀ j ξ, b * (4 : ℝ) ^ j.val < |ξ| → 𝓕 (f j) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
        (2 / 3 : ℝ)) ≤ (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2) := by
  obtain ⟨C,hC,hbound⟩ := scalar_shifted_line_comparison hL
  obtain ⟨M,hM⟩ := pow_unbounded_of_one_lt (b / a) (by norm_num : (1 : ℝ) < 4)
  have hsep : b < a * (4 : ℝ) ^ M := by
    have h := (div_lt_iff₀ ha).mp hM
    simpa only [mul_comm] using h
  let D : ℝ≥0 := ⟨annularErrorConstant a b, (annularErrorConstant_pos ha hb).le⟩
  let K : ℝ≥0 := 2 * C ^ 2 * M + 8 * (4 * D) ^ 2 + 1
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro N f hlow hhigh
  have hlocal (g : FiniteLineGrid) (offset : ℕ) (hdepth : offset + N ≤ g.depth)
      (hmesh : ∀ i, g.meshWidth (offset + i) = ((4 : ℝ) ^ i)⁻¹) :
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
        (2 / 3 : ℝ) ∂g.lineMeasure) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2) := by
    have hf : Measurable (fullBandSum f) := by
      rw [fullBandSum_coe]
      exact (∑ j, f j : SchwartzMap ℝ ℂ).continuous.measurable
    have hf2 : MemLp (fullBandSum f) 2 g.lineMeasure := (fullBandSum_memLp f).restrict g.root
    have hp2 (i : ℕ) : MemLp (partialBandSum f i) 2 g.lineMeasure :=
      (partialBandSum_memLp f i).restrict g.root
    have he2 (i : ℕ) : MemLp (fun x => partialBandSum f i x -
        g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i) x) 2 g.lineMeasure := by
      convert (hp2 i).sub (g.scalarAverage_memLp g.lineMeasure _ hf2 (offset + i)) using 1
    have h := hbound g offset (fullBandSum f) (partialBandSum f) hf
      (partialBandSum_measurable f) hf2 N
    rw [lintegral_enorm_square _ _ hf2] at h
    simp_rw [lintegral_enorm_square _ _ (he2 _)] at h
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      integral_nonneg (fun x => sq_nonneg (‖partialBandSum f i.val x -
        g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i.val) x‖)))] at h
    have htotal : (∫ x, ‖fullBandSum f x‖ ^ 2 ∂g.lineMeasure) ≤
        M * ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
      apply le_trans _ (geometric_annular_energy f ha hsep hlow hhigh)
      exact setIntegral_le_integral
        ((fullBandSum_memLp f).integrable_norm_pow (by decide : 2 ≠ 0))
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    have hsquare := general_annular_square_comparison g offset f ha hb hlow hhigh hdepth hmesh
    have ht := ENNReal.ofReal_le_ofReal htotal
    have hs := ENNReal.ofReal_le_ofReal hsquare
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg M), ENNReal.ofReal_natCast] at ht
    rw [ENNReal.ofReal_mul (sq_nonneg _)] at hs
    have hc : ENNReal.ofReal ((4 * annularErrorConstant a b) ^ 2) = (4 * (D : ℝ≥0∞)) ^ 2 := by
      change ENNReal.ofReal ((4 * (D : ℝ)) ^ 2) = _
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      simp only [ENNReal.ofReal_coe_nnreal]
    rw [hc] at hs
    calc
      _ ≤ 2 * (C : ℝ≥0∞) ^ 2 * (M * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) +
          8 * ((4 * (D : ℝ≥0∞)) ^ 2 * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) :=
        h.trans (add_le_add (mul_le_mul_right ht _) (mul_le_mul_right hs _))
      _ ≤ _ := by
        have hk : 2 * (C : ℝ≥0∞) ^ 2 * M + 8 * (4 * (D : ℝ≥0∞)) ^ 2 ≤ (K : ℝ≥0∞) := by
          dsimp [K]
          exact le_add_of_nonneg_right (by positivity)
        convert mul_le_mul_right hk (ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) using 1 <;> ring
  let V := fun x => ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
    (2 / 3 : ℝ)
  change (∫⁻ x, V x) ≤ _
  rw [← setLIntegral_univ, ← expandingGrid_cover N,
    setLIntegral_iUnion_of_directed V (expandingGrid_mono N).directed_le]
  apply iSup_le
  intro m
  exact hlocal (expandingGrid N m) m (by simp [expandingGrid]) (expandingGrid_mesh N m)

theorem general_hilbert_annular_variation (hL : LepingleInput) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (f : Fin N → κ → SchwartzMap ℝ ℂ),
      (∀ j k ξ, |ξ| < a * (4 : ℝ) ^ j.val → 𝓕 (f j k) ξ = 0) →
      (∀ j k ξ, b * (4 : ℝ) ^ j.val < |ξ| → 𝓕 (f j k) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => hilbertPartialBandSum f i x) N) ^ (2 / 3 : ℝ)) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∑ k, ∫ x, ‖f j k x‖ ^ 2) := by
  obtain ⟨K,hK,hbound⟩ := general_scalar_annular_variation hL ha hb
  refine ⟨K,hK,?_⟩
  intro N κ inst f hlow hhigh
  calc
    _ ≤ ∫⁻ x, ∑ k, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (fun j => f j k) i x) N) ^ (2 / 3 : ℝ) := by
      apply lintegral_mono
      intro x
      exact ennreal_complex_variation_coordinates (fun i => hilbertPartialBandSum f i x) N
    _ = ∑ k, ∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (fun j => f j k) i x) N) ^ (2 / 3 : ℝ) := by
      apply lintegral_finsetSum
      intro k _
      exact (measurable_finiteCubicVariation _ (partialBandSum_measurable (fun j => f j k)) N).ennreal_ofReal.pow_const _
    _ ≤ ∑ k, (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j k x‖ ^ 2) :=
      Finset.sum_le_sum (fun k _ => hbound N (fun j => f j k)
        (fun j => hlow j k) (fun j => hhigh j k))
    _ = _ := by
      rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg]
      · congr 2
        exact Finset.sum_comm
      · intro k _
        exact Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))

end LipschitzHilbert

end

end OAI
