import OAI.Analysis.LipschitzHilbert.Fourier.ScalarLineVariation
import OAI.Analysis.LipschitzHilbert.Fourier.BandOrthogonality
import OAI.Analysis.LipschitzHilbert.Fourier.ShiftedLineAverage

namespace OAI

/-! Local annular variation from Lépingle's inequality,
with the smooth/dyadic comparison supplied by packet estimates. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem fullBandSum_coe {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) :
    fullBandSum f = (∑ j, f j : SchwartzMap ℝ ℂ) := by
  funext x
  simp [fullBandSum]

theorem partialBandSum_coe {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (i : ℕ) :
    partialBandSum f i = (∑ j, if j.val < i then f j else 0 : SchwartzMap ℝ ℂ) := by
  funext x
  simp only [partialBandSum, sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

theorem fullBandSum_memLp {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) :
    MemLp (fullBandSum f) 2 volume := by
  rw [fullBandSum_coe]
  exact (∑ j, f j : SchwartzMap ℝ ℂ).memLp 2 volume

theorem partialBandSum_memLp {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (i : ℕ) :
    MemLp (partialBandSum f i) 2 volume := by
  have h (j : Fin N) : MemLp (fun x => if j.val < i then f j x else 0) 2 volume := by
    by_cases hj : j.val < i
    · simpa only [ite_eq_left hj] using (f j).memLp 2 volume
    · simp only [ite_eq_right hj]
      exact MemLp.zero
  convert memLp_finsetSum Finset.univ (fun j _ => h j) using 1
  funext x
  simp only [partialBandSum]

theorem geometric_annular_variation (hL : LepingleInput) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (g : FiniteLineGrid) (offset : ℕ) (f : Fin N → SchwartzMap ℝ ℂ),
      offset + N ≤ g.depth →
      (∀ i, g.meshWidth (offset + i) = ((4 : ℝ) ^ i)⁻¹) →
      (∀ j ξ, |ξ| < bandInner j.val → 𝓕 (f j) ξ = 0) →
      (∀ j ξ, bandOuter j.val < |ξ| → 𝓕 (f j) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
        (2 / 3 : ℝ) ∂g.lineMeasure) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2) := by
  obtain ⟨C,hC,hbound⟩ := scalar_shifted_line_comparison hL
  refine ⟨2 * C ^ 2 + 2048, by positivity, ?_⟩
  intro N g offset f hdepth hmesh hlow hhigh
  have hf : Measurable (fullBandSum f) := by
    rw [fullBandSum_coe]
    exact (∑ j, f j : SchwartzMap ℝ ℂ).continuous.measurable
  have hp (i : ℕ) : Measurable (partialBandSum f i) := by
    apply Finset.measurable_sum
    intro j _
    by_cases hj : j.val < i
    · simpa only [ite_eq_left hj] using (f j).continuous.measurable
    · simpa only [ite_eq_right hj] using (measurable_const : Measurable (fun _ : ℝ => (0 : ℂ)))
  have hf2 : MemLp (fullBandSum f) 2 g.lineMeasure := by
    exact (fullBandSum_memLp f).restrict g.root
  have hp2 (i : ℕ) : MemLp (partialBandSum f i) 2 g.lineMeasure := by
    exact (partialBandSum_memLp f i).restrict g.root
  have he2 (i : ℕ) : MemLp (fun x => partialBandSum f i x -
      g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i) x) 2 g.lineMeasure := by
    convert (hp2 i).sub (g.scalarAverage_memLp g.lineMeasure _ hf2 (offset + i)) using 1
  have h := hbound g offset (fullBandSum f) (partialBandSum f) hf hp hf2 N
  rw [lintegral_enorm_square _ _ hf2] at h
  simp_rw [lintegral_enorm_square _ _ (he2 _)] at h
  have hnonneg (i : Fin (N + 1)) : 0 ≤ ∫ x, ‖partialBandSum f i.val x -
      g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i.val) x‖ ^ 2 ∂g.lineMeasure :=
    integral_nonneg (fun _ => sq_nonneg _)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg i)] at h
  have htotal : (∫ x, ‖fullBandSum f x‖ ^ 2 ∂g.lineMeasure) ≤
      ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
    calc
      _ ≤ ∫ x, ‖fullBandSum f x‖ ^ 2 := by
        apply setIntegral_le_integral
        · exact (fullBandSum_memLp f).integrable_norm_pow (by decide : 2 ≠ 0)
        · filter_upwards with x
          exact sq_nonneg _
      _ = _ := separated_band_energy f hlow hhigh
  have hsquare := geometric_square_comparison g offset f hlow hhigh hdepth hmesh
  have htotal' := ENNReal.ofReal_le_ofReal htotal
  have hsquare' := ENNReal.ofReal_le_ofReal hsquare
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 256), ENNReal.ofReal_ofNat] at hsquare'
  calc
    _ ≤ 2 * (C : ℝ≥0∞) ^ 2 * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2) +
        8 * (256 * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) :=
      h.trans (add_le_add (mul_le_mul_right htotal' _) (mul_le_mul_right hsquare' _))
    _ = _ := by push_cast; ring


theorem local_annular_variation (hL : LepingleInput) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (origin : ℝ) (f : Fin N → SchwartzMap ℝ ℂ),
      (∀ j ξ, |ξ| < bandInner j.val → 𝓕 (f j) ξ = 0) →
      (∀ j ξ, bandOuter j.val < |ξ| → 𝓕 (f j) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
        (2 / 3 : ℝ) ∂(fourGrid origin N).lineMeasure) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2) := by
  obtain ⟨K,hK,hbound⟩ := geometric_annular_variation hL
  refine ⟨K,hK,?_⟩
  intro N origin f hlow hhigh
  exact hbound N (fourGrid origin N) 0 f (by simp [fourGrid])
    (fun i => by simpa only [Nat.zero_add] using fourGrid_mesh origin N i) hlow hhigh

end LipschitzHilbert

end

end OAI
