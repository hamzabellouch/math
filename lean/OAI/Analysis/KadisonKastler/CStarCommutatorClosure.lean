import OAI.Analysis.KadisonKastler.KaplanskyDensity
import OAI.Analysis.KadisonKastler.SpectralClipping

namespace OAI

/-! # Spatial commutator bounds pass to the represented bicommutant

Spectral clipping lifts each represented contraction to an actual source
contraction. Kaplansky density then passes its commutator bound to the
unit ball of the represented von Neumann closure.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_source_contraction (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (b : π.range) (hb : ‖(b : H →L[ℂ] H)‖ ≤ 1) :
    ∃ a : A, π a = b ∧ ‖a‖ ≤ 1 := by
  obtain ⟨a, ha⟩ := b.property
  change π a = (b : H →L[ℂ] H) at ha
  refine ⟨spectralClip 1 a, ?_, spectralClip_norm_le zero_lt_one a⟩
  rw [map_spectralClip_eq π zero_lt_one a (by simpa only [ha] using hb), ha]

theorem commutator_bound_generated_contraction
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hsource : ∀ a : A, ‖T * π a - π a * T‖ ≤ e * ‖a‖)
    (b : H →L[ℂ] H)
    (hb : b ∈ generatedVonNeumannAlgebra π.range) (hbn : ‖b‖ ≤ 1) :
    ‖T * b - b * T‖ ≤ e := by
  classical
  have hb' : b ∈ Set.centralizer (Set.centralizer (π.range : Set (H →L[ℂ] H))) := by
    rwa [← generatedVonNeumannAlgebra_coe]
  obtain ⟨a, ha, ht⟩ := publishedKaplanskyDensity.exists_strong_contraction_net
    π.range b hb' hbn
  have hbound (d : Finset H × ℕ) : ‖T * (a d : H →L[ℂ] H) - (a d : H →L[ℂ] H) * T‖ ≤ e := by
    obtain ⟨x, hx, hxn⟩ := exists_source_contraction π (a d) (ha d)
    rw [← hx]
    exact (hsource x).trans (mul_le_of_le_one_right he hxn)
  apply ContinuousLinearMap.opNorm_le_bound _ he
  intro x
  have hlim : Tendsto (fun d =>
      (T * (a d : H →L[ℂ] H) - (a d : H →L[ℂ] H) * T) x) atTop
      (𝓝 ((T * b - b * T) x)) := by
    change Tendsto (fun d => T ((a d : H →L[ℂ] H) x) - (a d : H →L[ℂ] H) (T x))
      atTop (𝓝 (T (b x) - b (T x)))
    exact (T.continuous.continuousAt.tendsto.comp (ht x)).sub (ht (T x))
  exact le_of_tendsto hlim.norm (Eventually.of_forall fun d =>
    (ContinuousLinearMap.le_opNorm _ x).trans
      (mul_le_mul_of_nonneg_right (hbound d) (norm_nonneg x)))

end

end KadisonKastler

end OAI
