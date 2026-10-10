import OAI.Analysis.KadisonKastler.SmoothedNormalizerLimit
import OAI.Analysis.KadisonKastler.TypeIIINormalizerPath

namespace OAI

/-! # Exact normalizers from approximate-normalizer smoothing paths

The path estimate produces algebra/commutant products independently at each
smoothing scale. The UCP limit argument then recovers one exact normalizer
without requiring the chosen products, or the polar paths, to converge.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance smoothedPathOrder (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance smoothedPathStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

private theorem exists_normalizer_of_infDist_lt
    (M : VonNeumannAlgebra H) (v : unitary (H →L[ℂ] H)) {a : ℝ}
    (ha : Metric.infDist (v : H →L[ℂ] H) (separateUnitaryProducts M) < a) :
    ∃ p : unitary (H →L[ℂ] H), Conjugates p M M ∧
      ‖(p : H →L[ℂ] H) - v‖ < a := by
  obtain ⟨p, hp, hvp⟩ := (Metric.infDist_lt_iff
    (show (separateUnitaryProducts M).Nonempty from
      ⟨1, one_mem_separateUnitaryProducts M⟩)).mp ha
  obtain ⟨b, c, hb, hc, rfl⟩ := hp
  refine ⟨b * c, conjugates_self_of_separate_factors hb hc, ?_⟩
  simpa only [dist_eq_norm, norm_sub_rev] using hvp

theorem exists_normalizer_of_smoothed_infDist
    (M : VonNeumannAlgebra H) (W : unitary (H →L[ℂ] H))
    (hCorrection : PublishedMultiplicationCorrection (unitaryConjugateAlgebra W M))
    (hCommutant : PublishedBlockCommutantApproximation
      (Algebra (unitaryConjugateAlgebra W M)) H)
    (E : ℕ → unitary (H →L[ℂ] H)) (Q : ℕ → H →L[ℂ] H)
    (hstar : ∀ x, Tendsto (fun n => star (Q n) x) atTop
      (𝓝 (star (W : H →L[ℂ] H) x)))
    {a d B g : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hB : 0 ≤ B)
    (hE : ∀ n, Metric.infDist (E n : H →L[ℂ] H) (separateUnitaryProducts M) < a)
    (hEQ : ∀ n, ‖(E n : H →L[ℂ] H) - Q n‖ ≤ d)
    (hQ : ∀ n, ‖Q n‖ ≤ B)
    (hsmall : (1 + B) * (a + d) < 1 / 1000)
    (hge : g + (1 + B) * (a + d) < 1)
    (hgap : kkDistance (unitaryConjugateAlgebra W M) M < g) :
    ∃ p : unitary (H →L[ℂ] H), Conjugates p M M ∧
      ‖(p : H →L[ℂ] H) - W‖ ≤ 128 * ((1 + B) * (a + d)) := by
  choose V hVM hVE using fun n => exists_normalizer_of_infDist_lt M (E n) (hE n)
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  apply exists_normalizer_of_smoothed_approximation M W hCorrection hCommutant ω
    V hVM Q (fun x => (hstar x).mono_left (Ultrafilter.of_le atTop)) hB (add_nonneg ha hd)
    hQ ?_ hsmall hge hgap
  intro n
  exact (norm_sub_le_norm_sub_add_norm_sub (V n : H →L[ℂ] H) (E n) (Q n)).trans
    (add_le_add (hVE n).le (hEQ n))

/-- Smoothing estimates give normalizers with constants chosen before
the Hilbert space and the type III factor. -/
theorem uniform_typeIII_smoothed_normalizers
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H,
        PublishedBlockCommutantApproximation (Algebra M) H) :
    ∃ e0 K : ℝ, 0 < e0 ∧ 0 < K ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [TopologicalSpace.SeparableSpace H],
      ∀ (M : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ W : unitary (H →L[ℂ] H),
      PublishedMultiplicationCorrection (unitaryConjugateAlgebra W M) →
      ∀ (E : ℕ → ℝ → unitary (H →L[ℂ] H)) (Q : ℕ → H →L[ℂ] H)
        (t e d B g : ℝ),
      0 < e → e < e0 → 0 ≤ d → 0 ≤ B →
      (∀ n, Continuous (E n)) → (∀ n, E n 0 = 1) →
      (∀ n s, ∀ x ∈ unitBall M,
        Metric.infDist (unitaryConj (H := H) (E n s) x) (M : Set (H →L[ℂ] H)) ≤ e) →
      (∀ x, Tendsto (fun n => star (Q n) x) atTop (𝓝 (star (W : H →L[ℂ] H) x))) →
      (∀ n, ‖(E n t : H →L[ℂ] H) - Q n‖ ≤ d) →
      (∀ n, ‖Q n‖ ≤ B) →
      (1 + B) * ((K + 1) * e + d) < 1 / 1000 →
      g + (1 + B) * ((K + 1) * e + d) < 1 →
      kkDistance (unitaryConjugateAlgebra W M) M < g →
      ∃ p : unitary (H →L[ℂ] H), Conjugates p M M ∧
        ‖(p : H →L[ℂ] H) - W‖ ≤ 128 * ((1 + B) * ((K + 1) * e + d)) := by
  obtain ⟨e0, K, he0, hK, hpath⟩ := uniform_typeIII_approximate_normalizer_path
    hSpectral hCompare hSakai hDistance
  refine ⟨e0, K, he0, hK, ?_⟩
  intro H _ _ _ _ M hM W hCorrection E Q t e d B g he he0' hd hB hcont hzero
    hdefect hstar hEQ hQ hsmall hge hgap
  apply exists_normalizer_of_smoothed_infDist M W hCorrection (hDistance H _)
    (fun n => E n t) Q hstar (mul_nonneg (by linarith) he.le) hd hB ?_
    hEQ hQ hsmall hge hgap
  intro n
  have hb := hpath H M hM Set.univ isPreconnected_univ (Set.mem_univ 0)
    (E n) (hcont n).continuousOn (hzero n) e he.le he0'
    (fun s _ x hx => hdefect n s x hx) t (Set.mem_univ t)
  exact hb.trans_lt (by nlinarith)

end

end KadisonKastler

end OAI
