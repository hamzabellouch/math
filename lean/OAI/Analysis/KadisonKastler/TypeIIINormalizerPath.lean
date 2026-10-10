import OAI.Analysis.KadisonKastler.TypeIIIInfinitesimal
import OAI.Analysis.KadisonKastler.NormalizerPathLocal

namespace OAI

/-! # A uniform bound for paths of approximate normalizers of type III factors -/

namespace KadisonKastler

open scoped Topology

noncomputable section

universe u

local instance typeIIIPathSourceOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance typeIIIPathSourceStarOrder {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem uniform_typeIII_approximate_normalizer_path
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H,
        PublishedBlockCommutantApproximation (Algebra M) H) :
    ∃ e0 C : ℝ, 0 < e0 ∧ 0 < C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [TopologicalSpace.SeparableSpace H],
      ∀ (M : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ (I : Set ℝ), IsPreconnected I → 0 ∈ I →
      ∀ (v : ℝ → unitary (H →L[ℂ] H)), ContinuousOn v I → v 0 = 1 →
      ∀ e : ℝ, 0 ≤ e → e < e0 →
      (∀ t ∈ I, ∀ x ∈ unitBall M, Metric.infDist (unitaryConj (v t) x)
        (M : Set (H →L[ℂ] H)) ≤ e) →
      ∀ t ∈ I, Metric.infDist ((v t : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
        (separateUnitaryProducts M) ≤ C * e := by
  obtain ⟨K, hK, hlinear⟩ := uniform_typeIII_selfAdjoint_estimate
    hSpectral hCompare hSakai hDistance
  let r : ℝ := min (1 / 4) (1 / (64 * K))
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hrquarter : r ≤ 1 / 4 := min_le_left _ _
  have hKr : K * r ≤ 1 / 64 := by
    calc
      K * r ≤ K * (1 / (64 * K)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK.le
      _ = 1 / 64 := by field_simp
  refine ⟨r / (4 * K), 2 * K, by positivity, by positivity, ?_⟩
  intro H _ _ _ _ M hM I hI hzero v hv hvzero e _ he hdefect t ht
  let b (s : ℝ) := Metric.infDist (v s : H →L[ℂ] H) (separateUnitaryProducts M)
  have hb : ContinuousOn b I :=
    (Metric.continuous_infDist_pt (separateUnitaryProducts M)).comp_continuousOn
      (continuous_subtype_val.comp_continuousOn hv)
  have hbzero : b 0 = 0 := by
    dsimp [b]
    rw [hvzero, OneMemClass.coe_one]
    exact Metric.infDist_zero_of_mem (one_mem_separateUnitaryProducts M)
  have hKe : K * e < r / 2 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4 * K)).mp he
    nlinarith
  have hbarrier := continuous_quadratic_barrier hI hzero b hb hbzero
    (fun _ _ => Metric.infDist_nonneg) hKe (show 0 ≤ 16 * K by positivity) hr
    (show (16 * K) * r ≤ 1 / 2 by nlinarith) ?_
  · simpa only [b, mul_assoc] using hbarrier t ht
  · intro s hs hbs
    have hsmall : b s < 1 := by linarith
    exact normalizer_distance_quadratic M hK.le (hlinear H M hM) (v s)
      (hdefect s hs) hsmall

end

end KadisonKastler

end OAI
