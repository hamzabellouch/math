import OAI.Analysis.KadisonKastler.PolarNormalizerPath
import OAI.Analysis.KadisonKastler.ApproximateNormalizerComposition

namespace OAI

/-! # Based approximate-normalizer paths from smoothed algebra relations -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

local instance polarPathOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance polarPathStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

theorem exists_based_polar_normalizer_path (M : VonNeumannAlgebra H)
    (a c : ℝ → H →L[ℂ] H) (ha : Continuous a) {r : ℝ}
    (hr : 0 ≤ r) (hrsmall : r < 1 / 8)
    (hanorm : ∀ t, ‖a t‖ ≤ 1 + r) (hcnorm : ∀ t, ‖c t‖ ≤ 1 + r)
    (hac : ∀ t, ‖a t * c t - 1‖ ≤ r) (hca : ∀ t, ‖c t * a t - 1‖ ≤ r)
    (halg : ∀ t x, x ∈ unitBall M →
      Metric.infDist (a t * x * c t) (M : Set (H →L[ℂ] H)) ≤ r)
    (hcalg : ∀ t x, x ∈ unitBall M →
      Metric.infDist (c t * x * a t) (M : Set (H →L[ℂ] H)) ≤ r) :
    ∃ v E : ℝ → unitary (H →L[ℂ] H), Continuous v ∧ Continuous E ∧ E 0 = 1 ∧
      (∀ t, E t = v t * star (v 0)) ∧
      (∀ t, ‖(v t : H →L[ℂ] H) - a t‖ ≤ 4 * r) ∧
      (∀ t, ‖star (v t : H →L[ℂ] H) - c t‖ ≤ 10 * r) ∧
      (∀ t x, x ∈ unitBall M →
        Metric.infDist (unitaryConj (H := H) (E t) x) (M : Set (H →L[ℂ] H)) ≤ 50 * r) := by
  obtain ⟨v, hv, hva, hvc⟩ := exists_continuous_polar_path a c ha hr hrsmall
    hanorm hcnorm hac hca
  let E (t : ℝ) := v t * star (v 0)
  refine ⟨v, E, hv, hv.mul continuous_const, ?_, fun _ => rfl, hva, hvc, ?_⟩
  · exact Unitary.mul_star_self (v 0)
  · intro t x hx
    have hf (s : ℝ) (y : H →L[ℂ] H) (hy : y ∈ unitBall M) :
        Metric.infDist (unitaryConj (H := H) (v s) y) (M : Set (H →L[ℂ] H)) ≤ 16 * r :=
      infDist_polar_conjugation_le M (v s) (a s) (c s) y hr hrsmall
        (hva s) (hvc s) (hcnorm s) hy.2 (halg s y hy)
    have hb (y : H →L[ℂ] H) (hy : y ∈ unitBall M) :
        Metric.infDist (unitaryConj (H := H) (star (v 0)) y)
          (M : Set (H →L[ℂ] H)) ≤ 17 * r :=
      infDist_polar_star_conjugation_le M (v 0) (a 0) (c 0) y hr hrsmall
        (hva 0) (hvc 0) (hanorm 0) hy.2 (hcalg 0 y hy)
    exact (infDist_unitaryConj_mul_le M (v t) (star (v 0)) (hf t) hb x hx).trans_eq (by ring)

end

end KadisonKastler

end OAI
