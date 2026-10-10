import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicSimplexScaling
import OAI.NumberTheory.JointDickman.Arithmetic.OrderedSimplexIntegrable
import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicMeasureIntegrable

namespace OAI

/-! # The least-coordinate recurrence for ordered logarithmic simplices -/
namespace JointDickman
open MeasureTheory Set

noncomputable def logarithmicSimplex (n : ℕ) (c : ℝ) : ℝ :=
  orderedSimplexMass (logarithmicPrimeMeasure c) n 1

 theorem logarithmicSimplex_slice {c s : ℝ} (hc : 0 < c) (hcs : c ≤ s) (hs : s < 1)
    (n : ℕ) :
    orderedSimplexMass ((logarithmicPrimeMeasure c : Measure ℝ).restrict (Ioi s)) n (1-s) =
      logarithmicSimplex n (s/(1-s)) := by
  rw [logarithmicPrimeMeasure_restrict_Ioi hc hcs]
  exact logarithmicSimplexMass_scale (hc.trans_le hcs) (by linarith) (by linarith [hc.trans_le hcs]) n

 theorem logarithmicSimplex_succ {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (n : ℕ) :
    logarithmicSimplex (n+1) c =
      ∫ s in c..1, logarithmicSimplex n (s/(1-s))/s := by
  rw [logarithmicSimplex, orderedSimplexMass_succ, logarithmicPrimeMeasure_integral hc hc1]
  apply intervalIntegral.integral_congr_Ioo_of_le hc1
  intro s hs
  dsimp only
  rw [logarithmicSimplex_slice hc hs.1.le hs.2]

 theorem logarithmicSimplex_integrable {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (n : ℕ) :
    IntervalIntegrable (fun s => logarithmicSimplex n (s/(1-s))/s) volume c 1 := by
  have hi := (logarithmicPrimeMeasure_integrable_iff hc hc1 _).mp
    (orderedSimplexMass_succ_integrable (logarithmicPrimeMeasure c) n 1)
  apply hi.congr_uIoo
  intro s hs
  rw [uIoo_of_le hc1] at hs
  dsimp only
  rw [logarithmicSimplex_slice hc hs.1.le hs.2]

 theorem logarithmicSimplex_zero (c : ℝ) : logarithmicSimplex 0 c = 1 := by
  have he : orderedTupleRegion 0 1 = Set.univ := by
    ext t
    simp [orderedTupleRegion, StrictMono]
  simp [logarithmicSimplex, orderedSimplexMass, he, measureReal_def]

end JointDickman

end OAI
