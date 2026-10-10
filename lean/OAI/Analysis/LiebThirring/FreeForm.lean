import OAI.Analysis.LiebThirring.CompactAlternative

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set
open scoped Topology

/-- Positive free form `∫|u'|² + a∫|u|²` on the full H¹ graph. -/
def freeFormMap (a : ℝ) : H1C →L[ℂ] H1C :=
  gradL.adjoint.comp gradL + (a:ℂ) • (valL.adjoint.comp valL)

lemma freeFormMap_inner (a : ℝ) (u v : H1C) :
    inner ℂ u (freeFormMap a v) =
      inner ℂ (gradL u) (gradL v)+(a:ℂ)*inner ℂ (valL u) (valL v) := by
  change inner ℂ u (gradL.adjoint (gradL v)+(a:ℂ) • valL.adjoint (valL v)) = _
  rw [inner_add_right,inner_smul_right u (valL.adjoint (valL v)) (a:ℂ),
    ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]

lemma freeFormMap_coercive {a : ℝ} (_ha : 0 < a) (u : H1C) :
    min 1 a * ‖u‖^2 ≤ (inner ℂ u (freeFormMap a u)).re := by
  rw [freeFormMap_inner,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  have hi (v : L2C) : (inner ℂ v v).re = ‖v‖^2 := (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  rw [hi,hi,h1_norm_sq]
  have h1 := mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) a) (sq_nonneg ‖gradL u‖)
  have h2 := mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) a) (sq_nonneg ‖valL u‖)
  nlinarith

lemma freeFormMap_bijective {a : ℝ} (ha : 0 < a) : Function.Bijective (freeFormMap a) :=
  coercive_bijective _ (lt_min (by norm_num) ha) (freeFormMap_coercive ha)

def freeFormEquiv {a : ℝ} (ha : 0 < a) : H1C ≃L[ℂ] H1C :=
  ContinuousLinearEquiv.ofBijective (freeFormMap a)
    (LinearMap.ker_eq_bot.mpr (freeFormMap_bijective ha).1)
    (LinearMap.range_eq_top.mpr (freeFormMap_bijective ha).2)

/-- Form of `H+a` on H¹. -/
def energyFormMap {W : ℝ → ℝ} (d : PotentialData W) (a : ℝ) : H1C →L[ℂ] H1C :=
  freeFormMap a-(weightedL d).adjoint.comp (weightedL d)

lemma energyFormMap_inner {W : ℝ → ℝ} (d : PotentialData W) (a : ℝ) (u v : H1C) :
    inner ℂ u (energyFormMap d a v) =
      schrodingerForm W (toH1 u) (toH1 v)+(a:ℂ)*inner ℂ (valL u) (valL v) := by
  change inner ℂ u (freeFormMap a v-(weightedL d).adjoint (weightedL d v)) = _
  rw [inner_sub_right,freeFormMap_inner,ContinuousLinearMap.adjoint_inner_right,form_eq_inner]
  ring

end SharpLiebThirring.OperatorProof

end

end OAI
