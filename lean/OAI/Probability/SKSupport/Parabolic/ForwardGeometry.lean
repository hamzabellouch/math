import Mathlib
import OAI.Probability.SKSupport.Backward.Backward

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK.Heat

def forwardTime (a t : ℝ) : ℝ := a+max t 0
def forwardScale (a t : ℝ) : ℝ := a/forwardTime a t
def forwardVariance (a t : ℝ) : ℝ := a*max t 0/forwardTime a t

def forwardCorrection (a : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (1/2:ℝ)*Real.log (forwardScale a t)+
    varianceLogHeat 1 (forwardVariance a t) f (forwardScale a t*x)

def forwardScore (a : ℝ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  x/forwardTime a t-deriv (forwardCorrection a f t) x

lemma forwardTime_pos {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 < forwardTime a t :=
  add_pos_of_pos_of_nonneg ha (le_max_right _ _)

lemma forwardScale_pos {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 < forwardScale a t :=
  div_pos ha (forwardTime_pos ha t)

lemma forwardScale_le_one {a : ℝ} (ha : 0 < a) (t : ℝ) : forwardScale a t ≤ 1 := by
  apply (div_le_one (forwardTime_pos ha t)).mpr
  exact le_add_of_nonneg_right (le_max_right _ _)

lemma forwardVariance_nonneg {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 ≤ forwardVariance a t :=
  div_nonneg (mul_nonneg ha.le (le_max_right _ _)) (forwardTime_pos ha t).le

lemma forwardVariance_le {a : ℝ} (ha : 0 < a) (t : ℝ) : forwardVariance a t ≤ a := by
  apply (div_le_iff₀ (forwardTime_pos ha t)).mpr
  try dsimp [forwardTime]
  nlinarith [sq_nonneg a]

lemma continuous_forwardTime (a : ℝ) : Continuous (forwardTime a) :=
  continuous_const.add (continuous_id.max continuous_const)
lemma continuous_forwardScale {a : ℝ} (ha : 0 < a) : Continuous (forwardScale a) :=
  continuous_const.div (continuous_forwardTime a) (fun t => ne_of_gt (forwardTime_pos ha t))
lemma continuous_forwardVariance {a : ℝ} (ha : 0 < a) : Continuous (forwardVariance a) :=
  (continuous_const.mul (continuous_id.max continuous_const)).div (continuous_forwardTime a)
    (fun t => ne_of_gt (forwardTime_pos ha t))

lemma hasDerivAt_forwardTime {a t : ℝ} (ht : 0 < t) : HasDerivAt (forwardTime a) 1 t := by
  apply ((hasDerivAt_id t).const_add a).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp only [forwardTime,max_eq_left (show (0:ℝ) ≤ s from le_of_lt hs),id_eq]

lemma hasDerivAt_forwardScale {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (forwardScale a) (-forwardScale a t/forwardTime a t) t := by
  convert (hasDerivAt_const t a).div (hasDerivAt_forwardTime ht) (ne_of_gt (forwardTime_pos ha t)) using 1 <;>
    first | rfl | (dsimp [forwardScale]; field_simp; ring)

lemma hasDerivAt_forwardVariance {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (forwardVariance a) ((forwardScale a t)^2) t := by
  have he : forwardVariance a = fun s => a-a*forwardScale a s := by
    funext s
    dsimp [forwardVariance,forwardScale]
    field_simp [ne_of_gt (forwardTime_pos ha s)]
    dsimp [forwardTime]
    ring
  rw [he]
  convert ((hasDerivAt_forwardScale ha ht).const_mul a).const_sub a using 1
  dsimp [forwardScale]
  field_simp

lemma forwardVariance_pos {a t : ℝ} (ha : 0 < a) (ht : 0 < t) : 0 < forwardVariance a t := by
  exact div_pos (mul_pos ha (lt_of_lt_of_le ht (le_max_left _ _))) (forwardTime_pos ha t)

lemma forwardCorrection_terminal (a : ℝ) (ha : a ≠ 0) (f : ℝ → ℝ) :
    forwardCorrection a f 0 = f := by
  have he : varianceLogHeat 1 0 f = f := funext (fun x => by
    simpa only [backward,sub_self] using backward_terminal 1 0 f x)
  funext x
  simp only [forwardCorrection,forwardScale,forwardVariance,forwardTime,max_self,add_zero,
    mul_zero,zero_div,div_self ha,Real.log_one,mul_zero,zero_add,one_mul,he]

end ZeroTemperatureSK.Heat

end
end

end OAI
