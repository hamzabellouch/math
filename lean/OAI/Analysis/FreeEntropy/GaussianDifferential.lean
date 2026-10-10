import OAI.Analysis.FreeEntropy.GaussianKernel

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped Topology
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
def normalTimeDerivative (s : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  (-(Fintype.card ι:ℝ)/(2*s)+‖x‖^2/(2*s^2))*normalKernel s x
def normalGradient (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) : ℝ := -x i/s*normalKernel s x
def normalSecond (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) : ℝ := ((x i)^2/s^2-1/s)*normalKernel s x
 theorem normalKernel_hasDeriv_coordinate_at (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) (r : ℝ) :
    HasDerivAt (fun t : ℝ => normalKernel s (x+t • EuclideanSpace.single i 1))
      (normalGradient s (x+r • EuclideanSpace.single i 1) i) r := by
  have hd : HasDerivAt (fun t : ℝ => ‖x+t • EuclideanSpace.single i 1‖^2) (2*(x i+r)) r := by
    have h := ((hasDerivAt_const r x).add ((hasDerivAt_id r).smul_const (EuclideanSpace.single i 1))).norm_sq
    simpa [real_inner_comm,PiLp.inner_apply,EuclideanSpace.single] using h
  have h := ((hasDerivAt_const r (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s))).sub (hd.div_const (2*s))).exp
  convert h using 1
  · rfl
  · dsimp only [Pi.sub_apply,normalGradient]
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,EuclideanSpace.single,PiLp.single_apply,ite_true,mul_one,normalKernel]
    ring
 theorem normalGradient_hasDeriv_coordinate (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) (r : ℝ) :
    HasDerivAt (fun t : ℝ => normalGradient s (x+t • EuclideanSpace.single i 1) i)
      (normalSecond s (x+r • EuclideanSpace.single i 1) i) r := by
  have h := (((hasDerivAt_const r (x i)).add (hasDerivAt_id r)).neg.div_const s).mul (normalKernel_hasDeriv_coordinate_at s x i r)
  simp only [normalGradient,normalSecond,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
    EuclideanSpace.single,PiLp.single_apply,ite_true,mul_one,Pi.neg_apply,Pi.add_apply,id_eq] at h ⊢
  convert h using 1; first | rfl | ring
 omit [DecidableEq ι] in
 theorem normal_heatEquation (s : ℝ) (x : EuclideanSpace ℝ ι) :
    normalTimeDerivative s x = (1/2:ℝ)*∑ i,normalSecond s x i := by
  unfold normalTimeDerivative normalSecond
  rw [← sum_mul,sum_sub_distrib,← sum_div,sum_const,card_univ,nsmul_eq_mul]
  have hn : ‖x‖^2=∑i,(x i)^2 := by simp [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
  rw [hn]
  ring
 omit [DecidableEq ι] in
 theorem normalTimeDerivative_continuousOn :
    ContinuousOn (fun z : ℝ × EuclideanSpace ℝ ι => normalTimeDerivative z.1 z.2) {z | 0<z.1} := by
  unfold normalTimeDerivative
  apply ContinuousOn.mul _ normalKernel_continuousOn
  apply ContinuousOn.add
  · exact continuousOn_const.div (by fun_prop) (fun z hz => mul_ne_zero (by norm_num) (ne_of_gt hz))
  · exact (continuous_snd.norm.pow 2).continuousOn.div ((continuous_const.mul (continuous_fst.pow 2)).continuousOn) (fun z hz => mul_ne_zero (by norm_num) (pow_ne_zero _ (ne_of_gt hz)))
 omit [DecidableEq ι] in
 theorem normalGradient_continuous (s : ℝ) (i : ι) : Continuous (fun x : EuclideanSpace ℝ ι => normalGradient s x i) := by
  unfold normalGradient
  exact (((PiLp.continuous_apply 2 _ i).neg).div_const s).mul (normalKernel_continuous_space s)
 omit [DecidableEq ι] in
 theorem normalSecond_continuous (s : ℝ) (i : ι) : Continuous (fun x : EuclideanSpace ℝ ι => normalSecond s x i) := by
  unfold normalSecond
  exact ((((PiLp.continuous_apply 2 _ i).pow 2).div_const (s^2)).sub continuous_const).mul (normalKernel_continuous_space s)
end FiniteEntropySeparation

end

end OAI
