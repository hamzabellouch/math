import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ExpMulLp

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile125
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma lipschitz_uniformly_vanishes_of_expWeighted (hfin : FiniteOnBoundedSets m) (o : X)
    (hvol : ∀ r : ℝ,0 < r → ∃ A B : ℝ,0 < A ∧ 0 ≤ B ∧ ∀ x : X,
      A*Real.exp (-B*dist x o) ≤ (m (Metric.ball x r)).toReal)
    {ι : Type*} {gs : ι → X → ℝ} {L : ℝ≥0} (hg : ∀ i,LipschitzWith L (gs i))
    (hw : ∀ a : ℝ,0 ≤ a → ∃ J : ℝ,∀ i,MemLp (fun x => gs i x*Real.exp (a*dist x o)) 2 m ∧
      (∫ x,(gs i x*Real.exp (a*dist x o))^2 ∂m) ≤ J) :
    ∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ i,∀ x : X,R < dist x o → |gs i x| < ε := by
  intro ε hε
  let r := ε/(2*((L:ℝ)+1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hre : r*(2*((L:ℝ)+1)) = ε := by dsimp [r]; field_simp
  have hrL : (L:ℝ)*r ≤ ε/2 := by nlinarith
  obtain ⟨A,B,hA,hB,hvolr⟩ := hvol r hr
  let a := (B+1)/2
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have haa : 2*a-B = 1 := by dsimp [a]; ring
  obtain ⟨I,hI⟩ := hw a ha
  let c := A*(ε/2)^2*Real.exp (-2*a*r)
  have hc : 0 < c := by dsimp only [c]; positivity
  refine ⟨max 0 (I/c+1),le_max_left _ _,?_⟩
  intro i x hx
  let g := gs i
  change |g x| < ε
  have hi := (memLp_two_iff_integrable_sq (hI i).1.aestronglyMeasurable).mp (hI i).1
  by_contra hbad
  have hgx : ε ≤ |g x| := le_of_not_gt hbad
  have hball (y : X) (hy : y ∈ Metric.ball x r) :
      (ε/2)^2*Real.exp (2*a*(dist x o-r)) ≤ (g y*Real.exp (a*dist y o))^2 := by
    have hxy : dist x y < r := by simpa only [Metric.mem_ball,dist_comm] using hy
    have hl := (hg i).dist_le_mul x y
    rw [Real.dist_eq] at hl
    have hab : |g x|-|g y| ≤ |g x-g y| := abs_sub_abs_le_abs_sub _ _
    have hgy : ε/2 ≤ |g y| := by
      have hh := mul_le_mul_of_nonneg_left hxy.le L.2
      have H := hab.trans (hl.trans (hh.trans hrL))
      have H' : ε-ε/2 ≤ |g y| := (sub_le_iff_le_add'.mpr (hgx.trans (sub_le_iff_le_add.mp H)))
      convert H' using 1
      ring
    have hd : dist x o-r ≤ dist y o := by linarith [dist_triangle x y o]
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd (show 0 ≤ 2*a by positivity))
    have hs : (ε/2)^2 ≤ (g y)^2 := by
      have hh := pow_le_pow_left₀ (by positivity : 0 ≤ ε/2) hgy 2
      simpa only [sq_abs] using hh
    rw [mul_pow,sq_exp_eq]
    have heq : 2*(a*dist y o) = 2*a*dist y o := by ring
    rw [heq]
    exact mul_le_mul hs he (Real.exp_pos _).le (sq_nonneg _)
  have hlocal := setIntegral_ge_of_const_le_real Metric.isOpen_ball.measurableSet
    (hfin _ Metric.isBounded_ball).ne hball hi.integrableOn
  have htot : (∫ y in Metric.ball x r,(g y*Real.exp (a*dist y o))^2 ∂m) ≤ I := (integral_mono_measure m.restrict_le_self (ae_of_all _ (fun y => sq_nonneg (g y*Real.exp (a*dist y o)))) hi).trans (hI i).2
  have hv := mul_le_mul_of_nonneg_left (hvolr x)
    (show 0 ≤ (ε/2)^2*Real.exp (2*a*(dist x o-r)) by positivity)
  have heq : (ε/2)^2*Real.exp (2*a*(dist x o-r))*(A*Real.exp (-B*dist x o)) = c*Real.exp (dist x o) := by
    dsimp only [c]
    rw [show 2*a*(dist x o-r) = -2*a*r+2*a*dist x o by ring,Real.exp_add]
    calc
      _ = A*(ε/2)^2*Real.exp (-2*a*r)*(Real.exp (2*a*dist x o)*Real.exp (-B*dist x o)) := by ring
      _ = _ := by
        rw [← Real.exp_add,show 2*a*dist x o+-B*dist x o = dist x o by
          calc
            _ = (2*a-B)*dist x o := by ring
            _ = _ := by rw [haa,one_mul]]
  rw [heq] at hv
  have hupper : c*Real.exp (dist x o) ≤ I := by
    exact hv.trans (hlocal.trans htot)
  have hlarge : I/c+1 < dist x o := (le_max_right _ _).trans_lt hx
  have hd := Real.add_one_le_exp (dist x o)
  have hiC : I/c*c = I := div_mul_cancel₀ _ hc.ne'
  have hstrict := mul_lt_mul_of_pos_left hlarge hc
  have hlow := mul_le_mul_of_nonneg_left hd hc.le
  nlinarith

end WeakHessian

end
end InlinedFile125

end OAI
