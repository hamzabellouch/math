import Mathlib
import OAI.Probability.JammingConcavity.RowWeightedStep

namespace OAI

/-! Row Quadratic Terminal Limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
open Filter
open Finset Set
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open scoped BigOperators Classical
open scoped ENNReal NNReal Topology BigOperators Matrix MatrixOrder
open scoped BigOperators RealInnerProductSpace
open scoped NNReal Topology BigOperators
open scoped NNReal BigOperators RealInnerProductSpace
open scoped ENNReal NNReal BigOperators MatrixOrder
open scoped MatrixOrder
open scoped NNReal
open scoped BigOperators NNReal
open scoped NNReal ENNReal BigOperators Topology
open scoped Topology ENNReal NNReal
open scoped Matrix.Norms.L2Operator MatrixOrder Topology NNReal ENNReal BigOperators
open scoped Topology ENNReal NNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped Topology NNReal ENNReal BigOperators
open scoped BigOperators NNReal Topology
open scoped Topology NNReal ENNReal BigOperators MatrixOrder
open scoped Topology NNReal ENNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators NNReal
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace MicroscopicJamming
lemma row_quadratic_operator_limit {u : ℝ → ℝ} {v : ℕ → ℝ → ℝ} {K a T : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hu : Measurable u) (hv : ∀ n,Measurable (v n))
    (hb : ∀ n x,|v n x| ≤ K*(1+x^2)) (hup : ∀ n x,v n x ≤ 0)
    (hlim : ∀ x,Tendsto (fun n => v n x) atTop (𝓝 (u x))) (x : ℝ) :
    Tendsto (fun n => gaussianRowOperator a T (v n) x) atTop (𝓝 (gaussianRowOperator a T u x)) := by
  have hup' (y : ℝ) : u y ≤ 0 := le_of_tendsto (hlim y) (Eventually.of_forall (fun n => hup n y))
  have hi : Integrable (fun z => K*(1+(x+Real.sqrt T*z)^2)) (gaussianReal 0 1) :=
    heat_affine_quadratic_integrable (v:=fun y => K*(1+y^2)) (by fun_prop) ⟨K,hK,fun y => by
      rw [abs_of_nonneg (by positivity)]
      have hh : 1+y^2 ≤ (1+|y|)^2 := by nlinarith [abs_nonneg y,sq_abs y]
      exact mul_le_mul_of_nonneg_left hh hK⟩ _ _
  by_cases hz : a=0
  · simp only [gaussianRowOperator,hz,ite_true]
    exact tendsto_integral_of_dominated_convergence (fun z => K*(1+(x+Real.sqrt T*z)^2))
      (fun n => ((hv n).comp (by fun_prop)).aestronglyMeasurable) hi
      (fun n => Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hb n (x+Real.sqrt T*z)))
      (Eventually.of_forall (fun z => hlim _))
  · have heb (n : ℕ) (y : ℝ) : ‖Real.exp (a*v n y)‖ ≤ 1 := by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_le_one_iff]
      exact mul_nonpos_of_nonneg_of_nonpos ha (hup n y)
    have he : Tendsto (fun n => gaussianHeat (fun y => Real.exp (a*v n y)) T x) atTop
        (𝓝 (gaussianHeat (fun y => Real.exp (a*u y)) T x)) := by
      exact tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
        (fun n => (Real.measurable_exp.comp (measurable_const.mul ((hv n).comp (by fun_prop)))).aestronglyMeasurable) (integrable_const 1) (fun n => Eventually.of_forall (fun z => heb n _))
        (Eventually.of_forall (fun z => (Real.continuous_exp.tendsto _).comp ((hlim (x+Real.sqrt T*z)).const_mul a)))
    have hui : Integrable (fun z => Real.exp (a*u (x+Real.sqrt T*z))) (gaussianReal 0 1) := by
      apply (integrable_const (1:ℝ)).mono' (Real.measurable_exp.comp (measurable_const.mul (hu.comp (by fun_prop)))).aestronglyMeasurable
      filter_upwards [] with z
      change ‖Real.exp (a*u (x+Real.sqrt T*z))‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_le_one_iff]
      exact mul_nonpos_of_nonneg_of_nonpos ha (hup' _)
    have hp : 0<gaussianHeat (fun y => Real.exp (a*u y)) T x := integral_exp_pos hui
    simpa only [gaussianRowOperator,hz,ite_false] using (he.log hp.ne').const_mul (1/a)
lemma row_quadratic_composition_limit {u : ℝ → ℝ} {v : ℕ → ℝ → ℝ} {A Q : ℝ} {C : ℕ → ℝ}
    (hQ : 0<Q) (hv : ∀ n,RowAnalyticTerminal (v n) A 0 (C n) 0 Q)
    (hlim : ∀ x,Tendsto (fun n => v n x) atTop (𝓝 (u x)))
    (rs : List (ℝ × ℝ)) (hrs : ∀ r∈rs,0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hT : gaussianStepTime rs ≤ Q) :
    ∀ x,Tendsto (fun n => gaussianRowComposition rs (v n) x) atTop (𝓝 (gaussianRowComposition rs u x)) := by
  induction rs with
  | nil => exact hlim
  | cons r rs ih =>
    have hr := hrs r (by simp)
    have htail : ∀ r∈rs,0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2 := fun r hr => hrs r (List.mem_cons_of_mem _ hr)
    have ht : gaussianStepTime rs ≤ Q := by
      have hh : r.2+gaussianStepTime rs ≤ Q := by simpa [gaussianStepTime] using hT
      linarith [hr.2.2]
    have hlimit := ih htail ht
    have hbound (n : ℕ) := gaussian_step_bounds (v n) A 0 (C n) 0 Q hQ (hv n) rs htail ht
    have hm (n : ℕ) : Measurable (gaussianRowComposition rs (v n)) := (hbound n).1.continuous.measurable
    have hmu : Measurable (gaussianRowComposition rs u) := measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.mpr hlimit)
    have hA : 0 ≤ A := (hv 0).2.1
    have hb (n : ℕ) (x : ℝ) : |gaussianRowComposition rs (v n) x| ≤ (A*(1+Q))*(1+x^2) := by
      have hh := (hbound n).2.2 x
      rw [abs_of_nonpos hh.1.2]
      have hh' : A*(1+x^2+gaussianStepTime rs) ≤ (A*(1+Q))*(1+x^2) := by
        nlinarith [mul_nonneg (mul_nonneg hA hQ.le) (sq_nonneg x),mul_le_mul_of_nonneg_left ht hA]
      linarith [hh.1.1]
    intro x
    exact row_quadratic_operator_limit (by positivity) hr.1 hmu hm hb (fun n y => ((hbound n).2.2 y).1.2) hlimit x
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma row_hinge_profile_conclusions {β Q : ℝ} (hβ : 0<β) (hQ : 0 ≤ Q) :
    RowProfileConclusions (fun z => -β*rowQuadraticHinge z) Q := by
  rcases eq_or_lt_of_le hQ with h0 | hQ
  · subst Q; exact rowProfile_zero _
  let R (n : ℕ) := (n:ℝ)+1
  let d (n : ℕ) := 1/R n
  have hR (n : ℕ) : 0<R n := by dsimp [R]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hd (n : ℕ) : 0<d n := by dsimp [d]; positivity
  have hd1 (n : ℕ) : d n ≤ 1 := by
    dsimp [d]
    apply (div_le_one (hR n)).mpr
    dsimp [R]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hdlim : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)
  choose v C H hv hvb hvc herr using fun n => row_hinge_analytic_approx_one (Q:=Q) hβ (hR n)
    (sq_pos_of_pos (hd n)) (show (d n)^2 ≤ 1 by nlinarith [hd n,hd1 n])
  let e (n : ℕ) := β*d n+2*β*(d n)^2
  have hen (n : ℕ) : 0 ≤ e n := by dsimp [e]; positivity
  have helim : Tendsto e atTop (𝓝 0) := by
    simpa only [zero_pow (by omega : (2:ℕ)≠0),mul_zero,add_zero] using (hdlim.const_mul β).add ((hdlim.pow 2).const_mul (2*β))
  have heq (n : ℕ) : β*R n*(d n)^2+2*β/(R n)^2=e n := by
    dsimp [d,e]
    field_simp
  have herror (n : ℕ) (x : ℝ) : |v n x-(-β*rowQuadraticHinge x)| ≤ e n*(1+x^2)^2 := by
    simpa only [heq n] using herr n x
  have hlim (x : ℝ) : Tendsto (fun n => v n x) atTop (𝓝 (-β*rowQuadraticHinge x)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (g:=fun n => e n*(1+x^2)^2) (fun _ => dist_nonneg) (fun n => by rw [Real.dist_eq]; exact herror n x)
    simpa only [zero_mul] using helim.mul_const ((1+x^2)^2)
  let L := 8*((3*β)*(1+Q))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let K := Real.exp ((10+8*L)*Q)
  have hbound (rs : List (ℝ × ℝ)) (hrs : ∀ r∈rs,0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
      (ht : gaussianStepTime rs=Q) (n m : ℕ) :
      |gaussianRowComposition rs (v n) 0-gaussianRowComposition rs (v m) 0| ≤ (e n+e m)*K := by
    apply row_step_weighted_terminal hQ (hv n) (hv m) hL (add_nonneg (hen n) (hen m)) hrs ht
    · intro t ht' x; simpa only [abs_zero,zero_add] using row_step_concave_slope hQ (hv n) hrs ht ht' x
    · intro t ht' x; simpa only [abs_zero,zero_add] using row_step_concave_slope hQ (hv m) hrs ht ht' x
    · intro x
      have hh := abs_sub_le (v n x) (-β*rowQuadraticHinge x) (v m x)
      rw [abs_sub_comm (-β*rowQuadraticHinge x)] at hh
      nlinarith [herror n x,herror m x]
  have hfinite (rs : List (ℝ × ℝ)) (hrs : ∀ r∈rs,0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) (ht : gaussianStepTime rs=Q) :=
    row_quadratic_composition_limit hQ hv hlim rs hrs ht.le 0
  apply row_terminal_profile_passage hQ hv hvb hvc
    (show Tendsto (fun n => e n*K) atTop (𝓝 0) by simpa only [zero_mul] using helim.mul_const K) _ hfinite
  intro rs hrs ht n
  have hh := le_of_tendsto_of_tendsto ((tendsto_const_nhds.sub (hfinite rs hrs ht)).abs)
    ((tendsto_const_nhds.add helim).mul_const K) (Eventually.of_forall (hbound rs hrs ht n))
  simpa only [add_zero,abs_sub_comm] using hh
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
 

theorem rowNonsmoothConcavity : RowNonsmoothConcavityStatement := by
  intro u hu Q hQ
  rcases hu with ⟨hc,L,hL,hlip⟩ | ⟨β,hβ,rfl⟩
  · exact row_lipschitz_profile_conclusions hc hL hlip hQ
  · exact row_hinge_profile_conclusions hβ hQ
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
 

theorem rowConcavityMain : RowConcavityMainStatement := by
  constructor
  · intro u A B C κ Q hQ hu hc p q hp hq θ hθ hθ1
    exact rowProfileValue_smooth_concave hQ hu hc p q hp hq hθ hθ1
  · exact rowNonsmoothConcavity
end MicroscopicJamming

end

end OAI
