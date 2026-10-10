import OAI.Dynamics.StandardMap.CurveCompose

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
def pairTransfer (a : ℝ) (v : CurvePlane) : CurvePlane := (a*v.1-v.2,v.1)
lemma pairTransfer_bound (k : ℝ) (hk : 0≤k) (x : ℝ) (v : CurvePlane) :
    ‖pairTransfer (potential k x) v‖≤growthBase k*‖v‖ := by
  rw [Prod.norm_def]
  have hM:=growthBase_ge_four k hk
  have h1:=norm_fst_le v
  have h2:=norm_snd_le v
  change |v.1|≤‖v‖ at h1
  change |v.2|≤‖v‖ at h2
  change max |potential k x*v.1-v.2| |v.1|≤_
  refine max_le ?_ (h1.trans ?_)
  · calc
      _ ≤ |potential k x| *|v.1|+|v.2| := by simpa only [abs_mul] using abs_sub (potential k x*v.1) v.2
      _ ≤ |potential k x| *‖v‖+‖v‖ := add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2
      _ ≤ _ := by nlinarith [potential_bound k x hk,norm_nonneg v]
  · exact le_mul_of_one_le_left (norm_nonneg _) (by linarith)
lemma pairTransfer_add (a : ℝ) (v w : CurvePlane) :
    pairTransfer a (v+w)=pairTransfer a v+pairTransfer a w := by ext <;> simp [pairTransfer] ; ring
lemma pairTransfer_sub (a : ℝ) (v w : CurvePlane) :
    pairTransfer a (v-w)=pairTransfer a v-pairTransfer a w := by ext <;> simp [pairTransfer] ; ring
lemma pairTransfer_parameter (a b : ℝ) (v : CurvePlane) :
    ‖pairTransfer a v-pairTransfer b v‖≤|a-b| *‖v‖ := by
  have he:pairTransfer a v-pairTransfer b v=((a-b)*v.1,0) := by ext <;> simp [pairTransfer] ; ring
  rw [he,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,abs_zero,max_eq_left (abs_nonneg _),abs_mul]
  exact mul_le_mul_of_nonneg_left (norm_fst_le v) (abs_nonneg _)
noncomputable def liftCurveVelocity (k : ℝ) (g v : ℝ → CurvePlane) (t : ℝ) : CurvePlane :=
  pairTransfer (potential k (g t).1) (v t)
lemma liftCurve_hasDeriv (k : ℝ) (g v : ℝ → CurvePlane)
    (hv : ∀t,HasDerivAt g (v t) t) (t : ℝ) :
    HasDerivAt ((liftStep k) ∘ g) (liftCurveVelocity k g v t) t := by
  have h1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hv t)
  have h2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hv t)
  convert! (((hasDerivAt_phi k (g t).1).comp t h1).sub h2).prodMk h1 using 1
lemma liftCurve_velocity_continuous (k : ℝ) (g v : ℝ → CurvePlane)
    (hg : Continuous g) (hv : Continuous v) : Continuous (liftCurveVelocity k g v) := by
  unfold liftCurveVelocity pairTransfer potential
  fun_prop
lemma liftCurve_variation (k ε : ℝ) (hk : 0≤k) (hε : 0≤ε) (hsmall : 2*Real.pi*ε≤1)
    (g : ControlledCurve ε) {s t : ℝ} (hs : s∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    ‖liftCurveVelocity k g.map g.velocity s-liftCurveVelocity k g.map g.velocity t‖≤
      2*growthBase k*ε*|s-t| := by
  have hM:0≤growthBase k := (growthBase_ge_four k hk).trans' (by norm_num)
  have hd:‖g.map s-g.map t‖≤ε*|s-t| := curve_displacement _ _ g.hasDeriv _ g.speed ht hs
  have hp:|potential k (g.map s).1-potential k (g.map t).1|≤
      2*Real.pi*growthBase k*‖g.map s-g.map t‖ := by
    exact (potential_lipschitz k _ _ hk).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le (g.map s-g.map t)) (by positivity))
  calc
    _ ≤ ‖pairTransfer (potential k (g.map s).1) (g.velocity s)-
      pairTransfer (potential k (g.map s).1) (g.velocity t)‖+
      ‖pairTransfer (potential k (g.map s).1) (g.velocity t)-
      pairTransfer (potential k (g.map t).1) (g.velocity t)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ growthBase k*‖g.velocity s-g.velocity t‖+
      |potential k (g.map s).1-potential k (g.map t).1| *‖g.velocity t‖ := by
      rw [← pairTransfer_sub]
      exact add_le_add (pairTransfer_bound k hk _ _) (pairTransfer_parameter _ _ _)
    _ ≤ growthBase k*(ε*|s-t|)+(2*Real.pi*growthBase k*(ε*|s-t|))*ε := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (g.variation s hs t ht) hM
      · exact mul_le_mul (hp.trans (mul_le_mul_of_nonneg_left hd (by positivity)))
          (g.speed t ht) (norm_nonneg _) (by positivity)
    _ ≤ _ := by
      have h:=mul_le_mul_of_nonneg_right hsmall
        (show 0≤growthBase k*ε*|s-t| by positivity)
      nlinarith
end StandardMapEntropy

end OAI
