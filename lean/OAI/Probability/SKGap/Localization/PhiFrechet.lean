import Mathlib
import OAI.Probability.SKGap.Localization.ScalarParametersJoined
import OAI.Probability.SKGap.Localization.PhiRatio

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace SKGap.Stein

abbrev Triple := ℝ × (ℝ × ℝ)
def eval3 (F : ℝ→ℝ→ℝ→ℝ) (x : Triple) : ℝ := F x.1 x.2.1 x.2.2

def grad2 (a b : ℝ) : (ℝ×ℝ)→L[ℝ]ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ a).coprod (ContinuousLinearMap.toSpanSingleton ℝ b)
def grad3 (a b c : ℝ) : Triple→L[ℝ]ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ a).coprod (grad2 b c)

lemma grad2_eq (a b : ℝ) : grad2 a b=
    a • ContinuousLinearMap.fst ℝ ℝ ℝ+b • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  apply ContinuousLinearMap.ext; intro x; simp [grad2,ContinuousLinearMap.toSpanSingleton_apply,mul_comm]
lemma grad3_eq (a b c : ℝ) : grad3 a b c=
    a • ContinuousLinearMap.fst ℝ ℝ (ℝ×ℝ)+
      (grad2 b c).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ×ℝ)) := by
  apply ContinuousLinearMap.ext; intro x; simp [grad3,ContinuousLinearMap.toSpanSingleton_apply,mul_comm]

lemma continuous_grad2 : Continuous (fun x : ℝ×ℝ=>grad2 x.1 x.2) := by
  simp only [grad2_eq]; fun_prop
lemma continuous_grad3 : Continuous (fun x : Triple=>grad3 x.1 x.2.1 x.2.2) := by
  simp only [grad3_eq,grad2_eq]; fun_prop

lemma hasFDerivAt_of_three_partials (F Fz Fr Fa : ℝ→ℝ→ℝ→ℝ)
    (hz : ∀z r a,HasDerivAt (fun z=>F z r a) (Fz z r a) z)
    (hr : ∀z r a,HasDerivAt (fun r=>F z r a) (Fr z r a) r)
    (ha : ∀z r a,HasDerivAt (fun a=>F z r a) (Fa z r a) a)
    (cz : Continuous (eval3 Fz)) (cr : Continuous (eval3 Fr)) (ca : Continuous (eval3 Fa))
    (x : Triple) : HasFDerivAt (eval3 F) (grad3 (eval3 Fz x) (eval3 Fr x) (eval3 Fa x)) x := by
  have hpair (z : ℝ) (y : ℝ×ℝ) : HasFDerivAt (fun v : ℝ×ℝ=>F z v.1 v.2)
      (grad2 (Fr z y.1 y.2) (Fa z y.1 y.2)) y := by
    apply HasStrictFDerivAt.hasFDerivAt
    apply hasStrictFDerivAt_uncurry_coprod
      (f:=fun r a=>F z r a)
      (f₁:=fun r a=>ContinuousLinearMap.toSpanSingleton ℝ (Fr z r a))
      (f₂:=fun r a=>ContinuousLinearMap.toSpanSingleton ℝ (Fa z r a))
    · exact Eventually.of_forall fun v=>(hr z v.1 v.2).hasFDerivAt
    · exact Eventually.of_forall fun v=>(ha z v.1 v.2).hasFDerivAt
    · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp
        (cr.comp (continuous_const.prodMk continuous_id))).continuousAt
    · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp
        (ca.comp (continuous_const.prodMk continuous_id))).continuousAt
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod
    (f:=fun (z : ℝ) (v : ℝ×ℝ)=>F z v.1 v.2)
    (f₁:=fun z v=>ContinuousLinearMap.toSpanSingleton ℝ (Fz z v.1 v.2))
    (f₂:=fun z v=>grad2 (Fr z v.1 v.2) (Fa z v.1 v.2))
  · exact Eventually.of_forall fun v=>(hz v.1 v.2.1 v.2.2).hasFDerivAt
  · exact Eventually.of_forall fun v=>hpair v.1 v.2
  · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp cz).continuousAt
  · exact (continuous_grad2.comp (cr.prodMk ca)).continuousAt

lemma continuous_momentNum (p q : ℕ) (b : Bool) :
    Continuous (fun x : ℝ×ℝ=>momentNum p q b x.1 x.2) := by
  unfold momentNum
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  apply Continuous.mul
  · unfold weight; fun_prop
  · exact (continuous_hyper b).comp (continuous_snd.mul (continuous_fst.fst))

lemma continuous_moment (p q : ℕ) (b : Bool) : Continuous (eval3 (moment p q b)) := by
  change Continuous (fun x : Triple=>momentNum p q b (x.1-x.2.1) x.2.2/(Real.cosh x.1*Real.cosh x.2.1))
  exact ((continuous_momentNum p q b).comp
    ((continuous_fst.sub continuous_snd.fst).prodMk continuous_snd.snd)).div
      ((Real.continuous_cosh.comp continuous_fst).mul (Real.continuous_cosh.comp continuous_snd.fst))
      (fun x=>(mul_pos (Real.cosh_pos _) (Real.cosh_pos _)).ne')

lemma continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr fun z=>(SKGapCutoff.tanh_hasDerivAt z).continuousAt

namespace KernelExpr
lemma continuous_eval (f : KernelExpr) : Continuous (eval3 f.eval) := by
  induction f with
  | atom p q b => exact continuous_moment p q b
  | add f g hf hg => exact hf.add hg
  | scale c f hf => exact hf.const_mul c
  | tz f hf => exact (continuous_tanh.comp continuous_fst).mul hf
  | tr f hf => exact (continuous_tanh.comp continuous_snd.fst).mul hf

def gradient (f : KernelExpr) (x : Triple) : Triple→L[ℝ]ℝ :=
  grad3 (eval3 f.dz.eval x) (eval3 f.dr.eval x) (eval3 f.da.eval x)

lemma hasFDerivAt_eval (f : KernelExpr) (x : Triple) :
    HasFDerivAt (eval3 f.eval) (f.gradient x) x :=
  hasFDerivAt_of_three_partials f.eval f.dz.eval f.dr.eval f.da.eval
    f.hasDerivAt_z f.hasDerivAt_r f.hasDerivAt_a
    f.dz.continuous_eval f.dr.continuous_eval f.da.continuous_eval x
end KernelExpr

lemma grad3_norm (a b c : ℝ) : ‖grad3 a b c‖≤|a|+|b|+|c| := by
  apply (grad3 a b c).opNorm_le_bound (by positivity)
  intro x
  have hz := norm_fst_le x
  have hr := (norm_fst_le x.2).trans (norm_snd_le x)
  have ha := (norm_snd_le x.2).trans (norm_snd_le x)
  change |x.1*a+(x.2.1*b+x.2.2*c)|≤(|a|+|b|+|c|)*‖x‖
  calc
    _ ≤ |x.1*a|+(|x.2.1*b|+|x.2.2*c|) := (abs_add_le _ _).trans
      (add_le_add (le_refl _) (abs_add_le _ _))
    _ ≤ ‖x‖*|a|+(‖x‖*|b|+‖x‖*|c|) := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right hz (abs_nonneg _))
        (add_le_add (mul_le_mul_of_nonneg_right hr (abs_nonneg _))
          (mul_le_mul_of_nonneg_right ha (abs_nonneg _)))
    _ = _ := by ring

lemma grad3_sub (a b c d e f : ℝ) :
    grad3 a b c-grad3 d e f=grad3 (a-d) (b-e) (c-f) := by
  apply ContinuousLinearMap.ext; intro x
  simp only [grad3,grad2,sub_apply,ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  ring

def strip (R : ℝ) : Set Triple := {x | |x.2.2|≤R}
lemma convex_strip (R : ℝ) : Convex ℝ (strip R) := by
  intro x hx y hy a b ha hb hab
  change |a*x.2.2+b*y.2.2|≤R
  calc
    _ ≤ |a*x.2.2|+|b*y.2.2| := abs_add_le _ _
    _ = a*|x.2.2|+b*|y.2.2| := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
    _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = R := by rw [←add_mul,hab,one_mul]

namespace KernelExpr
lemma absolute_bound (f : KernelExpr) {R : ℝ} {x : Triple} (hx : x∈strip R) :
    |eval3 f.eval x|≤f.mass*Real.exp (R/2) := by
  exact (f.relative_bound x.1 x.2.1 x.2.2).trans (mul_le_mul_of_nonneg_left
    ((phi_le_exp ..).trans (Real.exp_le_exp.mpr (by dsimp [strip] at hx; linarith))) f.mass_nonneg)

def dBudget (f : KernelExpr) (R : ℝ) : ℝ :=
  (f.dz.mass+f.dr.mass+f.da.mass)*Real.exp (R/2)
lemma dBudget_nonneg (f : KernelExpr) (R : ℝ) : 0≤f.dBudget R := by
  unfold dBudget
  exact mul_nonneg (add_nonneg (add_nonneg f.dz.mass_nonneg f.dr.mass_nonneg) f.da.mass_nonneg)
    (Real.exp_pos _).le
lemma gradient_bound (f : KernelExpr) {R : ℝ} {x : Triple} (hx : x∈strip R) :
    ‖f.gradient x‖≤f.dBudget R := by
  apply (grad3_norm ..).trans
  exact (add_le_add (add_le_add (f.dz.absolute_bound hx) (f.dr.absolute_bound hx))
    (f.da.absolute_bound hx)).trans_eq (by dsimp [dBudget]; ring)

lemma lipschitz_strip (f : KernelExpr) {R : ℝ} {x y : Triple}
    (hx : x∈strip R) (hy : y∈strip R) :
    |eval3 f.eval y-eval3 f.eval x|≤f.dBudget R*‖y-x‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _=>(f.hasFDerivAt_eval z).hasFDerivWithinAt)
    (fun _ hz=>f.gradient_bound hz) (convex_strip R) hx hy

def ddBudget (f : KernelExpr) (R : ℝ) : ℝ :=
  f.dz.dBudget R+f.dr.dBudget R+f.da.dBudget R
lemma ddBudget_nonneg (f : KernelExpr) (R : ℝ) : 0≤f.ddBudget R :=
  add_nonneg (add_nonneg (f.dz.dBudget_nonneg R) (f.dr.dBudget_nonneg R)) (f.da.dBudget_nonneg R)

lemma gradient_lipschitz (f : KernelExpr) {R : ℝ} {x y : Triple}
    (hx : x∈strip R) (hy : y∈strip R) :
    ‖f.gradient y-f.gradient x‖≤f.ddBudget R*‖y-x‖ := by
  rw [gradient,gradient,grad3_sub]
  apply (grad3_norm ..).trans
  exact (add_le_add (add_le_add (f.dz.lipschitz_strip hx hy) (f.dr.lipschitz_strip hx hy))
    (f.da.lipschitz_strip hx hy)).trans_eq (by dsimp [ddBudget]; ring)
end KernelExpr

namespace RatioExpr
lemma continuous_eval (f : RatioExpr) : Continuous (eval3 f.eval) := by
  induction f with
  | constant c => exact continuous_const
  | kernel f =>
    have hp : Continuous (eval3 phi) := by simpa only [KernelExpr.eval,moment_base] using
      (KernelExpr.atom 0 0 false).continuous_eval
    exact f.continuous_eval.div hp (fun x=>(phi_pos x.1 x.2.1 x.2.2).ne')
  | add f g hf hg => exact hf.add hg
  | mul f g hf hg => exact hf.mul hg

def gradient (f : RatioExpr) (x : Triple) : Triple→L[ℝ]ℝ :=
  grad3 (eval3 (f.d .z).eval x) (eval3 (f.d .r).eval x) (eval3 (f.d .a).eval x)
lemma hasFDerivAt_eval (f : RatioExpr) (x : Triple) :
    HasFDerivAt (eval3 f.eval) (f.gradient x) x :=
  hasFDerivAt_of_three_partials f.eval (f.d .z).eval (f.d .r).eval (f.d .a).eval
    f.hasDerivAt_z f.hasDerivAt_r f.hasDerivAt_a
    (f.d .z).continuous_eval (f.d .r).continuous_eval (f.d .a).continuous_eval x

def dBudget (f : RatioExpr) : ℝ := (f.d .z).mass+(f.d .r).mass+(f.d .a).mass
lemma gradient_bound (f : RatioExpr) (x : Triple) : ‖f.gradient x‖≤f.dBudget := by
  exact (grad3_norm ..).trans (add_le_add
    (add_le_add ((f.d .z).bounded ..) ((f.d .r).bounded ..)) ((f.d .a).bounded ..))
lemma lipschitz_global (f : RatioExpr) (x y : Triple) :
    |eval3 f.eval y-eval3 f.eval x|≤f.dBudget*‖y-x‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z (_ : z∈(Set.univ:Set Triple))=>(f.hasFDerivAt_eval z).hasFDerivWithinAt)
    (fun z _=>f.gradient_bound z) convex_univ (Set.mem_univ x) (Set.mem_univ y)
def ddBudget (f : RatioExpr) : ℝ := (f.d .z).dBudget+(f.d .r).dBudget+(f.d .a).dBudget
lemma gradient_lipschitz (f : RatioExpr) (x y : Triple) :
    ‖f.gradient y-f.gradient x‖≤f.ddBudget*‖y-x‖ := by
  rw [gradient,gradient,grad3_sub]
  apply (grad3_norm ..).trans
  exact (add_le_add (add_le_add ((f.d .z).lipschitz_global x y) ((f.d .r).lipschitz_global x y))
    ((f.d .a).lipschitz_global x y)).trans_eq (by dsimp [ddBudget]; ring)
end RatioExpr
end SKGap.Stein

end
end

end OAI
