import Mathlib
import OAI.Probability.LogConcave.Sampling.PrimitiveExpectedField
import OAI.Probability.LogConcave.Sampling.TerminalTransportConstant

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped NNReal

lemma gaussian_affine_norm_moment (d : ℕ) (a : ℝ) :
    Integrable (fun z : Point d => (a+‖z‖)^2) (stdGaussian (Point d)) ∧
      (∫z : Point d,(a+‖z‖)^2 ∂stdGaussian (Point d))≤2*a^2+2*d := by
  have h : MemLp (fun z : Point d => a+‖z‖) 2 (stdGaussian (Point d)) :=
    (memLp_const a).add (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).norm
  have hsq : Integrable (fun z : Point d => ‖z‖^2) (stdGaussian (Point d)) := by
    simpa only [id_eq] using (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).integrable_norm_pow
      (by norm_num : (2:ℕ)≠0)
  refine ⟨h.integrable_sq,?_⟩
  calc
    _ ≤ ∫z : Point d,2*a^2+2*‖z‖^2 ∂stdGaussian (Point d) := by
      apply integral_mono h.integrable_sq ((integrable_const _).add (hsq.const_mul 2))
      intro z
      change (a+‖z‖)^2≤2*a^2+2*‖z‖^2
      nlinarith [sq_nonneg (a-‖z‖)]
    _ = _ := by rw [integral_add (integrable_const _) (hsq.const_mul _),
      integral_const,probReal_univ,one_smul,integral_const_mul,stdGaussian_sq_norm]

lemma gaussian_growth_sq_moment {d e : ℕ} {f : Point d → Point e} (hf : Continuous f)
    {K a : ℝ} (hK : 0≤K) (ha : 0≤a) (hbound : ∀z,‖f z‖≤K*(a+‖z‖)) :
    Integrable (fun z => ‖f z‖^2) (stdGaussian (Point d)) ∧
      (∫z,‖f z‖^2 ∂stdGaussian (Point d))≤K^2*(2*a^2+2*d) := by
  have hg := (gaussian_affine_norm_moment d a).1.const_mul (K^2)
  have hb (z : Point d) : ‖f z‖^2≤K^2*(a+‖z‖)^2 := by
    rw [←mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (add_nonneg ha (norm_nonneg z)))).2 (hbound z)
  have hi : Integrable (fun z => ‖f z‖^2) (stdGaussian (Point d)) := by
    apply hg.mono' ((hf.norm.pow 2).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,Pi.pow_apply,abs_sq] using hb z)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫z : Point d,K^2*(a+‖z‖)^2 ∂stdGaussian (Point d) := integral_mono hi hg hb
    _ = K^2*(∫z : Point d,(a+‖z‖)^2 ∂stdGaussian (Point d)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (gaussian_affine_norm_moment d a).2 (sq_nonneg K)

lemma conditionalFieldMean_at_zero {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) (y : Point d) :
    conditionalFieldMean F x r 0 y=primitiveExpectedField F x r := by
  have he : conditionalPotential F x r 0 y=primitivePotential F x r := by
    funext z
    simp [conditionalPotential,primitivePotential]
  simp only [conditionalFieldMean,he,primitiveExpectedField]

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
  (hl : (lam:ℝ)*r^2≤1/2)

include hF hr hl in
lemma terminal_mean_error (z : Point d) :
    ‖primitiveField F x r z-primitiveExpectedField F x r‖≤
      2*((lam:ℝ)*r)*(Real.pi*Real.sqrt d+‖z‖+r*‖primitiveField F x r 0‖) := by
  have he := conditionalFieldMean_center_zero_bound hF x hr hl (by norm_num : (0:ℝ)≤0)
    (by norm_num : (0:ℝ)<1) (0:Point d)
  rw [conditionalFieldMean_at_zero,norm_zero,add_zero] at he
  have hc := (primitiveField_lipschitz hF x hr).dist_le_mul z 0
  simp only [dist_eq_norm,sub_zero,NNReal.coe_mul,NNReal.coe_mk] at hc
  have hh := (norm_sub_le_norm_sub_add_norm_sub (primitiveField F x r z)
    (primitiveField F x r 0) (primitiveExpectedField F x r)).trans
    (add_le_add hc (by simpa only [norm_sub_rev] using he))
  have hz := mul_nonneg (mul_nonneg lam.coe_nonneg hr) (norm_nonneg z)
  nlinarith

include hF hr hl in

theorem terminal_mean_squared_error :
    Integrable (fun z => ‖primitiveField F x r z-primitiveExpectedField F x r‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖primitiveField F x r z-primitiveExpectedField F x r‖^2 ∂stdGaussian (Point d))≤
        (2*((lam:ℝ)*r))^2*(2*(Real.pi*Real.sqrt d+r*‖primitiveField F x r 0‖)^2+2*d) := by
  apply gaussian_growth_sq_moment ((primitiveField_contDiff hF x r).continuous.sub continuous_const)
    (by positivity) (by positivity)
  intro z
  convert terminal_mean_error hF x hr hl z using 1
  first | rfl | ring

theorem terminal_sample_squared_error :
    (stdGaussian (Point d)).map (fullProbabilityFlow hF x hr hl 1)=gibbs (primitivePotential F x r) ∧
    Integrable (fun z => ‖fullProbabilityFlow hF x hr hl 1 z-(z-r • primitiveField F x r z)‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖fullProbabilityFlow hF x hr hl 1 z-(z-r • primitiveField F x r z)‖^2 ∂stdGaussian (Point d))≤
        (terminalTransportConstant*((lam:ℝ)*r^2))^2*
          (2*(Real.pi*Real.sqrt d+2*r*‖primitiveField F x r 0‖)^2+2*d) := by
  refine ⟨fullProbabilityFlow_pushforward hF x hr hl,?_⟩
  apply gaussian_growth_sq_moment
    ((fullProbabilityFlow_lipschitz hF x hr hl ⟨by norm_num,le_rfl⟩).continuous.sub
      (continuous_id.sub ((primitiveField_contDiff hF x r).continuous.const_smul r)))
    (mul_nonneg terminalTransportConstant_pos.le (by positivity)) (by positivity)
  intro z
  convert terminal_transport_error hF x hr hl z using 1 <;> first | rfl | ring
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped NNReal

lemma gaussian_lipschitz_memLp {d e : ℕ} {f : Point d → Point e} {K : ℝ≥0}
    (hf : LipschitzWith K f) : MemLp f 2 (stdGaussian (Point d)) := by
  have hh : LipschitzWith K (fun z => f z-f 0) :=
    LipschitzWith.of_dist_le_mul (fun z w => by simpa using hf.dist_le_mul z w)
  have hz : (fun z => f z-f 0) 0=0 := sub_self _
  have he := hh.comp_memLp hz (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d)))
  have hp : MemLp (fun z => f z-f 0+f 0) 2 (stdGaussian (Point d)) :=
    he.add (memLp_const (f 0))
  simpa only [sub_add_cancel] using hp

lemma gaussian_scaled_growth_sq_moment {d e : ℕ} {f : Point d → Point e} (hf : Continuous f)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hbound : ∀z,‖f z‖≤a+b*‖z‖) :
    Integrable (fun z => ‖f z‖^2) (stdGaussian (Point d)) ∧
      (∫z,‖f z‖^2 ∂stdGaussian (Point d))≤2*a^2+2*b^2*d := by
  have h : MemLp (fun z : Point d => a+b*‖z‖) 2 (stdGaussian (Point d)) :=
    (memLp_const a).add ((IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).norm.const_mul b)
  have hsq : Integrable (fun z : Point d => ‖z‖^2) (stdGaussian (Point d)) := by
    simpa only [id_eq] using (IsGaussian.memLp_two_id (μ:=stdGaussian (Point d))).integrable_norm_pow
      (by norm_num : (2:ℕ)≠0)
  have hdom : Integrable (fun z : Point d => 2*a^2+2*b^2*‖z‖^2) (stdGaussian (Point d)) :=
    (integrable_const _).add (hsq.const_mul _)
  have hb' (z : Point d) : ‖f z‖^2≤2*a^2+2*b^2*‖z‖^2 := by
    have hh := (sq_le_sq₀ (norm_nonneg _) (add_nonneg ha (mul_nonneg hb (norm_nonneg z)))).2 (hbound z)
    nlinarith [sq_nonneg (a-b*‖z‖)]
  have hi : Integrable (fun z => ‖f z‖^2) (stdGaussian (Point d)) :=
    hdom.mono' (hf.norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs,abs_sq] using hb' z)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫z : Point d,2*a^2+2*b^2*‖z‖^2 ∂stdGaussian (Point d) := integral_mono hi hdom hb'
    _ = _ := by rw [integral_add (integrable_const _) (hsq.const_mul _),integral_const,
      probReal_univ,one_smul,integral_const_mul,stdGaussian_sq_norm]

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
  (hl : (lam:ℝ)*r^2≤1/2)

include hF hr hl in

lemma probabilityFlow_initial_displacement (z : Point d) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    ‖fullProbabilityFlow hF x hr hl t z-z‖≤terminalTransportConstant*
      (r*‖primitiveField F x r 0‖+((lam:ℝ)*r^2)*(Real.pi*Real.sqrt d+‖z‖)) := by
  let c := primitiveField F x r 0
  let D := Real.pi*Real.sqrt d+‖z‖+2*r*‖c‖
  let q := (lam:ℝ)*r^2
  let ε := 2*q*D
  let B := |gronwallBound 0 (Real.pi^2+1) 1 1|+1
  let f (s : ℝ) := fullProbabilityFlow hF x hr hl s z
  let g (s : ℝ) := z-s • (r • c)
  have hv (s : ℝ) : LipschitzWith ⟨Real.pi^2+1,by positivity⟩ (fullProbabilityVelocity F x r s) := by
    apply (fullProbabilityVelocity_lipschitz hF x hr hl s).weaken
    change (Real.pi^2/2)*(lam:ℝ)*r^2≤Real.pi^2+1
    have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0≤Real.pi^2/2)
    nlinarith [sq_nonneg Real.pi]
  have hf : Continuous f := fullProbabilityFlow_time_continuous hF x hr hl z
  have hfd : ∀s∈Icc (0:ℝ) 1,HasDerivWithinAt f
      (fullProbabilityVelocity F x r s (f s)) (Icc 0 1) s := by
    intro s hs
    exact GlobalODE.flow_deriv (a:=0) (b:=1)
      (fun s _ => fullProbabilityVelocity_lipschitz hF x hr hl s)
      (fullProbabilityVelocity_continuous hF x hr hl) ⟨0,le_rfl,by norm_num⟩ z s hs
  have hgd (s : ℝ) : HasDerivAt g (-r • c) s := by
    convert (hasDerivAt_const s z).sub ((hasDerivAt_id s).smul_const (r • c)) using 1 <;> first | rfl | simp
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hh := dist_le_of_approx_trajectories_ODE hv hf.continuousOn
    (GlobalODE.right_deriv hfd) (εf:=0) (fun s _ => by simp) hg.continuousOn
    (fun s _ => (hgd s).hasDerivWithinAt) (εg:=ε)
    (fun s hs => probability_affine_residual hF x hr hl z hs)
    (δ:=0) (by simp only [f,g,fullProbabilityFlow_initial,Function.id_def,zero_smul,sub_zero,dist_self,le_refl]) t ht
  simp only [zero_add,sub_zero] at hh
  rw [GlobalODE.gronwallBound_zero_linear] at hh
  have hmono : gronwallBound 0 (Real.pi^2+1) 1 t≤B :=
    ((gronwallBound_mono (by norm_num) (by norm_num) (by positivity)) ht.2).trans
      (by dsimp [B]; linarith [le_abs_self (gronwallBound 0 (Real.pi^2+1) 1 1)])
  have he : dist (f t) (g t)≤ε*B := hh.trans (mul_le_mul_of_nonneg_left hmono (by dsimp [ε,q,D]; positivity))
  have hgz : dist (g t) z≤r*‖c‖ := by
    have he : g t-z=-(t • (r • c)) := by dsimp [g]; abel
    rw [dist_eq_norm,he,norm_neg,norm_smul,norm_smul,Real.norm_eq_abs,
      Real.norm_eq_abs,abs_of_nonneg ht.1,abs_of_nonneg hr]
    exact mul_le_of_le_one_left (by positivity) ht.2
  have ht' := (dist_triangle (f t) (g t) z).trans (add_le_add he hgz)
  change dist (f t) z≤_
  apply ht'.trans
  have hB : 0≤B := by dsimp [B]; positivity
  have hq : 0≤q := by dsimp [q]; positivity
  have hc : 0≤r*‖c‖ := by positivity
  have hbase : 0≤Real.pi*Real.sqrt d+‖z‖ := by positivity
  have habs := mul_le_mul_of_nonneg_right hl (show 0≤2*B*(r*‖c‖) from by positivity)
  dsimp [ε,D,q,B,c,terminalTransportConstant] at habs ⊢
  nlinarith [mul_nonneg hq hbase]

include hF hr hl in
lemma probabilityFlow_initial_rms {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    Integrable (fun z => ‖z-fullProbabilityFlow hF x hr hl t z‖^2) (stdGaussian (Point d)) ∧
    (∫z,‖z-fullProbabilityFlow hF x hr hl t z‖^2 ∂stdGaussian (Point d))≤
      2*(terminalTransportConstant*(r*‖primitiveField F x r 0‖+(lam:ℝ)*r^2*Real.pi*Real.sqrt d))^2+
      2*(terminalTransportConstant*((lam:ℝ)*r^2))^2*d := by
  apply gaussian_scaled_growth_sq_moment
    (continuous_id.sub (fullProbabilityFlow_lipschitz hF x hr hl ht).continuous)
    (mul_nonneg terminalTransportConstant_pos.le (by positivity))
    (mul_nonneg terminalTransportConstant_pos.le (by positivity))
  intro z
  simp only [Pi.sub_apply,id_eq]
  rw [norm_sub_rev]
  convert probabilityFlow_initial_displacement hF x hr hl z ht using 1
  first | rfl | ring
end LogConcaveSampling

end

end

end

end OAI
