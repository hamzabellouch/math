import Mathlib
import OAI.Analysis.Conductivity.Variational.WeakHarmonicMean

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology
open scoped NNReal ENNReal

theorem analyticAt_of_factorial_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {a : E} {R M C : ℝ} (hR : 0<R) (hM : 0≤M) (hC : 0<C)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞)) f (Metric.ball a R))
    (hb : ∀ n : ℕ, ∀ x∈Metric.ball a R,
      ‖iteratedFDeriv ℝ n f x‖≤M*C^n*(n.factorial : ℝ)) : AnalyticAt ℝ f a := by
  let p : FormalMultilinearSeries ℝ E F := fun n => (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n f a
  let r : ℝ≥0 := ⟨min R (1/C)/2,by positivity⟩
  have hr : 0<(r : ℝ) := by change 0 < min R (1/C)/2; positivity
  have hrR : (r : ℝ)<R := by
    change min R (1/C)/2<R
    have := min_le_left R (1/C)
    linarith
  have hrC : (r : ℝ)<1/C := by
    change min R (1/C)/2<1/C
    have := min_le_right R (1/C)
    have : 0<1/C := by positivity
    linarith
  have hp (n : ℕ) : ‖p n‖≤M*C^n := by
    dsimp [p]
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ (n.factorial : ℝ)⁻¹*(M*C^n*(n.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (hb n a (by simpa using hR)) (by positivity)
      _ = M*C^n := by
        have hn : (n.factorial : ℝ)≠0 := by positivity
        field_simp
  have hrad : (r : ℝ≥0∞)≤p.radius := by
    apply p.le_radius_of_bound M
    intro n
    calc
      ‖p n‖*(r : ℝ)^n ≤ M*C^n*(r : ℝ)^n := mul_le_mul_of_nonneg_right (hp n) (by positivity)
      _ = M*(C*(r : ℝ))^n := by rw [mul_pow]; ring
      _ ≤ M*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity)
        (by nlinarith [(lt_div_iff₀ hC).mp hrC])) hM
      _ = M := mul_one _
  refine ⟨p,⟨r,⟨hrad,by exact_mod_cast hr,?_⟩⟩⟩
  intro y hy
  have hyr : ‖y‖<(r : ℝ) := by
    rw [Metric.eball_coe] at hy
    simpa using hy
  have hyR : ‖y‖<R := hyr.trans hrR
  have hyC : C*‖y‖<1 := by nlinarith [(lt_div_iff₀ hC).mp hrC]
  have hseg (t : ℝ) (ht : t∈Icc 0 1) : a+t•y∈Metric.ball a R := by
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt hyR
  have hdiff (n : ℕ) (t : ℝ) (ht : t∈Icc 0 1) : ContDiffAt ℝ (n+1) f (a+t•y) :=
    ((hf _ (hseg t ht)).contDiffAt (Metric.isOpen_ball.mem_nhds (hseg t ht))).of_le (by exact_mod_cast (show (↑n+1 : ℕ∞)≤⊤ from le_top))
  have he (n : ℕ) :
      ‖f (a+y)-∑ k∈Finset.range (n+1), p k (fun _ => y)‖≤
        M*((n+1 : ℕ) : ℝ)*(C*‖y‖)^(n+1) := by
    rw [map_add_eq_sum_add_integral_iteratedFDeriv (hdiff n)]
    simp only [p,smul_apply,add_sub_cancel_left]
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    have hi : ‖∫ t in (0:ℝ)..1, (1-t)^n •
        iteratedFDeriv ℝ (n+1) f (a+t•y) (fun _ => y)‖≤
        M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1) := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1)) ?_).trans (by simp)
      intro t ht
      have ht' : t∈Icc (0:ℝ) 1 := by
        simp only [uIoc_of_le zero_le_one,mem_Ioc] at ht
        exact ⟨ht.1.le,ht.2⟩
      rw [norm_smul,Real.norm_of_nonneg (pow_nonneg (by linarith [ht'.2]) _)]
      calc
          _ ≤ 1*(‖iteratedFDeriv ℝ (n+1) f (a+t•y)‖*‖y‖^(n+1)) :=
            mul_le_mul (pow_le_one₀ (by linarith [ht'.2]) (by linarith [ht'.1]))
              (by simpa using (iteratedFDeriv ℝ (n+1) f (a+t•y)).le_opNorm (fun _ => y))
              (norm_nonneg _) (by positivity)
          _ ≤ M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1) := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb (n+1) _ (hseg t ht')) (by positivity : 0≤‖y‖^(n+1))
    calc
      _ ≤ (n.factorial : ℝ)⁻¹*(M*C^(n+1)*((n+1).factorial : ℝ)*‖y‖^(n+1)) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by
        rw [Nat.factorial_succ,Nat.cast_mul,mul_pow]
        have hn : (n.factorial : ℝ)≠0 := by positivity
        field_simp
  have ht : Tendsto (fun n : ℕ => M*((n+1 : ℕ) : ℝ)*(C*‖y‖)^(n+1)) atTop (𝓝 0) := by
    have hh := (tendsto_self_mul_const_pow_of_lt_one (show 0≤C*‖y‖ by positivity) hyC).comp
      (tendsto_add_atTop_nat 1)
    simpa only [mul_zero,mul_assoc,Function.comp_apply] using hh.const_mul M
  have hlim : Tendsto (fun n : ℕ => ∑ k∈Finset.range (n+1), p k (fun _ => y)) atTop (𝓝 (f (a+y))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp_rw [norm_sub_rev]
    exact squeeze_zero (fun _ => norm_nonneg _) he ht
  apply (hasSum_iff_tendsto_nat_of_summable_norm ?_).mpr
  · exact (tendsto_add_atTop_iff_nat 1).mp hlim
  · apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => ?_) ((summable_geometric_of_lt_one (show 0≤C*‖y‖ by positivity) hyC).mul_left M)
    calc
      ‖p n (fun _ => y)‖≤‖p n‖*‖y‖^n := by simpa using (p n).le_opNorm (fun _ => y)
      _≤M*C^n*‖y‖^n := mul_le_mul_of_nonneg_right (hp n) (by positivity)
      _=M*(C*‖y‖)^n := by rw [mul_pow]; ring

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped Convolution

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

lemma RadialMeanOn.linearIsometry {f : WeylSpace → F} {a : WeylSpace} {R : ℝ}
    (hm : RadialMeanOn f a R) (L : F →ₗᵢ[ℝ] G) : RadialMeanOn (L ∘ f) a R := by
  intro s hs x hx
  change L (f x)=∫ y, (radialEta radialProfile s y) • L (f (x-y))
  simp_rw [←L.map_smul]
  rw [L.integral_comp_comm]
  exact congrArg L (hm s hs x hx)

lemma RadialMeanOn.iterated {f : WeylSpace → F} {a : WeylSpace} {R : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) (n : ℕ) : RadialMeanOn (iteratedFDeriv ℝ n f) a R := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact hm.linearIsometry (continuousMultilinearCurryFin0 ℝ WeylSpace F).symm.toLinearIsometry
  | succ n ih =>
    have : CompleteSpace (WeylSpace →L[ℝ] WeylSpace [×n]→L[ℝ] F) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => WeylSpace) F).symm.toIsometryEquiv.completeSpace
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact (ih.derivative (hf.iteratedFDeriv_right (by exact_mod_cast (show (⊤ : ℕ∞)+n≤⊤ from le_top))) (hc.iteratedFDeriv n)).linearIsometry
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => WeylSpace) F).symm.toLinearIsometry

lemma RadialMeanOn.iterated_bound {f : WeylSpace → F} {a : WeylSpace} {R M s : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) (hM : 0≤M) (hs : 0<s)
    (hb : ∀ x∈Metric.ball a R, ‖f x‖≤M) (n : ℕ) :
    ∀ x : WeylSpace, dist x a+(n : ℝ)*s<R →
      ‖iteratedFDeriv ℝ n f x‖≤M*(radialGradientMass/s)^n := by
  induction n with
  | zero =>
    intro x hx
    simp only [Nat.cast_zero,zero_mul,add_zero] at hx
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hb x hx
  | succ n ih =>
    intro x hx
    have hx' : dist x a+s<R := by
      have hn : 0≤(n : ℝ)*s := mul_nonneg (Nat.cast_nonneg _) hs.le
      push_cast at hx
      nlinarith
    rw [←norm_fderiv_iteratedFDeriv]
    have he := (hm.iterated hf hc n).derivative_bound
      (hf.iteratedFDeriv_right (by exact_mod_cast (show (⊤ : ℕ∞)+n≤⊤ from le_top))) hs hx'
      (mul_nonneg hM (pow_nonneg (div_nonneg radialGradientMass_nonneg hs.le) n)) (fun y hy => by
        apply ih
        have hh : dist y x ≤ s := hy
        have ht := dist_triangle y x a
        push_cast at hx
        nlinarith)
    rw [radialEta_gradient_integral hs] at he
    simpa only [pow_succ,mul_assoc] using he

lemma RadialMeanOn.factorial_bound {f : WeylSpace → F} {a x : WeylSpace} {R M : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) (hR : 0<R) (hM : 0≤M)
    (hb : ∀ y∈Metric.ball a R, ‖f y‖≤M) (hx : x∈Metric.ball a (R/2)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f x‖≤M*(2*Real.exp 1*(radialGradientMass+1)/R)^n*(n.factorial : ℝ) := by
  rcases n with _ | n
  · simpa using hb x (Metric.ball_subset_ball (by linarith) hx)
  let N : ℕ := n+1
  have hN : 0<(N : ℝ) := by dsimp [N]; positivity
  let s := R/(2*(N : ℝ))
  have hs : 0<s := by dsimp [s]; positivity
  have he := hm.iterated_bound hf hc hM hs hb N x (by
    have hn : (N : ℝ)*s=R/2 := by dsimp [s]; field_simp
    rw [hn]
    have hx' : dist x a<R/2 := hx
    linarith)
  have hn : (N : ℝ)^N≤(Real.exp 1)^N*(N.factorial : ℝ) := by
    have hh := Real.pow_div_factorial_le_exp (N : ℝ) hN.le N
    rw [div_le_iff₀ (by positivity : 0<(N.factorial : ℝ))] at hh
    simpa only [←Real.exp_nat_mul, mul_one] using hh
  have hbase : radialGradientMass/s≤(2*(radialGradientMass+1)/R)*(N : ℝ) := by
    dsimp [s]
    field_simp
    nlinarith [radialGradientMass_nonneg]
  calc
    _ ≤ M*(radialGradientMass/s)^N := he
    _ ≤ M*((2*(radialGradientMass+1)/R)*(N : ℝ))^N := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity [radialGradientMass_nonneg]) hbase _) hM
    _ = M*(2*(radialGradientMass+1)/R)^N*(N : ℝ)^N := by rw [mul_pow]; ring
    _ ≤ M*(2*(radialGradientMass+1)/R)^N*((Real.exp 1)^N*(N.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hn (by positivity [radialGradientMass_nonneg])
    _ = _ := by
      have heq : 2*Real.exp 1*(radialGradientMass+1)/R = (2*(radialGradientMass+1)/R)*Real.exp 1 := by ring
      rw [heq,mul_pow]
      dsimp [N]
      ring

lemma RadialMeanOn.analyticAt {f : WeylSpace → F} {a : WeylSpace} {R : ℝ}
    (hm : RadialMeanOn f a R) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) (hR : 0<R) : AnalyticAt ℝ f a := by
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hf.continuous
  have hM' : 0≤M := (norm_nonneg (f a)).trans (hM a)
  refine analyticAt_of_factorial_bound (R := R/2) (M := M)
    (C := 2*Real.exp 1*(radialGradientMass+1)/R) (by positivity) hM'
    (by positivity [radialGradientMass_nonneg]) hf.contDiffOn ?_
  intro n x hx
  exact hm.factorial_bound hf hc hR hM' (fun y _ => hM y) hx n

end ScalarConductivity

end

end OAI
