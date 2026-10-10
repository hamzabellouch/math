import OAI.Geometry.Kahler.BaseRadialMeasure

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma hasDerivAt_sphere_integral {F F' : ℝ → Sphere → ℝ}
    (hF : Continuous (fun p : ℝ × Sphere => F p.1 p.2))
    (hF' : Continuous (fun p : ℝ × Sphere => F' p.1 p.2))
    (hd : ∀ t ξ, HasDerivAt (fun r => F r ξ) (F' t ξ) t) (t : ℝ) :
    HasDerivAt (fun r => ∫ ξ, F r ξ ∂sigma) (∫ ξ, F' t ξ ∂sigma) t := by
  obtain ⟨C,hC⟩ := ((isCompact_closedBall t 1).prod (isCompact_univ : IsCompact (univ : Set Sphere))).bddAbove_image hF'.norm.continuousOn
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := sigma)
    (F := F) (F' := F') (bound := fun _ => C) (s := Metric.ball t 1)
    (Metric.ball_mem_nhds t (by norm_num)) ?_ ?_ ?_ ?_ (integrable_const C) ?_).2
  · exact Eventually.of_forall (fun r => (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact continuous_integrable (hF.comp (continuous_const.prodMk continuous_id))
  · exact (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with ξ r hr
    exact hC (mem_image_of_mem (fun p : ℝ × Sphere => ‖F' p.1 p.2‖)
      (show (r,ξ) ∈ Metric.closedBall t 1 ×ˢ (univ : Set Sphere) from ⟨Metric.ball_subset_closedBall hr,mem_univ _⟩))
  · exact Eventually.of_forall (fun ξ r _ => hd r ξ)

private def rotA (u v r t : ℝ) := Real.cos t^2*u+Real.sin t^2*v+2*Real.cos t*Real.sin t*r
private def rotA' (u v r t : ℝ) := 2*Real.cos t*Real.sin t*(v-u)+2*(Real.cos t^2-Real.sin t^2)*r
private def rotA'' (u v r t : ℝ) := 2*(Real.cos t^2-Real.sin t^2)*(v-u)-8*Real.cos t*Real.sin t*r

private lemma rotA_deriv (u v r t : ℝ) : HasDerivAt (rotA u v r) (rotA' u v r t) t := by
  convert (((Real.hasDerivAt_cos t).pow 2 |>.mul_const u).add
    ((Real.hasDerivAt_sin t).pow 2 |>.mul_const v)).add
    ((((Real.hasDerivAt_cos t).const_mul 2).mul (Real.hasDerivAt_sin t)).mul_const r) using 1 <;> try rfl
  all_goals
    (try dsimp [rotA,rotA']); ring

private lemma rotA'_deriv (u v r t : ℝ) : HasDerivAt (rotA' u v r) (rotA'' u v r t) t := by
  convert (((((Real.hasDerivAt_cos t).const_mul 2).mul (Real.hasDerivAt_sin t)).mul_const (v-u)).add
    (((((Real.hasDerivAt_cos t).pow 2).sub ((Real.hasDerivAt_sin t).pow 2)).const_mul 2).mul_const r)) using 1 <;> try rfl
  all_goals
    (try dsimp [rotA',rotA'']); ring

private lemma rotated_radialU (t : ℝ) (ξ : Sphere) :
    radialU (sphereAction (rotationIsometry t) ξ) = rotA (radialU ξ) (radialV ξ) (radialR ξ) t := by
  simp only [radialU,radialV,radialR,rotationIsometry,rotA,sphereAction_coe,suIsometry_zero,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

private def rotF (n : ℕ) (t : ℝ) (ξ : Sphere) := rotA (radialU ξ) (radialV ξ) (radialR ξ) t^(n+2)
private def rotF' (n : ℕ) (t : ℝ) (ξ : Sphere) :=
  (n+2 : ℝ)*rotA (radialU ξ) (radialV ξ) (radialR ξ) t^(n+1)*rotA' (radialU ξ) (radialV ξ) (radialR ξ) t
private def rotF'' (n : ℕ) (t : ℝ) (ξ : Sphere) :=
  (n+2 : ℝ)*((n+1 : ℝ)*rotA (radialU ξ) (radialV ξ) (radialR ξ) t^n*
    (rotA' (radialU ξ) (radialV ξ) (radialR ξ) t)^2+
    rotA (radialU ξ) (radialV ξ) (radialR ξ) t^(n+1)*rotA'' (radialU ξ) (radialV ξ) (radialR ξ) t)

private lemma rotF_deriv (n : ℕ) (t : ℝ) (ξ : Sphere) :
    HasDerivAt (fun s => rotF n s ξ) (rotF' n t ξ) t := by
  convert (rotA_deriv (radialU ξ) (radialV ξ) (radialR ξ) t).pow (n+2) using 1 <;> try rfl
  all_goals
    (try simp only [rotF',Nat.cast_add,Nat.cast_ofNat]); try rfl

private lemma rotF'_deriv (n : ℕ) (t : ℝ) (ξ : Sphere) :
    HasDerivAt (fun s => rotF' n s ξ) (rotF'' n t ξ) t := by
  convert ((((rotA_deriv (radialU ξ) (radialV ξ) (radialR ξ) t).pow (n+1)).const_mul (n+2:ℝ)).mul
    (rotA'_deriv (radialU ξ) (radialV ξ) (radialR ξ) t)) using 1 <;> try rfl
  all_goals
    (try simp only [rotF'',Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,Pi.pow_apply]); ring

attribute [local fun_prop] radialU_continuous radialV_continuous radialR_continuous

private lemma rotF_continuous (n : ℕ) : Continuous (fun p : ℝ × Sphere => rotF n p.1 p.2) := by
  unfold rotF rotA
  fun_prop
private lemma rotF'_continuous (n : ℕ) : Continuous (fun p : ℝ × Sphere => rotF' n p.1 p.2) := by
  unfold rotF' rotA rotA'
  fun_prop
private lemma rotF''_continuous (n : ℕ) : Continuous (fun p : ℝ × Sphere => rotF'' n p.1 p.2) := by
  unfold rotF'' rotA rotA' rotA''
  fun_prop

lemma radial_moment_recurrence (n : ℕ) :
    (n+3 : ℝ)*(∫ ξ, radialU ξ^(n+2) ∂sigma) =
      (n+2 : ℝ)*(∫ ξ, radialU ξ^(n+1) ∂sigma) := by
  have hconst : ∀ t, (∫ ξ, rotF n t ξ ∂sigma) = ∫ ξ, radialU ξ^(n+2) ∂sigma := by
    intro t
    simpa only [rotated_radialU,rotF] using sigma_integral_unitary (rotationIsometry t)
      (fun ξ => radialU ξ^(n+2))
  have hzero : ∀ t, (∫ ξ, rotF' n t ξ ∂sigma) = 0 := by
    intro t
    have hc : HasDerivAt (fun s => ∫ ξ, rotF n s ξ ∂sigma) 0 t := by
      simpa only [hconst] using hasDerivAt_const t (∫ ξ, radialU ξ^(n+2) ∂sigma)
    exact (hasDerivAt_sphere_integral (rotF_continuous n) (rotF'_continuous n) (rotF_deriv n) t).unique hc
  have hsecond : (∫ ξ, rotF'' n 0 ξ ∂sigma) = 0 := by
    have hc : HasDerivAt (fun s => ∫ ξ, rotF' n s ξ ∂sigma) 0 0 := by
      simpa only [hzero] using hasDerivAt_const (0:ℝ) (0:ℝ)
    exact (hasDerivAt_sphere_integral (rotF'_continuous n) (rotF''_continuous n) (rotF'_deriv n) 0).unique hc
  have he : ∀ ξ : Sphere, rotF'' n 0 ξ = (n+2:ℝ)*
      (4*(n+1:ℝ)*(radialU ξ^n*radialR ξ^2)+
        2*(radialU ξ^(n+1)*radialV ξ)-2*radialU ξ^(n+2)) := by
    intro ξ
    simp only [rotF'',rotA,rotA',rotA'',Real.cos_zero,Real.sin_zero,zero_mul,mul_zero,one_pow,one_mul,add_zero,sub_zero,pow_succ]
    ring
  simp_rw [he] at hsecond
  have hR : Integrable (fun ξ => radialU ξ^n*radialR ξ^2) sigma :=
    continuous_integrable ((radialU_continuous.pow n).mul (radialR_continuous.pow 2))
  have hUV : Integrable (fun ξ => radialU ξ^(n+1)*radialV ξ) sigma :=
    continuous_integrable ((radialU_continuous.pow (n+1)).mul radialV_continuous)
  have hU : Integrable (fun ξ => radialU ξ^(n+2)) sigma := continuous_integrable (radialU_continuous.pow (n+2))
  have hparts := integral_sub (μ := sigma)
    (f := fun ξ => 4*(n+1:ℝ)*(radialU ξ^n*radialR ξ^2)+2*(radialU ξ^(n+1)*radialV ξ))
    (g := fun ξ => 2*radialU ξ^(n+2))
    ((hR.const_mul (4*(n+1:ℝ))).add (hUV.const_mul 2)) (hU.const_mul 2)
  have hparts' := integral_add (μ := sigma)
    (f := fun ξ => 4*(n+1:ℝ)*(radialU ξ^n*radialR ξ^2))
    (g := fun ξ => 2*(radialU ξ^(n+1)*radialV ξ))
    (hR.const_mul (4*(n+1:ℝ))) (hUV.const_mul 2)
  rw [integral_const_mul,hparts,hparts',integral_const_mul,integral_const_mul,integral_const_mul] at hsecond
  have huv : (∫ ξ, radialU ξ^(n+1)*radialV ξ ∂sigma) =
      (∫ ξ, radialU ξ^(n+1) ∂sigma)-(∫ ξ, radialU ξ^(n+2) ∂sigma) := by
    rw [← integral_sub (f := fun ξ => radialU ξ^(n+1)) (g := fun ξ => radialU ξ^(n+2))
      (continuous_integrable (radialU_continuous.pow (n+1))) hU]
    apply integral_congr_ae
    filter_upwards [] with ξ
    have hv : radialV ξ = 1-radialU ξ := by linarith [radialUV ξ]
    rw [hv,show n+2 = (n+1)+1 from rfl,pow_succ]
    ring
  have hs := radial_square_integral n
  rw [huv] at hs hsecond
  have hn : (0:ℝ) < n+2 := by positivity
  have hh := (mul_eq_zero.mp hsecond).resolve_left hn.ne'
  linear_combination (n+1:ℝ)*hs-hh/2

lemma radial_first_moment : (∫ ξ, radialU ξ ∂sigma) = 1/2 := by
  have hi := sigma_integral_unitary (suIsometry 0 1 (by simp)) radialU
  have he : ∀ ξ : Sphere, radialU (sphereAction (suIsometry 0 1 (by simp)) ξ) = radialV ξ := by
    intro ξ
    simp [radialU,radialV]
  simp_rw [he] at hi
  have huv : (∫ ξ, radialU ξ ∂sigma)+(∫ ξ, radialV ξ ∂sigma) = 1 := by
    rw [← integral_add (continuous_integrable radialU_continuous) (continuous_integrable radialV_continuous)]
    simp_rw [radialUV]
    simp
  linarith

lemma radial_moment (n : ℕ) : (∫ ξ, radialU ξ^n ∂sigma) = 1/(n+1:ℝ) := by
  rcases n with _|n
  · simp
  induction n with
  | zero => simpa only [Nat.zero_add,Nat.cast_one,pow_one,show (1:ℝ)+1 = 2 by norm_num] using radial_first_moment
  | succ n ih =>
    have hr := radial_moment_recurrence n
    rw [ih] at hr
    have hn : (n+2:ℝ) ≠ 0 := by positivity
    have hn' : (n+3:ℝ) ≠ 0 := by positivity
    simp only [Nat.cast_add,Nat.cast_one] at *
    field_simp at hr ⊢
    nlinarith

end PinchedHartogs.BaseConstruction

end

end OAI
