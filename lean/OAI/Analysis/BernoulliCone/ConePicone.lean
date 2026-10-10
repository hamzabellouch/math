import OAI.Analysis.BernoulliCone.DominatedVariation

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli.Halfspace
open HarmonicKernel
variable {d : ℕ}

lemma positiveSquareRatio_hasFDerivAt {u v : Space d → ℝ} {x : Space d}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) (hu0 : 0<u x) :
    HasFDerivAt (positiveSquareRatio v u)
      ((2*v x/u x) • fderiv ℝ v x-(v x/u x)^2 • fderiv ℝ u x) x := by
  have hh := (hv.hasFDerivAt.pow 2).mul ((hasDerivAt_inv hu0.ne').comp_hasFDerivAt x hu.hasFDerivAt)
  have he : positiveSquareRatio v u =ᶠ[𝓝 x] (fun y=>v y^2/u y) := by
    filter_upwards [hu.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hu0)] with y hy
    change 0<u y at hy
    simp only [positiveSquareRatio,ite_eq_left hy]
  simp only [Function.comp_apply] at hh
  convert! hh.congr_of_eventuallyEq he using 1
  ext z
  simp only [sub_apply,smul_apply,smul_eq_mul,add_apply,pow_one,Nat.reduceSub]
  field_simp
  ring

lemma positiveSquareRatio_gradient {u v : Space d → ℝ} {x : Space d}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) (hu0 : 0<u x) :
    gradient (positiveSquareRatio v u) x=
      (2*v x/u x) • gradient v x-(v x/u x)^2 • gradient u x := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,(positiveSquareRatio_hasFDerivAt hu hv hu0).fderiv]
  simp only [sub_apply,smul_apply,smul_eq_mul,inner_sub_left,real_inner_smul_left,inner_gradient_left]

lemma weighted_positiveSquareRatio_gradient {u v : Space d → ℝ} {x : Space d}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) (hu0 : 0<u x) :
    gradient (fun y=>potential y*positiveSquareRatio v u y) x =
      positiveSquareRatio v u x • gradient potential x +
        potential x • gradient (positiveSquareRatio v u) x := by
  apply ext_inner_right ℝ
  intro z
  have hh := (contDiff_potential.differentiable (by simp) x).hasFDerivAt.mul
    (positiveSquareRatio_hasFDerivAt hu hv hu0)
  change HasFDerivAt (fun y=>potential y*positiveSquareRatio v u y) _ x at hh
  rw [inner_gradient_left,hh.fderiv]
  simp only [inner_add_left,real_inner_smul_left,inner_gradient_left,add_apply,smul_apply,smul_eq_mul]
  rw [(positiveSquareRatio_hasFDerivAt hu hv hu0).fderiv]
  ring

/-- Picone ground-state equality from full minimizing comparison. It is a
consequence, not a stationarity or regularity assumption in `GlobalMinimizer`. -/
theorem picone_gradient_equality {u v : Space d → ℝ} {L M C : ℝ≥0}
    (hm : GlobalMinimizer u) (hL : LipschitzWith L u) (hM : LipschitzWith M v)
    (hom : ∀r:ℝ, 0<r → ∀x, u (r•x)=r*u x)
    (hC : 1≤C) (hbound : ∀x, |v x| ≤ (C:ℝ)*u x)
    (hvI : (∫ x in ball (0:Space d) 2, potential x*‖gradient v x‖^2-rawKernel x*v x^2)=0) :
    ∀ᵐ x ∂volume.restrict (ball (0:Space d) 1),
      gradient v x=(v x/u x) • gradient u x := by
  let B := ball (0:Space d) 2
  let μ := volume.restrict B
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hn := hm.nonneg_of_continuous hL.continuous
  let q := fun x=>potential x*positiveSquareRatio v u x
  have hφ : Test B potential := radial_potential_test
  obtain ⟨K,hφL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ.2.1 hφ.1 (by simp)
  obtain ⟨J,hq'⟩ := lipschitz_mul_compact (positiveSquareRatio_lipschitz hL hM hC hn hbound) hφL hφ.2.1
  have hq : LipschitzWith J q := by simpa only [q,mul_comm] using hq'
  have hc : HasCompactSupport q := hφ.2.1.mul_right
  have hs : tsupport q ⊆ B := tsupport_mul_subset_left.trans hφ.2.2
  obtain ⟨A,hA⟩ := hφ.2.1.exists_bound_of_continuous contDiff_potential.continuous
  have hC0 : 0<(C:ℝ) := lt_of_lt_of_le zero_lt_one (show 1≤(C:ℝ) from hC)
  have hqbound : ∀x, |q x| ≤ ((|A|+1)*(C:ℝ)^2)*u x := by
    intro x
    rw [show q x=potential x*positiveSquareRatio v u x from rfl,abs_mul,
      abs_of_nonneg (positiveSquareRatio_nonneg x)]
    have hb := positiveSquareRatio_bound C.coe_nonneg hn hbound x
    have hφb : |potential x| ≤ |A|+1 := (hA x).trans (by linarith [le_abs_self A])
    calc
      _ ≤ (|A|+1)*((C:ℝ)^2*u x) := mul_le_mul hφb hb (positiveSquareRatio_nonneg x) (by positivity)
      _ = _ := by ring
  have hqI := hm.dominatedVariation hL (by norm_num : 0<(2:ℝ))
    (LipschitzSobolev.h10 hq hc isOpen_ball hs)
    (show 0<(|A|+1)*(C:ℝ)^2 by positivity) (Eventually.of_forall hqbound)
  have hu0 := SobolevCalculus.gradient_zero_on_zero_set isOpen_ball (LipschitzSobolev.h1_ball hL 0 2)
  have hv0 := SobolevCalculus.gradient_zero_on_zero_set isOpen_ball (LipschitzSobolev.h1_ball hM 0 2)
  have hq0 := SobolevCalculus.gradient_zero_on_zero_set isOpen_ball (LipschitzSobolev.h1_ball hq 0 2)
  let F := fun x=>potential x*‖gradient v x‖^2-rawKernel x*v x^2
  let E := fun x=>inner ℝ (gradient u x) (gradient q x)
  let R := fun x=>potential x*‖gradient v x-(v x/u x) • gradient u x‖^2
  have hRE : R =ᵐ[μ] (fun x=>F x-E x) := by
    filter_upwards [ae_restrict_of_ae hL.ae_differentiableAt,
      ae_restrict_of_ae hM.ae_differentiableAt,hu0,hv0,hq0] with x hux hvx hug hvg hqg
    by_cases hup : 0<u x
    · have he := ConeCalculus.euler_identity hux hom
      rw [←inner_gradient_left] at he
      dsimp [R,F,E,q]
      rw [weighted_positiveSquareRatio_gradient hux hvx hup,
        positiveSquareRatio_gradient hux hvx hup,potential_gradient]
      rw [←real_inner_self_eq_norm_sq]
      simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
        inner_add_right,real_inner_self_eq_norm_sq,positiveSquareRatio,ite_eq_left hup,
        real_inner_comm (gradient v x) (gradient u x),he,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
      field_simp
      ring
    · have huz : u x=0 := le_antisymm (not_lt.mp hup) (hn x)
      have hvz : v x=0 := abs_eq_zero.mp (le_antisymm (by simpa only [huz,mul_zero] using hbound x) (abs_nonneg _))
      have hqz : q x=0 := by simp [q,positiveSquareRatio,hup]
      simp only [R,F,E,huz,hvz,hug huz,hvg hvz,hqg hqz,zero_div,zero_smul,sub_self,
        norm_zero,zero_pow (by norm_num : 2≠0),mul_zero,inner_zero_left]
  have hFi : Integrable F μ := radial_outer_integrable hM
  have hEi : Integrable E μ := integrable_inner_of_memLp (LipschitzSobolev.h1_ball hL 0 2).2.1
    (LipschitzSobolev.h1_ball hq 0 2).2.1
  have hRi : Integrable R μ := (hFi.sub hEi).congr hRE.symm
  have hRI : (∫ x, R x ∂μ)=0 := by
    rw [integral_congr_ae hRE,integral_sub hFi hEi]
    change (∫x in B,F x)-(∫x in B,E x)=0
    rw [hvI,hqI,sub_self]
  have haz : R =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall (fun x=>mul_nonneg (potential_nonneg x) (sq_nonneg _))) hRi).mp hRI
  have hle : volume.restrict (ball (0:Space d) 1)≤μ :=
    Measure.restrict_mono (ball_subset_ball (by norm_num)) le_rfl
  filter_upwards [ae_mono hle haz,ae_restrict_mem measurableSet_ball] with x hx hxb
  have hsq : ‖gradient v x-(v x/u x) • gradient u x‖^2=0 :=
    (mul_eq_zero.mp hx).resolve_left (potential_pos hxb).ne'
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
end Bernoulli.Halfspace

end
end

end OAI
