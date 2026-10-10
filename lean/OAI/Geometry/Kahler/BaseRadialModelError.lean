import OAI.Geometry.Kahler.BasePatchComparison

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma radial_log_bound (a ε : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ρ ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) R,
      |Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)| ≤ M := by
  have hq : Continuous (fun p : ℝ × ℝ => a*p.1*Real.exp (-p.2)) := by fun_prop
  have hL := logFactor_continuous.comp (hq.prodMk (continuous_const (y := ε)))
  have hc := (hL.log (fun p => (logFactor_pos _ _).ne')).sub (continuous_const (y := Real.log (1+ε^2)))
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hc.continuousOn (s := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) R))
  refine ⟨M,(norm_nonneg _).trans (hM (0,0) ⟨⟨le_rfl,zero_le_one⟩,⟨le_rfl,hR⟩⟩),?_⟩
  intro ρ hρ y hy
  exact hM (ρ,y) ⟨hρ,hy⟩

lemma exp_radial_weight_error {k : ℕ} (hk : 0 < k) {R y : ℝ} (hy : 0 ≤ y) (hyR : y ≤ R) :
    |Real.exp (-2*y/k)-1| ≤ 2*R/k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have ht : 0 ≤ 2*y/(k:ℝ) := by positivity
  have he1 : Real.exp (-2*y/k) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by nlinarith) hk0.le)
  rw [abs_of_nonpos (sub_nonpos.mpr he1)]
  have he := Real.one_sub_le_exp_neg (2*y/(k:ℝ))
  have hrep : -(2*y/(k:ℝ)) = -2*y/k := by ring
  rw [hrep] at he
  have hm : 2*y/(k:ℝ) ≤ 2*R/k := by gcongr
  linarith

lemma radial_patch_model_error {a ε ρ M : ℝ} (hM : 0 ≤ M)
    (pr : RadialProfiles a) {k : ℕ} (hk : 0 < k)
    (hb : ∀ y ∈ Icc 0 pr.R, |Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)| ≤ M) :
    |(∫ y in 0..pr.R, radialPatchModel a ε ρ k pr.f y)-modelMean a ε ρ pr.R pr.f| ≤ 2*pr.R^2*M/k := by
  have hR : 0 ≤ pr.R := pr.R_pos.le
  rw [modelMean,← intervalIntegral.integral_sub
    ((radialPatchModel_continuous a ε ρ k pr.smooth_f.continuous).intervalIntegrable 0 pr.R)
    ((modelIntegrand_continuous_y pr.smooth_f.continuous a ε ρ).intervalIntegrable 0 pr.R)]
  have he : ∀ y, radialPatchModel a ε ρ k pr.f y-modelIntegrand a ε ρ pr.f y=
      (Real.exp (-2*y/k)-1)*(Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)) := by
    intro y; unfold radialPatchModel modelIntegrand; ring
  simp_rw [he]
  have hh : ‖∫ y in (0:ℝ)..pr.R, (Real.exp (-2*y/k)-1)*
      (Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2))‖ ≤
      ((2*pr.R/k)*M)*|pr.R-0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    have hy' : y ∈ Icc 0 pr.R := by
      rw [uIoc_of_le pr.R_pos.le] at hy
      exact ⟨hy.1.le,hy.2⟩
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul_of_nonneg_left (hb y hy') (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (exp_radial_weight_error hk hy'.1 hy'.2) hM)
  rw [Real.norm_eq_abs,sub_zero,abs_of_pos pr.R_pos] at hh
  exact hh.trans_eq (by ring)

lemma ideal_patch_upper {a ε ρ M : ℝ} (ha : 0 ≤ a) (hε : ε ≠ 0) (hρ : 0 ≤ ρ)
    (hM : 0 ≤ M) (pr : RadialProfiles a) {k : ℕ} (hk : 0 < k) (p : Sphere)
    (hb : ∀ y ∈ Icc 0 pr.R, |Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)| ≤ M) :
    (∫ ξ in peakPatch k pr.R p, regularizedLog a ε ((ρ:ℂ)*bracket (ξ:Base) (p:Base)^k)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma) ≤
      2/(k:ℝ)*(modelMean a ε ρ pr.R pr.f+2*pr.R^2*M/k) := by
  rw [ideal_patch_integral ha hρ hε pr hk p]
  gcongr
  have hh := (abs_le.mp (radial_patch_model_error hM pr hk hb)).2
  linarith

end PinchedHartogs.BaseConstruction

end

end OAI
