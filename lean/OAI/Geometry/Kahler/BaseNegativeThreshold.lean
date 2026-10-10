import OAI.Geometry.Kahler.BaseNegativeScaleBound

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

lemma gaussian_shift_tendsto (R : ℝ) :
    Tendsto (fun D : ℝ => Real.exp (-(D-R)^2/4)) atTop (𝓝 0) := by
  have hs : Tendsto (fun D : ℝ => D-R) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [eventually_ge_atTop (B+R)] with D hD
    linarith
  have hh : Tendsto (fun D : ℝ => (D-R)^2/4) atTop atTop :=
    ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hs).atTop_div_const (by norm_num)
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hh using 1
  ext D
  congr 1
  ring

lemma profiles_off_patch {a : ℝ} (ha : 1 < a) (ha2 : a < 2) :
    ∃ pr : RadialProfiles a, a*(gaussianConstant*Real.exp (-pr.R/4)) ≤ 1/2 := by
  have hh : Tendsto (fun R : ℝ => a*(gaussianConstant*Real.exp (-R/4))) atTop (𝓝 0) := by
    have he : Tendsto (fun R : ℝ => Real.exp (-R/4)) atTop (𝓝 0) := by
      convert Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<4)) using 1
      ext R; congr 1; dsimp; ring
    simpa only [mul_assoc,mul_zero] using he.const_mul (a*gaussianConstant)
  obtain ⟨R,hR⟩ := eventually_atTop.mp (hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  obtain ⟨pr,hpr⟩ := exists_radialProfiles ha ha2 R
  exact ⟨pr,(hR pr.R hpr.le).le⟩

theorem negative_scale_parameters {a : ℝ} (ha : 1 < a) (pr : RadialProfiles a)
    (hoff : a*(gaussianConstant*Real.exp (-pr.R/4)) ≤ 1/2) :
    ∃ ε η Dstar : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ η < 1/2 ∧ 1 ≤ Dstar ∧
      ∀ D : ℝ, Dstar ≤ D → ∃ kmin : ℕ, ∃ d : ℝ, 0 < d ∧
        ∀ k : ℕ, kmin ≤ k → ∀ P : Finset Sphere,
          ProjectivelySeparated (D/Real.sqrt k) P → ProjectiveCover (D/Real.sqrt k) P →
          ∀ ρ ∈ Icc (1-η) 1,
            (∫ ξ : Sphere, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ) ∂sigma)+
              ∑ p ∈ P, ∫ ξ : Sphere, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*
                densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ ∂sigma ≤ -d := by
  have ha0 : 0 < a := by linarith
  obtain ⟨ε,η,he,he1,heta,heta1,heps,hmodel⟩ := model_regularization_parameters ha pr (by positivity : 0 < 2*a)
  obtain ⟨C,hC,hval,hlip⟩ := regularizedLog_uniform_bounds a he.ne' (A := max gaussianConstant 1) (by positivity)
  obtain ⟨M,hM,hlog⟩ := radial_log_bound a ε pr.R_pos.le
  let Δ := modelGap a pr
  have hΔ : 0 < Δ := modelGap_pos pr
  have herror : Tendsto (fun D : ℝ => pr.R*(C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))*(1+Real.exp 1)) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using ((gaussian_shift_tendsto (Real.sqrt (2*pr.R))).const_mul (C*gaussianConstant)).const_mul pr.R |>.mul_const (1+Real.exp 1)
  obtain ⟨D₁,hD₁⟩ := eventually_atTop.mp (herror.eventually (gt_mem_nhds (by positivity : 0 < Δ/8)))
  let Dstar := max D₁ (max 1 (2*Real.sqrt (2*pr.R)+1))
  refine ⟨ε,η,Dstar,he,he1,heta,heta1,(le_max_left 1 _).trans (le_max_right _ _),?_⟩
  intro D hD
  have hD1 : D₁ ≤ D := (le_max_left _ _).trans hD
  have hDge : 1 ≤ D := (le_max_left 1 _).trans ((le_max_right _ _).trans hD)
  have hDsep : 2*Real.sqrt (2*pr.R) < D := by
    have hh := (le_max_right 1 (2*Real.sqrt (2*pr.R)+1)).trans ((le_max_right D₁ _).trans hD)
    linarith
  have hDR : Real.sqrt (2*pr.R) ≤ D := by linarith [Real.sqrt_nonneg (2*pr.R)]
  have hweight : Tendsto (fun t : ℝ => 2*pr.R^2*M/t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  obtain ⟨n,hn⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually
    (hweight.eventually (gt_mem_nhds (by positivity : 0 < Δ/8))))
  obtain ⟨nR,hnR⟩ := exists_nat_ge (max (2*pr.R) (D^2))
  refine ⟨max 1 (max n nR),Δ/(2*D^2),by positivity,?_⟩
  intro k hk P hP hcover ρ hρ
  have hk1 : 1 ≤ k := (le_max_left _ _).trans hk
  have hkn : n ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hkr : nR ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hkR : 2*pr.R ≤ k := (le_max_left _ _).trans (hnR.trans (by exact_mod_cast hkr))
  have hkD : D^2 ≤ k := (le_max_right _ _).trans (hnR.trans (by exact_mod_cast hkr))
  have hρ0 : 0 ≤ ρ := by linarith [hρ.1]
  have hpatch : ∀ p ∈ P, (∫ ξ in peakPatch k pr.R p, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma) ≤ -Δ/k := by
    intro p hp
    exact weighted_patch_negative ha0.le he.ne' hρ0 hρ.2 hC hM hlip
      (by omega : 0 < k) pr hkR hDge hDR hP hp (hlog ρ ⟨hρ0,hρ.2⟩)
      (hmodel ρ hρ) (hn k hkn).le (hD₁ D hD1).le
  have hh := one_scale_average_negative ha0.le he.ne' hρ0 hρ.2 hΔ pr (by omega) hkR hDge hoff hDsep hP heps hpatch
  apply hh.trans
  have hcount := (peak_count hDge hkD hP hcover).1
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcnt : 1/D^2 ≤ (P.card:ℝ)/k := by
    apply (le_div_iff₀ hk0).mpr
    simpa only [one_div,mul_comm,div_eq_mul_inv,mul_one] using hcount
  have hn' := mul_le_mul_of_nonneg_left hcnt (show 0 ≤ Δ/2 by positivity)
  convert neg_le_neg hn' using 1 <;> ring

end PinchedHartogs.BaseConstruction

end

end OAI
