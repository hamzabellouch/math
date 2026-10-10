import OAI.Geometry.Relativity.CKS.AngularSymbols

namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Set Filter Finset CKSSphericalHarmonics CKSInducedSphere CKSSphericalChart CKSBending
open scoped Topology ContDiff

lemma log_heat_nonneg (T : ℝ) :
    ∀ᶠ x : E in spatialInfinity, 0 ≤ T+(1/2:ℝ)*Real.log ‖x‖ := by
  filter_upwards [eventually_norm_ge (Real.exp (-2*T)),eventually_norm_gt 0] with x hx hr
  have hlog : -2*T ≤ Real.log ‖x‖ := (Real.le_log_iff_exp_le hr).mpr hx
  linarith

lemma log_heat_exponential {r : ℝ} (hr : 0 < r) (T : ℝ) :
    Real.exp (-6*(T+(1/2:ℝ)*Real.log r)) = Real.exp (-6*T)*r^(-3:ℝ) := by
  rw [Real.rpow_def_of_pos hr,←Real.exp_add]
  congr 1
  ring

theorem radialHeat_symbol {p : ℕ → Poly} (hp : PolynomialRapid p)
    {F : ℝ → E → ℝ} (hF : HeatGenerated p F) (T d : ℝ) :
    Symbol (d+3) (radialHeat F T (1/2) d) := by
  apply symbol_of_words
  · filter_upwards [eventually_norm_gt 0] with x hx
    exact radialHeat_smooth (hF.joint_smooth hp) T (1/2) d (norm_pos_iff.mp hx)
  · intro w
    obtain ⟨C,hC,hb⟩ := radialHeat_word_decay hp hF T (1/2) d w
    refine ⟨C*Real.exp (-6*T),mul_nonneg hC (Real.exp_pos _).le,?_⟩
    filter_upwards [eventually_norm_gt 0,log_heat_nonneg T] with x hx ht
    apply (hb x (norm_pos_iff.mp hx) ht).trans_eq
    rw [log_heat_exponential hx T]
    rw [show -(d+3+w.length) = -(d+w.length)+(-3) by ring,Real.rpow_add hx]
    ring

def tailKappa (R : ℝ) : ℝ := heatTime R (2*R^2)-Real.log (2*R^2)/2

def massHeatRemainder (f₀ : C(Sphere,ℝ)) (R : ℝ) : E → ℝ :=
  radialHeat (spatialHeat (heatPolynomials f₀) (0,[])) (tailKappa R) (1/2) 0

lemma massHeatRemainder_symbol (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (R : ℝ) :
    Symbol 3 (massHeatRemainder f₀ R) := by
  simpa only [zero_add,massHeatRemainder] using
    radialHeat_symbol (smoothDatum_rapid f₀ hf₀) (HeatGenerated.basic (0,[])) (tailKappa R) 0

lemma cartMass_tail_formula (f₀ : C(Sphere,ℝ)) (m : ℝ) {R : ℝ} (hR : 12 ≤ R) :
    cartMass f₀ m R =ᶠ[spatialInfinity] (fun x =>
      m+paddingCharge R-2*‖x‖^(-(1/2:ℝ))+massHeatRemainder f₀ R x) := by
  filter_upwards [eventually_norm_ge (2*R^2)] with x hx
  have hRp : 0 < R := by linarith
  have hx' : 2*R ≤ ‖x‖ := by nlinarith
  have hr : 0 < ‖x‖ := lt_of_lt_of_le (by positivity : 0 < 2*R) hx'
  have ht : heatTime R ‖x‖ = tailKappa R+(1/2:ℝ)*Real.log ‖x‖ := by
    rw [heatTime_tail hR hx,tailKappa]
    ring
  have hp : paddingMass R ‖x‖ = paddingCharge R-2*‖x‖^(-(1/2:ℝ)) := by
    rw [paddingMass_tail hRp hx',paddingCharge,Real.rpow_neg (norm_nonneg _),←Real.sqrt_eq_rpow]
    ring
  simp only [cartMass,ht,hp,canonicalF,massHeatRemainder,radialHeat,
    neg_zero,Real.rpow_zero,one_mul]
  ring

theorem cartMass_symbol (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 12 ≤ R) : Symbol 0 (cartMass f₀ m R) := by
  have hp := (norm_power_symbol (1/2:ℝ)).const_mul (2:ℝ)
  have hh := massHeatRemainder_symbol f₀ hf₀ R
  apply (((Symbol.const (m+paddingCharge R)).sub (hp.weaken (by norm_num))).add
    (hh.weaken (by norm_num))).congr
  exact (cartMass_tail_formula f₀ m hR).symm

theorem cartMass_refined (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 12 ≤ R) : Symbol 3 (fun x =>
      cartMass f₀ m R x-(m+paddingCharge R-2*‖x‖^(-(1/2:ℝ)))) := by
  apply (massHeatRemainder_symbol f₀ hf₀ R).congr
  filter_upwards [cartMass_tail_formula f₀ m hR] with x hx
  rw [hx]
  ring

end
end CKSADM

end

end OAI
