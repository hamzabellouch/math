import OAI.Geometry.Relativity.CKS.HeatSymbols

namespace OAI

noncomputable section
namespace CKSADM
noncomputable section
open Set Filter Finset CKSSphericalHarmonics CKSInducedSphere CKSSphericalChart CKSBending
open scoped Topology ContDiff

theorem rational_coefficient_symbol {F : E → ℝ} (hF : Symbol 0 F) :
    Symbol 1 (fun x => (1-2*F x/‖x‖)⁻¹-1) := by
  let q : E → ℝ := fun x => 2*F x/‖x‖
  have hq : Symbol 1 q := by
    have hh := (hF.const_mul 2).mul (norm_power_symbol 1)
    simpa only [zero_add,Real.rpow_neg_one,div_eq_mul_inv,q] using hh
  have hd : Symbol 0 (fun x => 1-q x) := (Symbol.const 1).sub (hq.weaken (by norm_num))
  obtain ⟨C,hC,hb⟩ := hF.2 0
  have hl : ∀ᶠ x in spatialInfinity, (1:ℝ)/2 ≤ 1-q x := by
    filter_upwards [hb,eventually_norm_ge (4*C+1)] with x hx hr
    have hh : |F x| ≤ C := by simpa only [neg_zero,Real.rpow_zero,mul_one] using hx
    exact denominator_lower hC hh hr
  have hi := hd.inverse (c := (1:ℝ)/2) (by norm_num) (hl.mono (fun x hx => hx.trans (le_abs_self _)))
  have hp := hq.mul hi
  simp only [add_zero] at hp
  apply hp.congr
  filter_upwards [hl] with x hx
  have hne : 1-q x ≠ 0 := by linarith
  change q x*(1-q x)⁻¹ = (1-q x)⁻¹-1
  field_simp
  ring

theorem cartB_symbol (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 12 ≤ R) : Symbol 1 (cartB f₀ m R) :=
  rational_coefficient_symbol (cartMass_symbol f₀ hf₀ m hR)

theorem constructed_metric_decay (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 12 ≤ R) (i j : Ix) :
    Symbol 1 (fun x => metric (cartB f₀ m R) x i j-(if i=j then 1 else 0)) := by
  have hh := ((cartB_symbol f₀ hf₀ m hR).mul (normal_symbol i)).mul (normal_symbol j)
  simp only [add_zero] at hh
  convert hh using 1
  funext x
  simp [metric]

theorem constructed_metric_word_decay (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 12 ≤ R) (i j : Ix) (w : List Ix) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in spatialInfinity,
      |cartWord w (fun y => metric (cartB f₀ m R) y i j-(if i=j then 1 else 0)) x| ≤
        C*‖x‖^(-(1+w.length:ℝ)) :=
  SymbolN.word (constructed_metric_decay f₀ hf₀ m hR i j) w

end
end CKSADM

end

end OAI
