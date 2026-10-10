import OAI.Geometry.Kahler.BaseOffPatchMean

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

lemma weighted_patch_negative {a ε ρ C M D Δ : ℝ} (ha : 0 ≤ a) (hε : ε ≠ 0)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hlip : ∀ v w : ℂ, ‖v‖ ≤ max gaussianConstant 1 → ‖w‖ ≤ max gaussianConstant 1 →
      |regularizedLog a ε v-regularizedLog a ε w| ≤ C*‖v-w‖)
    {k : ℕ} (hk : 0 < k) (pr : RadialProfiles a) (hkR : 2*pr.R ≤ k)
    (hD : 1 ≤ D) (hDR : Real.sqrt (2*pr.R) ≤ D)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P) {p : Sphere} (hp : p ∈ P)
    (hb : ∀ y ∈ Icc 0 pr.R, |Real.log (logFactor (a*ρ*Real.exp (-y)) ε)-Real.log (1+ε^2)| ≤ M)
    (hm : modelMean a ε ρ pr.R pr.f ≤ -(3/4)*Δ)
    (hweight : 2*pr.R^2*M/k ≤ Δ/8)
    (herror : pr.R*(C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))*(1+Real.exp 1) ≤ Δ/8) :
    (∫ ξ in peakPatch k pr.R p, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma) ≤ -Δ/k := by
  have h1 := (abs_le.mp (weighted_patch_error hε hρ hρ1 hC hlip hk pr hkR hD hDR hP hp)).2
  have h2 := ideal_patch_upper ha hε hρ hM pr hk p hb
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have h3 := mul_le_mul_of_nonneg_left herror (show 0 ≤ 2/(k:ℝ) by positivity)
  have h4 : 2/(k:ℝ)*(modelMean a ε ρ pr.R pr.f+2*pr.R^2*M/k) ≤ 2/(k:ℝ)*(-(3/4)*Δ+Δ/8) := by gcongr
  have he : (2*pr.R/k)*(C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))*(1+Real.exp 1)=
      (2/(k:ℝ))*(pr.R*(C*gaussianConstant*Real.exp (-(D-Real.sqrt (2*pr.R))^2/4))*(1+Real.exp 1)) := by ring
  rw [he] at h1
  calc
    _ ≤ 2/(k:ℝ)*(-(3/4)*Δ+Δ/8)+(2/(k:ℝ))*(Δ/8) := by linarith
    _ = _ := by ring

lemma one_scale_average_negative {a ε ρ Δ D : ℝ} (ha : 0 ≤ a) (hε : ε ≠ 0)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hΔ : 0 < Δ) (pr : RadialProfiles a)
    {k : ℕ} (hk : 0 < k) (hkR : 2*pr.R ≤ k) (hD : 1 ≤ D)
    (hoff : a*(gaussianConstant*Real.exp (-pr.R/4)) ≤ 1/2)
    (hsep : 2*Real.sqrt (2*pr.R) < D) {P : Finset Sphere}
    (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    (heps : 2*a*ε^2 ≤ Δ/8)
    (hpatch : ∀ p ∈ P, (∫ ξ in peakPatch k pr.R p, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*
      (1+densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ) ∂sigma) ≤ -Δ/k) :
    (∫ ξ : Sphere, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ) ∂sigma)+
      ∑ p ∈ P, ∫ ξ : Sphere, regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)*
        densityCorrection k pr.R pr.f pr.b (fun _ => 1) p ξ ∂sigma ≤ -(Δ/2)*((P.card:ℝ)/k) := by
  have hV : Continuous (fun ξ : Sphere => regularizedLog a ε ((ρ:ℂ)*peakPolynomial P k ξ)) :=
    (regularizedLog_contDiff a hε).continuous.comp
      (continuous_const.mul ((peakPolynomial_analytic P k).continuous.comp continuous_subtype_val))
  rw [patch_decomposition pr hk P (peakPatch_disjoint hk pr.R_pos hsep hP) hV]
  have ho := peak_off_set_integral ha hρ hρ1 hε P hk
    (peakPatchUnion_open P k pr.R).measurableSet.compl
    (fun z ξ => not_congr (peakPatchUnion_phase P k pr.R z ξ)) (fun ξ hξ => ?_)
  · have hs := Finset.sum_le_sum hpatch
    have he : (∑ p ∈ P, (-Δ/(k:ℝ)))= -Δ*((P.card:ℝ)/k) := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    rw [he] at hs
    have hk0 : (0:ℝ) < k := by exact_mod_cast hk
    have hc : 0 ≤ (P.card:ℝ)/(k:ℝ) := by positivity
    have hεbound := mul_le_mul_of_nonneg_right heps hc
    have he' : 2*a*ε^2*(P.card:ℝ)/k=(2*a*ε^2)*((P.card:ℝ)/k) := by ring
    rw [he'] at ho
    nlinarith
  · apply le_trans (mul_le_mul_of_nonneg_left (peak_off_patch (by omega) pr.R_pos hkR hD hP ξ ?_) ha) hoff
    intro p hp hmem
    exact hξ (mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨hp,hmem⟩⟩)

end PinchedHartogs.BaseConstruction

end

end OAI
