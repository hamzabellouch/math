import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.RadialCutoffMemOfNeZero
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereLSupport

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff ComplexConjugate
attribute [local instance] Classical.propDecidable

theorem sphere_pair_far_supportedND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C) (J : ℕ) :
    ∃ H D P B : ℝ, 0≤H ∧ 0≤D ∧ 0≤P ∧ 0≤B ∧
      ∀ (S T : Set (SphereAmbientND n)) (b c : SphereAmbientND n → ℂ) (e z : SphereAmbientND n) (A Λ Μ : ℝ),
      ContDiff ℝ ∞ b → ContDiff ℝ ∞ c →
      (∀ w∈S, -w∈S) → (∀ w∈T, -w∈T) → tsupport b ⊆ S → tsupport c ⊆ T →
      ‖e‖=1 → ‖z‖=1 →
      1≤A → 0<Λ → 0<Μ → A^2≤Λ → A^2≤Μ →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖≤C*A^j) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j c w‖≤C*A^j) →
      ‖∫ u : ℝ, (Ψ u:ℂ)*sphereAxisIntegralND (Λ*u) e b*conj (sphereAxisIntegralND (Μ*u) z c)‖≤
        (if e∈S ∧ z∈T then H*(Λ^(-(n:ℝ)/2)*Μ^(-(n:ℝ)/2))/(1+|Λ-Μ|)^2 else 0) +
        P*((D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3))*B +
          (B+D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3))*
            (D*Μ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3))) := by
  obtain ⟨H,hH,hkernel⟩ := pole_pair_kernelND hΨ hs n J
  obtain ⟨D,hD,hrem⟩ := sphere_radial_remainderND (n := n) C hC J
  obtain ⟨K,hK,hcoeff⟩ := spherePoleCoefficientND_bound (n := n) J C hC
  obtain ⟨P,hP,hPb⟩ := radialStationaryProfile_derivatives hΨ hs 0 0
  have hcut : ∀ u, |Ψ u|≤P := by
    simpa only [iteratedDeriv_zero,radialStationaryProfile,Real.rpow_zero,mul_one,
      Complex.norm_real,Real.norm_eq_abs] using hPb 0 le_rfl
  let B := C*(canonicalSphereMeasureND (SphereAmbientND n)).real univ
  have hB : 0≤B := mul_nonneg hC ENNReal.toReal_nonneg
  refine ⟨H*K*K,D,(15/4:ℝ)*P,B,by positivity,hD,by positivity,hB,?_⟩
  intro S T b c e z A Λ Μ hb hc hS hT hbS hcT he hz hA hΛ hΜ hscaleΛ hscaleΜ hbd hcd
  have hb0 : ∀ w, ‖w‖=1 → ‖b w‖≤C := by
    intro w hw
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hbd 0 (by omega) w hw
  have hc0 : ∀ w, ‖w‖=1 → ‖c w‖≤C := by
    intro w hw
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hcd 0 (by omega) w hw
  have hcomp := radial_pair_comparisonND hΨ.continuous hs
    (sphereAxisIntegralND_continuous hb.continuous e Λ).continuousOn
    (sphereAxisIntegralND_continuous hc.continuous z Μ).continuousOn
    (radialPoleSumND_continuousOn n J Λ (spherePoleCoefficientND J Λ b e))
    (radialPoleSumND_continuousOn n J Μ (spherePoleCoefficientND J Μ c z))
    hP hB (show 0≤D*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3) by positivity)
    hcut
    (fun u _ => sphereAxisIntegralND_norm_bound (Λ*u) e hb0)
    (fun u _ => sphereAxisIntegralND_norm_bound (Μ*u) z hc0)
    (hrem b e A Λ hb he hA hΛ hbd) (hrem c z A Μ hc hz hA hΜ hcd)
  apply hcomp.trans
  apply add_le_add _ le_rfl
  by_cases hgood : e∈S ∧ z∈T
  · simp only [ite_eq_left hgood]
    exact hkernel Λ Μ K K _ _ hΛ hΜ hK hK
      (hcoeff b e A Λ hb he hA hΛ hscaleΛ (fun j hj w hw => hbd j (by omega) w hw))
      (hcoeff c z A Μ hc hz hA hΜ hscaleΜ (fun j hj w hw => hcd j (by omega) w hw))
  · simp only [ite_eq_right hgood]
    have hzprod (u : ℝ) : (Ψ u:ℂ)*
        radialPoleSumND n J Λ (spherePoleCoefficientND J Λ b e) u*
          conj (radialPoleSumND n J Μ (spherePoleCoefficientND J Μ c z) u)=0 := by
      by_cases hbmem : e∈S
      · have hcn : z∉T := fun h => hgood ⟨hbmem,h⟩
        rw [radialPoleSumND_zero n J Μ _ (spherePoleCoefficientND_zero hc hT hcT hcn Μ)]
        simp
      · rw [radialPoleSumND_zero n J Λ _ (spherePoleCoefficientND_zero hb hS hbS hbmem Λ)]
        simp
    simp_rw [hzprod,integral_zero,norm_zero]
    exact le_rfl

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
