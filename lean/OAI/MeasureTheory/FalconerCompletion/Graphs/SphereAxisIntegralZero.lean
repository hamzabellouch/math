import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.EuclideanPairDirection
import OAI.MeasureTheory.FalconerCompletion.Graphs.ProfileChildCard
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereNoncomparableRapid

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real
open scoped ContDiff ComplexConjugate Topology

lemma sphereAxisIntegralND_zeroND {n : ℕ} (e : SphereAmbientND n) (b : SphereAmbientND n → ℂ) :
    sphereAxisIntegralND 0 e b = ∫ w, b w ∂canonicalSphereMeasureND (SphereAmbientND n) := by
  simp [sphereAxisIntegralND]

theorem sphere_noncomparable_zero_rapidND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ β : ℝ} (hθ : 0<θ) (hβ : 0<β) (B T : ℝ) :
    ∃ J : ℕ, ∀ᶠ R : ℝ in atTop,
      ∀ (b c : SphereAmbientND n → ℂ) (e z : SphereAmbientND n) (A Λ Μ : ℝ),
      ContDiff ℝ ∞ b → Continuous c → ‖e‖=1 → (Μ=0 ∨ ‖z‖=1) →
      1≤A → A≤R^2 → R^β≤Λ → A^2/Λ≤R^(-θ) → 0≤Μ → 2*Μ≤Λ →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖≤C*A^j) →
      (∀ w, ‖w‖=1 → ‖c w‖≤C) →
      R^B*‖∫ u : ℝ, (Ψ u:ℂ)*sphereAxisIntegralND (Λ*u) e b*conj (sphereAxisIntegralND (Μ*u) z c)‖≤R^(-T) := by
  obtain ⟨J,hJ⟩ := sphere_noncomparable_rapidND (n := n) hΨ hs C hC hθ hβ B T
  refine ⟨J,?_⟩
  filter_upwards [hJ] with R hJ
  intro b c e z A Λ Μ hb hc he hz hA hAup hΛ hratio hΜ hsep hbd hcd
  rcases hz with rfl|hz
  · have hh := hJ b c e (WithLp.toLp 2 (0,(1:ℝ))) A Λ 0 hb hc he sphere_north_normND
      hA hAup hΛ hratio hΜ hsep hbd hcd
    simpa only [zero_mul,sphereAxisIntegralND_zeroND] using hh
  · exact hJ b c e z A Λ Μ hb hc he hz hA hAup hΛ hratio hΜ hsep hbd hcd

lemma sphere_radial_pair_swap_normND {n : ℕ} (Ψ : ℝ → ℝ)
    (b c : SphereAmbientND n → ℂ) (e z : SphereAmbientND n) (Λ Μ : ℝ) :
    ‖∫ u : ℝ, (Ψ u:ℂ)*sphereAxisIntegralND (Λ*u) e b*conj (sphereAxisIntegralND (Μ*u) z c)‖ =
      ‖∫ u : ℝ, (Ψ u:ℂ)*sphereAxisIntegralND (Μ*u) z c*conj (sphereAxisIntegralND (Λ*u) e b)‖ := by
  have he : (fun u : ℝ => (Ψ u:ℂ)*sphereAxisIntegralND (Λ*u) e b*conj (sphereAxisIntegralND (Μ*u) z c)) =
      (fun u : ℝ => conj ((Ψ u:ℂ)*sphereAxisIntegralND (Μ*u) z c*conj (sphereAxisIntegralND (Λ*u) e b))) := by
    funext u
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_conj]
    ring
  rw [he,integral_conj,Complex.norm_conj]

theorem original_far_noncomparable_pointND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ β : ℝ} (hθ : 0<θ) (hβ : 0<β) (B T : ℝ) :
    ∃ J : ℕ, ∀ᶠ R : ℝ in atTop,
      ∀ (b c : SphereAmbientND n → ℂ) (x y : SphereAmbientND n × SphereAmbientND n) (A v : ℝ),
      ContDiff ℝ ∞ b → ContDiff ℝ ∞ c → 1≤A → A≤R^2 →
      R^β≤(2:ℝ)^v*max (dist x.1 x.2) (dist y.1 y.2) →
      A^2/((2:ℝ)^v*max (dist x.1 x.2) (dist y.1 y.2))≤R^(-θ) →
      2*min (dist x.1 x.2) (dist y.1 y.2)≤ max (dist x.1 x.2) (dist y.1 y.2) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖≤C*A^j) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j c w‖≤C*A^j) →
      R^B*‖∫ u : ℝ, (Ψ u:ℂ)*
        sphereAxisIntegralND (((2:ℝ)^v*dist x.1 x.2)*u) (farUnitDirectionND x) b*
          conj (sphereAxisIntegralND (((2:ℝ)^v*dist y.1 y.2)*u) (farUnitDirectionND y) c)‖≤R^(-T) := by
  obtain ⟨J,hJ⟩ := sphere_noncomparable_zero_rapidND (n := n) hΨ hs C hC hθ hβ B T
  refine ⟨J,?_⟩
  filter_upwards [hJ,eventually_gt_atTop (0:ℝ)] with R hJ hR
  intro b c x y A v hb hc hA hAup hΛ hrat hsep hbd hcd
  have hz (z : SphereAmbientND n × SphereAmbientND n) :
      (2:ℝ)^v*dist z.1 z.2=0 ∨ ‖farUnitDirectionND z‖=1 := by
    by_cases hd : dist z.1 z.2=0
    · exact Or.inl (by rw [hd,mul_zero])
    · exact Or.inr (farUnitDirectionND_norm z (lt_of_le_of_ne dist_nonneg (Ne.symm hd)))
  have hb0 (w : SphereAmbientND n) (hw : ‖w‖=1) : ‖b w‖≤C := by
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hbd 0 (by omega) w hw
  have hc0 (w : SphereAmbientND n) (hw : ‖w‖=1) : ‖c w‖≤C := by
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hcd 0 (by omega) w hw
  have h2 : 0<(2:ℝ)^v := Real.rpow_pos_of_pos (by norm_num) v
  rcases le_total (dist y.1 y.2) (dist x.1 x.2) with hxy|hyx
  · simp only [max_eq_left hxy,min_eq_right hxy] at hΛ hrat hsep
    have hxpos : 0<dist x.1 x.2 := (mul_pos_iff_of_pos_left h2).mp
      ((Real.rpow_pos_of_pos hR β).trans_le hΛ)
    apply hJ b c (farUnitDirectionND x) (farUnitDirectionND y) A _ _ hb hc.continuous
      (farUnitDirectionND_norm _ hxpos) (hz y) hA hAup hΛ hrat (by positivity) _ hbd hc0
    nlinarith [mul_le_mul_of_nonneg_left hsep h2.le]
  · simp only [max_eq_right hyx,min_eq_left hyx] at hΛ hrat hsep
    rw [sphere_radial_pair_swap_normND]
    have hypos : 0<dist y.1 y.2 := (mul_pos_iff_of_pos_left h2).mp
      ((Real.rpow_pos_of_pos hR β).trans_le hΛ)
    apply hJ c b (farUnitDirectionND y) (farUnitDirectionND x) A _ _ hc hb.continuous
      (farUnitDirectionND_norm _ hypos) (hz x) hA hAup hΛ hrat (by positivity) _ hcd hb0
    nlinarith [mul_le_mul_of_nonneg_left hsep h2.le]

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Filter Real
open scoped ContDiff ComplexConjugate Topology

theorem sphere_noncomparable_zero_rapid_euclideanND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ β : ℝ} (hθ : 0<θ) (hβ : 0<β) (B T : ℝ) :
    ∃ J : ℕ, ∀ᶠ R : ℝ in atTop,
      ∀ (b c : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (e z : EuclideanSpace ℝ (Fin (n+1))) (A Λ Μ : ℝ),
      ContDiff ℝ ∞ b → Continuous c → ‖e‖=1 → (Μ=0 ∨ ‖z‖=1) →
      1≤A → A≤R^2 → R^β≤Λ → A^2/Λ≤R^(-θ) → 0≤Μ → 2*Μ≤Λ →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖≤C*A^j) →
      (∀ w, ‖w‖=1 → ‖c w‖≤C) →
      R^B*‖∫ u : ℝ, (Ψ u:ℂ)*sphereAxisIntegralND (Λ*u) e b*conj (sphereAxisIntegralND (Μ*u) z c)‖≤R^(-T) := by
  obtain ⟨J,hJ⟩ := sphere_noncomparable_zero_rapidND (n := n) hΨ hs C hC hθ hβ B T
  refine ⟨J,?_⟩
  let E := sphereAmbientEuclideanND n
  filter_upwards [hJ] with R hJ
  intro b c e z A Λ Μ hb hc he hz hA hAup hΛ hrat hΜ hsep hbd hcd
  have hh := hJ (b ∘ E) (c ∘ E) (E.symm e) (E.symm z) A Λ Μ
    (hb.comp E.toContinuousLinearEquiv.contDiff) (hc.comp E.continuous)
    (by simpa using he) (by simpa using hz) hA hAup hΛ hrat hΜ hsep
    (by intro j hj w hw; rw [E.norm_iteratedFDeriv_comp_right]; exact hbd j hj (E w) (by simpa using hw))
    (by intro w hw; exact hcd (E w) (by simpa using hw))
  have hk (u : ℝ) : sphereAxisIntegralND (Λ*u) e b=sphereAxisIntegralND (Λ*u) (E.symm e) (b ∘ E) := by
    simpa using sphereAxisIntegralND_transport E (Λ*u) (E.symm e) b
  have hl (u : ℝ) : sphereAxisIntegralND (Μ*u) z c=sphereAxisIntegralND (Μ*u) (E.symm z) (c ∘ E) := by
    simpa using sphereAxisIntegralND_transport E (Μ*u) (E.symm z) c
  simpa only [hk,hl] using hh

lemma euclidean_radial_pair_swap_normND {n : ℕ} (Ψ : ℝ → ℝ)
    (b c : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (e z : EuclideanSpace ℝ (Fin (n+1))) (Λ Μ : ℝ) :
    ‖∫ u : ℝ, (Ψ u:ℂ)*sphereAxisIntegralND (Λ*u) e b*conj (sphereAxisIntegralND (Μ*u) z c)‖ =
      ‖∫ u : ℝ, (Ψ u:ℂ)*sphereAxisIntegralND (Μ*u) z c*conj (sphereAxisIntegralND (Λ*u) e b)‖ := by
  have he : (fun u : ℝ => (Ψ u:ℂ)*sphereAxisIntegralND (Λ*u) e b*conj (sphereAxisIntegralND (Μ*u) z c)) =
      (fun u : ℝ => conj ((Ψ u:ℂ)*sphereAxisIntegralND (Μ*u) z c*conj (sphereAxisIntegralND (Λ*u) e b))) := by
    funext u
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_conj]
    ring
  rw [he,integral_conj,Complex.norm_conj]

theorem euclidean_far_noncomparable_pointND {n : ℕ} {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ t, Ψ t≠0 → t∈Ioo (1/4:ℝ) 4) (C : ℝ) (hC : 0≤C)
    {θ β : ℝ} (hθ : 0<θ) (hβ : 0<β) (B T : ℝ) :
    ∃ J : ℕ, ∀ᶠ R : ℝ in atTop,
      ∀ (b c : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (x y : EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) (A v : ℝ),
      ContDiff ℝ ∞ b → ContDiff ℝ ∞ c → 1≤A → A≤R^2 →
      R^β≤(2:ℝ)^v*max (dist x.1 x.2) (dist y.1 y.2) →
      A^2/((2:ℝ)^v*max (dist x.1 x.2) (dist y.1 y.2))≤R^(-θ) →
      2*min (dist x.1 x.2) (dist y.1 y.2)≤ max (dist x.1 x.2) (dist y.1 y.2) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖≤C*A^j) →
      (∀ j≤2*(J+1)+n+3, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j c w‖≤C*A^j) →
      R^B*‖∫ u : ℝ, (Ψ u:ℂ)*
        sphereAxisIntegralND (((2:ℝ)^v*dist x.1 x.2)*u) (euclideanPairDirectionND x) b*
          conj (sphereAxisIntegralND (((2:ℝ)^v*dist y.1 y.2)*u) (euclideanPairDirectionND y) c)‖≤R^(-T) := by
  obtain ⟨J,hJ⟩ := sphere_noncomparable_zero_rapid_euclideanND (n := n) hΨ hs C hC hθ hβ B T
  refine ⟨J,?_⟩
  filter_upwards [hJ,eventually_gt_atTop (0:ℝ)] with R hJ hR
  intro b c x y A v hb hc hA hAup hΛ hrat hsep hbd hcd
  have hz (z : EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) :
      (2:ℝ)^v*dist z.1 z.2=0 ∨ ‖euclideanPairDirectionND z‖=1 := by
    by_cases hd : dist z.1 z.2=0
    · exact Or.inl (by rw [hd,mul_zero])
    · exact Or.inr (euclideanPairDirectionND_norm z (lt_of_le_of_ne dist_nonneg (Ne.symm hd)))
  have hb0 (w : EuclideanSpace ℝ (Fin (n+1))) (hw : ‖w‖=1) : ‖b w‖≤C := by
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hbd 0 (by omega) w hw
  have hc0 (w : EuclideanSpace ℝ (Fin (n+1))) (hw : ‖w‖=1) : ‖c w‖≤C := by
    simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hcd 0 (by omega) w hw
  have h2 : 0<(2:ℝ)^v := Real.rpow_pos_of_pos (by norm_num) v
  rcases le_total (dist y.1 y.2) (dist x.1 x.2) with hxy|hyx
  · simp only [max_eq_left hxy,min_eq_right hxy] at hΛ hrat hsep
    have hxpos : 0<dist x.1 x.2 := (mul_pos_iff_of_pos_left h2).mp
      ((Real.rpow_pos_of_pos hR β).trans_le hΛ)
    apply hJ b c (euclideanPairDirectionND x) (euclideanPairDirectionND y) A _ _ hb hc.continuous
      (euclideanPairDirectionND_norm _ hxpos) (hz y) hA hAup hΛ hrat (by positivity) _ hbd hc0
    nlinarith [mul_le_mul_of_nonneg_left hsep h2.le]
  · simp only [max_eq_right hyx,min_eq_left hyx] at hΛ hrat hsep
    rw [euclidean_radial_pair_swap_normND]
    have hypos : 0<dist y.1 y.2 := (mul_pos_iff_of_pos_left h2).mp
      ((Real.rpow_pos_of_pos hR β).trans_le hΛ)
    apply hJ c b (euclideanPairDirectionND y) (euclideanPairDirectionND x) A _ _ hc hb.continuous
      (euclideanPairDirectionND_norm _ hypos) (hz x) hA hAup hΛ hrat (by positivity) _ hcd hb0
    nlinarith [mul_le_mul_of_nonneg_left hsep h2.le]

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
