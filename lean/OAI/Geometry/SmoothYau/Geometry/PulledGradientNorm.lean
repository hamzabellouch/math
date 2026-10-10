import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.PulledGradient

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma coordinateCovariantSecond_apply
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {f : E → V}
    (hf : ContDiff ℝ ∞ f) (x v w : E) :
    coordinateCovariantSecond Γ f x v w =
      fderiv ℝ (fun z => fderiv ℝ f z w) x v - fderiv ℝ f x (Γ x v w) := by
  rw [second_directional_eq hf]
  rfl

lemma coordinateCovariantSecond_norm_bound
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (f : E → V) (x : E) :
    ‖coordinateCovariantSecond Γ f x‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) x‖ + ‖fderiv ℝ f x‖ * ‖Γ x‖ := by
  apply (coordinateCovariantSecond Γ f x).opNorm_le_bound₂ (by positivity)
  intro v w
  change ‖fderiv ℝ (fderiv ℝ f) x v w - fderiv ℝ f x (Γ x v w)‖ ≤ _
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) x v w‖ + ‖fderiv ℝ f x (Γ x v w)‖ := norm_sub_le _ _
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ * ‖v‖ * ‖w‖ +
        ‖fderiv ℝ f x‖ * (‖Γ x‖ * ‖v‖ * ‖w‖) :=
      add_le_add ((fderiv ℝ (fderiv ℝ f) x).le_opNorm₂ v w)
        (((fderiv ℝ f x).le_opNorm (Γ x v w)).trans
          (mul_le_mul_of_nonneg_left ((Γ x).le_opNorm₂ v w) (norm_nonneg _)))
    _ = _ := by ring

theorem corrugation_covariant_second
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (c N : ℝ) (x v w : E) :
    coordinateCovariantSecond Γ (fun z => ψ z+c*(χ z*F (N • y z))) x v w =
      coordinateCovariantSecond Γ ψ x v w +
      c*N^2*χ x*fderiv ℝ (fderiv ℝ F) (N • y x) (fderiv ℝ y x v) (fderiv ℝ y x w) +
      c*N*χ x*fderiv ℝ F (N • y x) (coordinateCovariantSecond Γ y x v w) +
      c*N*fderiv ℝ χ x v*fderiv ℝ F (N • y x) (fderiv ℝ y x w) +
      c*N*fderiv ℝ χ x w*fderiv ℝ F (N • y x) (fderiv ℝ y x v) +
      c*F (N • y x)*coordinateCovariantSecond Γ χ x v w := by
  have hP : ContDiff ℝ ∞ (fun z => ψ z+c*(χ z*F (N • y z))) :=
    hψ.add (contDiff_const.mul (hχ.mul (hF.comp (hy.const_smul N))))
  have hfirst : fderiv ℝ (fun z => ψ z+c*(χ z*F (N • y z))) x (Γ x v w) =
      fderiv ℝ ψ x (Γ x v w) + c*fderiv ℝ χ x (Γ x v w)*F (N • y x) +
      c*χ x*N*fderiv ℝ F (N • y x) (fderiv ℝ y x (Γ x v w)) := by
    convert corrugation_first hψ hχ hF hy c N x (Γ x v w) using 1; congr 2
    funext z
    ring
  rw [coordinateCovariantSecond_apply Γ hP,
    corrugation_second hψ hχ hF hy,hfirst,
    coordinateCovariantSecond_apply Γ hψ,
    coordinateCovariantSecond_apply Γ hy,
    coordinateCovariantSecond_apply Γ hχ,map_sub]
  ring

def corrugationSecondRemainder
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (ψ χ : E → ℝ) (F : V → ℝ) (y : E → V)
    (d N : ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  coordinateCovariantSecond Γ (fun z => ψ z+(d/N)*(χ z*F (N • y z))) x -
    coordinateCovariantSecond Γ ψ x -
      (d*N*χ x) • (fderiv ℝ (fderiv ℝ F) (N • y x)).bilinearComp
        (fderiv ℝ y x) (fderiv ℝ y x)

lemma corrugationSecondRemainder_apply
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (d N : ℝ) (hN : N ≠ 0)
    (x v w : E) :
    corrugationSecondRemainder Γ ψ χ F y d N x v w =
      d*χ x*fderiv ℝ F (N • y x) (coordinateCovariantSecond Γ y x v w) +
      d*fderiv ℝ χ x v*fderiv ℝ F (N • y x) (fderiv ℝ y x w) +
      d*fderiv ℝ χ x w*fderiv ℝ F (N • y x) (fderiv ℝ y x v) +
      (d/N)*F (N • y x)*coordinateCovariantSecond Γ χ x v w := by
  change coordinateCovariantSecond Γ _ x v w - coordinateCovariantSecond Γ ψ x v w -
    (d*N*χ x)*fderiv ℝ (fderiv ℝ F) (N • y x) (fderiv ℝ y x v) (fderiv ℝ y x w) = _
  rw [corrugation_covariant_second Γ hψ hχ hF hy]
  field_simp [hN]
  ring

theorem corrugationSecondRemainder_norm_bound
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (d N : ℝ) (hN : N ≠ 0)
    (x : E) :
    ‖corrugationSecondRemainder Γ ψ χ F y d N x‖ ≤
      |d| * |χ x| * ‖fderiv ℝ F (N • y x)‖ * ‖coordinateCovariantSecond Γ y x‖ +
      2 * |d| * ‖fderiv ℝ χ x‖ * ‖fderiv ℝ F (N • y x)‖ * ‖fderiv ℝ y x‖ +
      |d / N| * |F (N • y x)| * ‖coordinateCovariantSecond Γ χ x‖ := by
  let DF := fderiv ℝ F (N • y x)
  let Dy := fderiv ℝ y x
  let Dχ := fderiv ℝ χ x
  let Hy := coordinateCovariantSecond Γ y x
  let Hχ := coordinateCovariantSecond Γ χ x
  apply (corrugationSecondRemainder Γ ψ χ F y d N x).opNorm_le_bound₂
    (by positivity)
  intro v w
  rw [corrugationSecondRemainder_apply Γ hψ hχ hF hy d N hN]
  have hyterm : ‖d * χ x * DF (Hy v w)‖ ≤
      |d| * |χ x| * ‖DF‖ * ‖Hy‖ * ‖v‖ * ‖w‖ := by
    simp only [norm_mul, Real.norm_eq_abs]
    calc
      _ ≤ |d| * |χ x| * (‖DF‖ * (‖Hy‖ * ‖v‖ * ‖w‖)) := by
        gcongr
        exact (DF.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (Hy.le_opNorm₂ v w) (norm_nonneg _))
      _ = _ := by ring
  have hcross (v w : E) : ‖d * Dχ v * DF (Dy w)‖ ≤
      |d| * ‖Dχ‖ * ‖DF‖ * ‖Dy‖ * ‖v‖ * ‖w‖ := by
    simp only [norm_mul, Real.norm_eq_abs]
    calc
      _ ≤ |d| * (‖Dχ‖ * ‖v‖) * (‖DF‖ * (‖Dy‖ * ‖w‖)) := by
        gcongr
        · exact Dχ.le_opNorm v
        · exact (DF.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (Dy.le_opNorm w) (norm_nonneg _))
      _ = _ := by ring
  have hχterm : ‖(d / N) * F (N • y x) * Hχ v w‖ ≤
      |d / N| * |F (N • y x)| * ‖Hχ‖ * ‖v‖ * ‖w‖ := by
    simp only [norm_mul, Real.norm_eq_abs]
    calc
      _ ≤ |d / N| * |F (N • y x)| * (‖Hχ‖ * ‖v‖ * ‖w‖) := by
        gcongr
        exact Hχ.le_opNorm₂ v w
      _ = _ := by ring
  calc
    _ ≤ (‖d * χ x * DF (Hy v w)‖ + ‖d * Dχ v * DF (Dy w)‖ +
        ‖d * Dχ w * DF (Dy v)‖) + ‖(d / N) * F (N • y x) * Hχ v w‖ :=
      (norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (|d| * |χ x| * ‖DF‖ * ‖Hy‖ * ‖v‖ * ‖w‖ +
        |d| * ‖Dχ‖ * ‖DF‖ * ‖Dy‖ * ‖v‖ * ‖w‖ +
        |d| * ‖Dχ‖ * ‖DF‖ * ‖Dy‖ * ‖w‖ * ‖v‖) +
        |d / N| * |F (N • y x)| * ‖Hχ‖ * ‖v‖ * ‖w‖ :=
      add_le_add (add_le_add (add_le_add hyterm (hcross v w)) (hcross w v)) hχterm
    _ = _ := by dsimp [DF, Dy, Dχ, Hy, Hχ]; ring

theorem corrugationSecondRemainder_uniform
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : Continuous Γ)
    {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y)
    (K : Set E) (hK : IsCompact K) (d B : ℝ) (hB : ∀ z, |F z| ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 0 < N → ∀ x ∈ K,
      ‖corrugationSecondRemainder Γ ψ χ F y d N x‖ ≤
        C * ((|χ x| + ‖fderiv ℝ χ x‖) * ‖fderiv ℝ F (N • y x)‖ + N⁻¹) := by
  obtain ⟨Y₂, hY₂⟩ := hK.exists_bound_of_continuousOn (f := coordinateCovariantSecond Γ y)
    (continuous_coordinateCovariantSecond Γ hΓ hy).continuousOn
  obtain ⟨Y₁, hY₁⟩ := hK.exists_bound_of_continuousOn (f := fderiv ℝ y)
    (hy.continuous_fderiv (by simp)).continuousOn
  obtain ⟨χ₂, hχ₂⟩ := hK.exists_bound_of_continuousOn (f := coordinateCovariantSecond Γ χ)
    (continuous_coordinateCovariantSecond Γ hΓ hχ).continuousOn
  let c₁ := |d| * |Y₂|
  let c₂ := 2 * |d| * |Y₁|
  let c₃ := |d| * |B| * |χ₂|
  let C := 1 + c₁ + c₂ + c₃
  have hc₁ : 0 ≤ c₁ := by dsimp [c₁]; positivity
  have hc₂ : 0 ≤ c₂ := by dsimp [c₂]; positivity
  have hc₃ : 0 ≤ c₃ := by dsimp [c₃]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hc₁C : c₁ ≤ C := by dsimp [C]; linarith
  have hc₂C : c₂ ≤ C := by dsimp [C]; linarith
  have hc₃C : c₃ ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro N hN x hx
  have hY₂x := (hY₂ x hx).trans (le_abs_self Y₂)
  have hY₁x := (hY₁ x hx).trans (le_abs_self Y₁)
  have hχ₂x := (hχ₂ x hx).trans (le_abs_self χ₂)
  have hBx := (hB (N • y x)).trans (le_abs_self B)
  calc
    _ ≤ |d| * |χ x| * ‖fderiv ℝ F (N • y x)‖ * ‖coordinateCovariantSecond Γ y x‖ +
        2 * |d| * ‖fderiv ℝ χ x‖ * ‖fderiv ℝ F (N • y x)‖ * ‖fderiv ℝ y x‖ +
        |d / N| * |F (N • y x)| * ‖coordinateCovariantSecond Γ χ x‖ :=
      corrugationSecondRemainder_norm_bound Γ hψ hχ hF hy d N (ne_of_gt hN) x
    _ ≤ |d| * |χ x| * ‖fderiv ℝ F (N • y x)‖ * |Y₂| +
        2 * |d| * ‖fderiv ℝ χ x‖ * ‖fderiv ℝ F (N • y x)‖ * |Y₁| +
        |d / N| * |B| * |χ₂| := by gcongr
    _ = c₁ * (|χ x| * ‖fderiv ℝ F (N • y x)‖) +
        c₂ * (‖fderiv ℝ χ x‖ * ‖fderiv ℝ F (N • y x)‖) + c₃ * N⁻¹ := by
      rw [abs_div, abs_of_pos hN]
      dsimp [c₁, c₂, c₃]
      ring
    _ ≤ C * (|χ x| * ‖fderiv ℝ F (N • y x)‖) +
        C * (‖fderiv ℝ χ x‖ * ‖fderiv ℝ F (N • y x)‖) + C * N⁻¹ := by gcongr
    _ = _ := by ring


end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped InnerProductSpace
variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ E] in
lemma pulledGradient_norm_le (j : V →L[ℝ] E) (u : E → ℝ) (x : E) :
    ‖pulledGradient j u x‖ ≤ ‖fderiv ℝ u x‖*‖j‖ := by
  rw [pulledGradient,LinearIsometryEquiv.norm_map]
  exact ContinuousLinearMap.opNorm_comp_le _ _

def pulledRadialLeading (j : V →L[ℝ] E) (y : E → ProfilePlane) (β : ℝ → ℝ)
    (b N : ℝ) (x : E) : ProfileForm V :=
  (fderiv ℝ (fderiv ℝ (periodicRadialFunction β b)) (N • y x)).bilinearComp
    ((fderiv ℝ y x).comp j) ((fderiv ℝ y x).comp j)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
lemma pulledRadialLeading_decomposition (j : V →L[ℝ] E) (y : E → ProfilePlane)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) (hβ0 : β 0 = 0)
    {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hsmall : 2*R < 1)
    (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0) (N : ℝ) (x : E) (v w : V) :
    let z := periodicRadialOffset R (N • y x)
    let D := (fderiv ℝ y x).comp j
    pulledRadialLeading j y β b N x v w =
      periodicRadialSecond β R (N • y x)*planeRadialCovector z (D v)*planeRadialCovector z (D w) +
      periodicAngularSecond β R (N • y x)*planeAngularCovector z (D v)*planeAngularCovector z (D w) := by
  have hF : ContDiff ℝ ∞ (periodicRadialFunction β b) := radial_periodic_smooth hβ hr hb hzero
  dsimp [pulledRadialLeading]
  rw [←second_directional_eq hF]
  exact periodicRadialFunction_second hβ hβ0 hr hrR hsmall hb hzero _ _ _

def pulledRadialRemainder (Γ : E → E →L[ℝ] E →L[ℝ] E) (j : V →L[ℝ] E)
    (ψ χ : E → ℝ) (y : E → ProfilePlane) (β : ℝ → ℝ) (b δ A N : ℝ) (x : E) : ProfileForm V :=
  (corrugationSecondRemainder Γ ψ χ (periodicRadialFunction β b) y (δ*A) N x).bilinearComp j j

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
lemma radialCorrugation_hessian (Γ : E → E →L[ℝ] E →L[ℝ] E) (j : V →L[ℝ] E)
    (ψ χ : E → ℝ) (y : E → ProfilePlane) (β : ℝ → ℝ) (b δ A N : ℝ) (x : E) :
    pulledHessian Γ j (radialCorrugation ψ χ y β b δ A N) x =
      pulledHessian Γ j ψ x+(N*δ*A*χ x) • pulledRadialLeading j y β b N x +
        pulledRadialRemainder Γ j ψ χ y β b δ A N x := by
  unfold radialCorrugation
  ext v w
  simp only [pulledHessian,pulledRadialLeading,pulledRadialRemainder,
    corrugationSecondRemainder,ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.comp_apply,add_apply,sub_apply,smul_apply,smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] in
lemma actual_radial_error_bound {χ : E → ℝ} {y : E → ProfilePlane}
    {β : ℝ → ℝ} (K : Set E) (hK : IsCompact K) (hχ : ContDiff ℝ ∞ χ)
    {b r R : ℝ} (hβ : ContDiff ℝ ∞ β) (hr : 0 ≤ r) (hrR : r < R)
    (hsmall : 2*R < 1) (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0)
    (δ A J : ℝ) (hJ : 0 ≤ J) :
    ∃ Ce : ℝ, 0 ≤ Ce ∧ ∀ N : ℝ, 0 < N → ∀ x ∈ K, ∀ j : V →L[ℝ] E, ‖j‖ ≤ J →
      ‖(δ*A/N*periodicRadialFunction β b (N • y x)) • pulledGradient j χ x‖ ≤ Ce/N := by
  obtain ⟨B,hB,hBF⟩ := periodicRadialFunction_bounded hβ hr hrR hsmall hb hzero
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn (hχ.continuous_fderiv (by simp)).continuousOn
  let D' := max D 0
  have hD' : 0 ≤ D' := le_max_right _ _
  refine ⟨|δ*A| *B*D'*J,by positivity,?_⟩
  intro N hN x hx j hj
  have hjp : ‖pulledGradient j χ x‖ ≤ D'*J :=
    (pulledGradient_norm_le j χ x).trans (mul_le_mul ((hD x hx).trans (le_max_left _ _)) hj
      (norm_nonneg _) hD')
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_div,abs_of_pos hN]
  calc
    _ ≤ (|δ*A|/N*B)*(D'*J) := mul_le_mul
      (mul_le_mul_of_nonneg_left (hBF _) (div_nonneg (abs_nonneg _) hN.le)) hjp
      (norm_nonneg _) (by positivity)
    _ = _ := by ring



end YauCounterexamples
end

end OAI
