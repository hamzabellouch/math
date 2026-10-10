import Mathlib
import OAI.Geometry.PrescribedRicci.KahlerGradientEnergy

namespace OAI

/-! Kahler Gradient Coercivity. -/

noncomputable section
open Matrix Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder Classical Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ}

lemma holRealForm_injective : Function.Injective
    (fun L : Coordinates d →L[ℝ] ℝ => fun j => holRealForm j L) := by
  suffices hz : ∀ L : Coordinates d →L[ℝ] ℝ, (∀ j, holRealForm j L = 0) → L = 0 by
    intro L M he
    have hh := hz (L-M) (by intro j; simp only [map_sub]; exact sub_eq_zero.mpr (congrFun he j))
    exact sub_eq_zero.mp hh
  intro L hL
  have hre (j : Fin d) : L (coordinateVector j) = 0 := by
    have hh := congrArg Complex.re (hL j)
    simp [holRealForm] at hh
    linarith
  have him (j : Fin d) : L (Complex.I • coordinateVector j) = 0 := by
    have hh := congrArg Complex.im (hL j)
    simp [holRealForm] at hh
    linarith
  apply ContinuousLinearMap.ext
  intro v
  have he : v = ∑ j, ((v j).re • coordinateVector j + (v j).im • (Complex.I • coordinateVector j)) := by
    ext k
    simp only [coordinateVector, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Complex.real_smul, Pi.single_apply]
    simp [mul_ite, Finset.sum_add_distrib]
  rw [he, map_sum]
  simp only [map_add, map_smul, hre, him, smul_zero, add_zero, Finset.sum_const_zero,
    _root_.zero_apply]

def formEnergy (H : Matrix (Fin d) (Fin d) ℂ) (L : Coordinates d →L[ℝ] ℝ) : ℝ :=
  (gradientPair H (fun j => holRealForm j L) (fun j => holRealForm j L)).re

lemma formEnergy_pos (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.PosDef)
    (L : Coordinates d →L[ℝ] ℝ) (hL : L ≠ 0) : 0 < formEnergy H L := by
  let p := fun j => holRealForm j L
  have hp : p ≠ 0 := by
    intro hh
    apply hL
    apply holRealForm_injective
    funext j
    change holRealForm j L = holRealForm j 0
    rw [map_zero]
    exact congrFun hh j
  have hps : star p ≠ 0 := by simpa using hp
  have hh := hH.inv.re_dotProduct_pos hps
  have he : gradientPair H p p = star (star p) ⬝ᵥ (H⁻¹ *ᵥ star p) := by
    simp only [gradientPair, dotProduct, Matrix.mulVec, Pi.star_apply, star_star, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  change 0 < (gradientPair H p p).re
  rw [he]
  exact hh

lemma formEnergy_smul (H : Matrix (Fin d) (Fin d) ℂ) (c : ℝ)
    (L : Coordinates d →L[ℝ] ℝ) : formEnergy H (c • L) = c^2 * formEnergy H L := by
  unfold formEnergy gradientPair
  simp only [map_smul, Complex.real_smul, star_mul, Complex.star_def, Complex.conj_ofReal]
  have he : (∑ j, ∑ i, H⁻¹ j i * (star ((c : ℂ) * holRealForm i L)) * ((c : ℂ) * holRealForm j L)) =
      (c : ℂ)^2 * ∑ j, ∑ i, H⁻¹ j i * star (holRealForm i L) * holRealForm j L := by
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal] at he
  rw [he, ← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

variable {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma continuousOn_formEnergy (g : KaehlerMetric A) (i : Fin A.count) :
    ContinuousOn (fun z : Coordinates d × (Coordinates d →L[ℝ] ℝ) => formEnergy (g.matrix i z.1) z.2)
      ((A.chart i).target ×ˢ Set.univ) := by
  have hH : ContinuousOn (fun z => (g.matrix i z)⁻¹) (A.chart i).target := by
    intro z hz
    exact (MongeAmpere.contDiffAt_inv _ (ne_of_gt (g.positive i z hz).det_pos)).continuousAt.comp_continuousWithinAt
      ((g.smooth i).continuousOn z hz)
  unfold formEnergy gradientPair
  apply Complex.continuous_re.comp_continuousOn
  apply continuousOn_finsetSum
  intro j _
  apply continuousOn_finsetSum
  intro k _
  exact (((continuousOn_pi.mp (continuousOn_pi.mp hH j) k).comp continuous_fst.continuousOn
    (fun z hz => hz.1)).mul ((holRealForm k).continuous.comp continuous_snd).star.continuousOn).mul
      ((holRealForm j).continuous.comp continuous_snd).continuousOn

lemma compact_gradient_coercivity (g : KaehlerMetric A) (i : Fin A.count)
    {K : Set (Coordinates d)} (hK : IsCompact K) (hs : K ⊆ (A.chart i).target) :
    ∃ a : ℝ, 0 < a ∧ ∀ z ∈ K, ∀ L : Coordinates d →L[ℝ] ℝ,
      a * ‖L‖^2 ≤ formEnergy (g.matrix i z) L := by
  let S : Set (Coordinates d × (Coordinates d →L[ℝ] ℝ)) := K ×ˢ Metric.sphere 0 1
  have hc : IsCompact S := hK.prod (isCompact_sphere 0 1)
  have hcF := (g.continuousOn_formEnergy i).mono (show S ⊆ (A.chart i).target ×ˢ univ from
    fun z hz => ⟨hs hz.1, mem_univ _⟩)
  by_cases hn : S.Nonempty
  · obtain ⟨⟨z₀,L₀⟩,hm,hlow⟩ := hc.exists_isMinOn hn hcF
    have hL₀ : L₀ ≠ 0 := by
      intro h
      have := hm.2
      simp [h] at this
    refine ⟨formEnergy (g.matrix i z₀) L₀, formEnergy_pos _ (g.positive i z₀ (hs hm.1)) L₀ hL₀, ?_⟩
    intro z hz L
    by_cases hL : L = 0
    · simp [hL, formEnergy, gradientPair]
    · have hnorm : 0 < ‖L‖ := norm_pos_iff.mpr hL
      have hnL : ‖(‖L‖⁻¹ : ℝ) • L‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']
      have hh := hlow (show (z,(‖L‖⁻¹ : ℝ) • L) ∈ S from
        ⟨hz, by simpa only [Metric.mem_sphere, dist_zero_right] using hnL⟩)
      change formEnergy (g.matrix i z₀) L₀ ≤ formEnergy (g.matrix i z) ((‖L‖⁻¹ : ℝ) • L) at hh
      rw [formEnergy_smul] at hh
      have ht := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖L‖)
      have he : ‖L‖⁻¹ ^2 * formEnergy (g.matrix i z) L * ‖L‖^2 = formEnergy (g.matrix i z) L := by
        calc
          _ = formEnergy (g.matrix i z) L * (‖L‖⁻¹ ^2 * ‖L‖^2) := by ring
          _ = _ := by rw [← mul_pow, inv_mul_cancel₀ hnorm.ne']; simp
      rwa [he] at ht
  · refine ⟨1,by norm_num,fun z hz L => ?_⟩
    by_cases hL : L = 0
    · simp [hL, formEnergy, gradientPair]
    · have hnorm : 0 < ‖L‖ := norm_pos_iff.mpr hL
      have hnL : ‖(‖L‖⁻¹ : ℝ) • L‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']
      exact (hn ⟨(z,(‖L‖⁻¹ : ℝ) • L),hz,by simpa only [Metric.mem_sphere, dist_zero_right] using hnL⟩).elim

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI
