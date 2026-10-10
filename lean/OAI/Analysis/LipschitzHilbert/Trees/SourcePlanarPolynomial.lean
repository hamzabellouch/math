import OAI.Analysis.LipschitzHilbert.Trees.SourceVectorPolynomial

namespace OAI

/-! Transverse polynomial localization of actual planar vector packets.
Both coordinate frequency cutoffs are retained. -/
noncomputable section
open FourierTransform
namespace LipschitzHilbert
variable {κ : Type*} [Fintype κ]

theorem transversePolynomial_temperate (b r : ℝ) (q : ℕ) :
    Function.HasTemperateGrowth (fun z : ℝ×ℝ => (polynomialWeight b r q z.2:ℂ)) := by
  have hs : Function.HasTemperateGrowth (fun z : ℝ×ℝ => z.2) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth
  unfold polynomialWeight
  simp only [div_eq_mul_inv]
  fun_prop

def planarPolynomialLocalization (b r : ℝ) (q : ℕ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) :
    SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ) :=
  SchwartzMap.smulLeftCLM (EuclideanSpace ℂ κ)
    (fun z : ℝ×ℝ => (polynomialWeight b r q z.2:ℂ)) f

@[simp] theorem planarPolynomialLocalization_apply (b r : ℝ) (q : ℕ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (z : ℝ×ℝ) :
    planarPolynomialLocalization b r q f z=(polynomialWeight b r q z.2:ℂ) • f z :=
  SchwartzMap.smulLeftCLM_apply_apply (transversePolynomial_temperate b r q) f z

theorem planarPolynomialLocalization_norm (b r : ℝ) (q : ℕ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (z : ℝ×ℝ) :
    ‖planarPolynomialLocalization b r q f z‖=polynomialWeight b r q z.2*‖f z‖ := by
  rw [planarPolynomialLocalization_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ((polynomialWeight_one_le b r q z.2).trans' (by norm_num))]

theorem planarPolynomialLocalization_horizontal (b r : ℝ) (q : ℕ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (y : ℝ) :
    vectorHorizontalSlice (planarPolynomialLocalization b r q f) y=
      (polynomialWeight b r q y:ℂ) • vectorHorizontalSlice f y := by
  ext x k
  simp only [vectorHorizontalSlice_apply,planarPolynomialLocalization_apply,smul_apply]

theorem planarPolynomialLocalization_vertical (b r : ℝ) (q : ℕ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (x : ℝ) :
    vectorVerticalSlice (planarPolynomialLocalization b r q f) x=
      vectorPolynomialLocalization b r q (vectorVerticalSlice f x) := by
  ext y k
  simp only [vectorVerticalSlice_apply,planarPolynomialLocalization_apply,vectorPolynomialLocalization_apply]

theorem planarPolynomialLocalization_horizontal_band (b r : ℝ) (q : ℕ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (R : ℝ)
    (hf : ∀ y ξ, 𝓕 (vectorHorizontalSlice f y) ξ≠0 → |ξ|≤R) :
    ∀ y ξ, 𝓕 (vectorHorizontalSlice (planarPolynomialLocalization b r q f) y) ξ≠0 → |ξ|≤R := by
  intro y ξ hne
  by_contra hn
  have hzero : 𝓕 (vectorHorizontalSlice f y) ξ=0 := by
    by_contra h
    exact hn (hf y ξ h)
  apply hne
  rw [planarPolynomialLocalization_horizontal,fourier_smul,smul_apply,hzero,smul_zero]

theorem planarPolynomialLocalization_vertical_band (b r : ℝ) (q : ℕ)
    (f : SchwartzMap (ℝ×ℝ) (EuclideanSpace ℂ κ)) (R : ℝ)
    (hf : ∀ x η, 𝓕 (vectorVerticalSlice f x) η≠0 → |η|≤R) :
    ∀ x η, 𝓕 (vectorVerticalSlice (planarPolynomialLocalization b r q f) x) η≠0 → |η|≤R := by
  intro x η hne
  by_contra hn
  apply hne
  rw [planarPolynomialLocalization_vertical]
  apply vectorPolynomialLocalization_high b r q (vectorVerticalSlice f x) R _ η (lt_of_not_ge hn)
  intro ξ hξ
  by_contra h
  exact (not_le_of_gt hξ) (hf x ξ h)

end LipschitzHilbert

end

end OAI
