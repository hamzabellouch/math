import OAI.Probability.InvariantIsing.Magnetic.MagneticRealProfile
import Mathlib.Analysis.Convex.Jensen

namespace OAI

/-! Transporting a magnetization profile through a finite coupling of
field populations increases its grouped constrained entropy. -/
noncomputable section
open Set
open scoped BigOperators
namespace InvariantIsing

def transportedMagnetization {A B : Type*} [Fintype A]
    (w : A → B → ℝ) (δ : B → ℝ) (mag : A → ℝ) (b : B) : ℝ :=
  (∑ a, w a b*mag a)/δ b

lemma transportedMagnetization_radius {A B : Type*} [Fintype A]
    (w : A → B → ℝ) (δ : B → ℝ) (mag : A → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hδ : ∀ b, 0 < δ b) (hcol : ∀ b, ∑ a, w a b=δ b)
    {s : ℝ} (hm : ∀ a, |mag a| ≤ s) (b : B) :
    |transportedMagnetization w δ mag b| ≤ s := by
  rw [transportedMagnetization,abs_div,abs_of_pos (hδ b)]
  apply (div_le_iff₀ (hδ b)).mpr
  calc
    |∑ a, w a b*mag a| ≤ ∑ a, |w a b*mag a| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, w a b*|mag a| := by simp_rw [abs_mul,abs_of_nonneg (hw _ _)]
    _ ≤ ∑ a, w a b*s := Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hm a) (hw a b))
    _ = s*δ b := by rw [← Finset.sum_mul,hcol,mul_comm]

lemma transportedMagnetization_groupValue {A B : Type*} [Fintype A] [Fintype B]
    (w : A → B → ℝ) (γ : A → ℝ) (δ : B → ℝ) (mag : A → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hδ : ∀ b, 0 < δ b)
    (hrow : ∀ a, ∑ b, w a b=γ a) (hcol : ∀ b, ∑ a, w a b=δ b)
    (hm : ∀ a, |mag a| ≤ 1) (h : FieldStep) :
    magneticGroupValue γ mag h ≤
      magneticGroupValue δ (transportedMagnetization w δ mag) h := by
  have hJ b : (∑ a, w a b*constrainedFieldValue h (mag a)) ≤
      δ b*constrainedFieldValue h (transportedMagnetization w δ mag b) := by
    have hj := (concaveOn_constrainedFieldValue_magnetization h).le_map_sum
      (t := Finset.univ) (w := fun a => w a b/δ b) (p := mag)
      (fun a _ => div_nonneg (hw a b) (hδ b).le)
      (by rw [← Finset.sum_div,hcol,div_self (hδ b).ne'])
      (fun a _ => abs_le.mp (hm a))
    simp only [smul_eq_mul] at hj
    have he : (∑ a, w a b/δ b*mag a)=transportedMagnetization w δ mag b := by
      simp only [transportedMagnetization,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [he] at hj
    have hl : (∑ a, w a b/δ b*constrainedFieldValue h (mag a))=
        (∑ a, w a b*constrainedFieldValue h (mag a))/δ b := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [hl] at hj
    simpa only [mul_comm] using (div_le_iff₀ (hδ b)).mp hj
  calc
    magneticGroupValue γ mag h = ∑ a, ∑ b, w a b*constrainedFieldValue h (mag a) := by
      simp_rw [magneticGroupValue,← Finset.sum_mul,hrow]
    _ = ∑ b, ∑ a, w a b*constrainedFieldValue h (mag a) := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun b _ => hJ b)

lemma transportedMagnetization_variational {A B : Type*} [Fintype A] [Fintype B]
    (R : ℝ → ℝ) (w : A → B → ℝ) (γ : A → ℝ) (δ : B → ℝ) (mag : A → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hδ : ∀ b, 0 < δ b)
    (hrow : ∀ a, ∑ b, w a b=γ a) (hcol : ∀ b, ∑ a, w a b=δ b)
    (hm : ∀ a, |mag a| ≤ 1) :
    magneticVariationalFunctional R γ mag ≤
      magneticVariationalFunctional R δ (transportedMagnetization w δ mag) := by
  apply iInf_mono
  intro p
  apply add_le_add _ le_rfl
  apply iSup_mono
  intro h
  apply EReal.coe_le_coe
  exact add_le_add (transportedMagnetization_groupValue w γ δ mag hw hδ hrow hcol hm h) le_rfl

end InvariantIsing

end

end OAI
