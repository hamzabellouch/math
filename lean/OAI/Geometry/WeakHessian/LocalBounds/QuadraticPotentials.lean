import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile25
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X]

def compactCTransform (S : Set X) (ψ : X → ℝ) (x : X) : ℝ :=
  sInf ((fun y => dist x y^2/2-ψ y) '' S)

lemma compactCTransform_attained {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    {ψ : X → ℝ} (hψ : ContinuousOn ψ S) (x : X) :
    ∃ y ∈ S, compactCTransform S ψ x = dist x y^2/2-ψ y ∧
      ∀ z ∈ S, compactCTransform S ψ x ≤ dist x z^2/2-ψ z := by
  obtain ⟨y,hy,hm⟩ := hS.exists_isMinOn hne (((continuous_const.dist continuous_id).pow 2).div_const 2 |>.continuousOn |>.sub hψ)
  have he : compactCTransform S ψ x = dist x y^2/2-ψ y := by
    apply IsLeast.csInf_eq
    exact ⟨mem_image_of_mem _ hy,by rintro _ ⟨z,hz,rfl⟩; exact hm hz⟩
  exact ⟨y,hy,he,fun z hz => he ▸ hm hz⟩

lemma compactCTransform_le {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    {ψ : X → ℝ} (hψ : ContinuousOn ψ S) (x : X) {y : X} (hy : y ∈ S) :
    compactCTransform S ψ x+ψ y ≤ dist x y^2/2 := by
  obtain ⟨z,hz,he,hm⟩ := compactCTransform_attained hS hne hψ x
  linarith [hm y hy]

lemma half_cost_difference_bound (o x z y : X) {R : ℝ} (hy : dist y o ≤ R) :
    |dist x y^2/2-dist z y^2/2| ≤
      ((dist x o+dist z o)/2+R)*dist x z := by
  have ha := abs_dist_sub_le x z y
  have hb : dist x y+dist z y ≤ dist x o+dist z o+2*R := by
    have hx := dist_triangle x o y
    have hz := dist_triangle z o y
    rw [dist_comm o y] at hx hz
    linarith
  have hfact : dist x y^2/2-dist z y^2/2 = (dist x y-dist z y)*(dist x y+dist z y)/2 := by ring
  rw [hfact,abs_div,abs_mul,abs_of_nonneg (add_nonneg dist_nonneg dist_nonneg)]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  have H := mul_le_mul ha hb (add_nonneg dist_nonneg dist_nonneg) dist_nonneg
  nlinarith

lemma compactCTransform_difference_bound {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    {ψ : X → ℝ} (hψ : ContinuousOn ψ S) (o : X) {R : ℝ}
    (hs : S ⊆ Metric.closedBall o R) (x z : X) :
    |compactCTransform S ψ x-compactCTransform S ψ z| ≤
      ((dist x o+dist z o)/2+R)*dist x z := by
  have one (x z : X) : compactCTransform S ψ x-compactCTransform S ψ z ≤
      ((dist x o+dist z o)/2+R)*dist x z := by
    obtain ⟨y,hy,he,hm⟩ := compactCTransform_attained hS hne hψ z
    have H := compactCTransform_le hS hne hψ x hy
    have B := (le_abs_self (dist x y^2/2-dist z y^2/2)).trans (half_cost_difference_bound o x z y (hs hy))
    linarith
  apply abs_le.mpr
  constructor
  · have H := one z x
    rw [add_comm (dist z o),dist_comm z x] at H
    linarith
  · exact one x z

lemma compactCTransform_lipschitzOn_ball {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    {ψ : X → ℝ} (hψ : ContinuousOn ψ S) (o : X) (R T : ℝ≥0)
    (hs : S ⊆ Metric.closedBall o R) :
    LipschitzOnWith (T+R) (compactCTransform S ψ) (Metric.closedBall o T) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx z hz
  rw [Real.dist_eq]
  exact (compactCTransform_difference_bound hS hne hψ o hs x z).trans (by
    apply mul_le_mul_of_nonneg_right _ dist_nonneg
    change (dist x o+dist z o)/2+R ≤ (T:ℝ)+R
    change dist x o ≤ T at hx
    change dist z o ≤ T at hz
    linarith)

lemma compactCTransform_contact {S : Set X} (hS : IsCompact S) (hne : S.Nonempty)
    {φ ψ : X → ℝ} (hψ : ContinuousOn ψ S)
    (hdual : ∀ x y,φ x+ψ y ≤ dist x y^2/2) {x y : X} (hy : y ∈ S)
    (hc : φ x+ψ y = dist x y^2/2) : compactCTransform S ψ x = φ x := by
  obtain ⟨z,hz,he,hm⟩ := compactCTransform_attained hS hne hψ x
  have H := hdual x z
  have H' := compactCTransform_le hS hne hψ x hy
  linarith
end WeakHessian

end
end InlinedFile25

end OAI
