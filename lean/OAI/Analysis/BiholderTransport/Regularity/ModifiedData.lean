import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.ActualParameter

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace WeakMTWTransport
section ModifiedData
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]

lemma modified_transform_bounds {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {a D b H : ℝ} {B : ℝ → ℝ}
    (hB : Continuous B) (hb : 0 ≤ b) (hbound : ∀ s,0 ≤ B s ∧ B s ≤ H) (x : M) :
    u x-b*H ≤ cTransform (modifiedDatum v a D b B) x ∧
      cTransform (modifiedDatum v a D b B) x ≤ u x := by
  have hw := continuous_modifiedDatum hv a D b hB
  have hshift : Continuous (fun y => v y+b*H) := by
    rw [hdual.2]
    exact (continuous_cTransform hu).add continuous_const
  have h1 := cTransform_antitone (w := fun y => v y+b*H) hw hshift
    (fun y => add_le_add_right (mul_le_mul_of_nonneg_left (hbound _).2 hb) (v y)) x
  have h2 := cTransform_antitone hv hw
    (fun y => le_add_of_nonneg_right (mul_nonneg hb (hbound _).1)) x
  rw [cTransform_add_const hv,hdual.1.symm] at h1
  rw [hdual.1.symm] at h2
  exact ⟨h1,h2⟩

lemma modified_double_bounds {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {a D b : ℝ} {B : ℝ → ℝ}
    (hB : Continuous B) (hb : 0 ≤ b) (hbound : ∀ s,0 ≤ B s) (y : M) :
    v y ≤ cTransform (cTransform (modifiedDatum v a D b B)) y ∧
      cTransform (cTransform (modifiedDatum v a D b B)) y ≤ modifiedDatum v a D b B y := by
  have hw := continuous_modifiedDatum hv a D b hB
  have h1 := cTransform_antitone hv hw
    (fun y => le_add_of_nonneg_right (mul_nonneg hb (hbound _)))
  rw [←hdual.1] at h1
  have h2 := cTransform_antitone (continuous_cTransform hw) hu h1 y
  rw [←hdual.2] at h2
  exact ⟨h2,cTransform_cTransform_le hw y⟩

lemma modified_excess_upper {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {a D b : ℝ} {Bc Bo : ℝ → ℝ}
    (hBo : Continuous Bo) (hb : 0 ≤ b) (ho : ∀ s,0 ≤ Bo s) (hc : ∀ s,Bc s ≤ 1)
    (y : M) : modifiedExcess v a D b Bc Bo y ≤ b := by
  have H := (modified_double_bounds (a := a) (D := D) hu hv hdual hBo hb ho y).1
  have Hc := mul_le_mul_of_nonneg_left (hc ((v y-a)/D)) hb
  dsimp only [modifiedExcess,modifiedDatum]
  linarith

lemma modified_contact_original_section {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {a D b H : ℝ} {B : ℝ → ℝ}
    (hB : Continuous B) (hb : 0 ≤ b) (hbound : ∀ s,0 ≤ B s ∧ B s ≤ H) {x y : M}
    (hc : contactGap (cTransform (modifiedDatum v a D b B)) (modifiedDatum v a D b B) x y=0) :
    contactGap u v x y ≤ b*H := by
  have Hg := (modified_transform_bounds (a := a) (D := D) hu hv hdual hB hb hbound x).1
  have Ho := mul_nonneg hb (hbound ((v y-a)/D)).1
  dsimp only [contactGap,modifiedDatum] at hc ⊢
  linarith only [Hg,Ho,hc]

omit [CompactSpace M] [Nonempty M] in
lemma modified_excess_at_contact {v : M → ℝ} {a D b : ℝ} {Bc Bo : ℝ → ℝ} {x y : M}
    (hc : contactGap (cTransform (modifiedDatum v a D b Bo))
      (cTransform (cTransform (modifiedDatum v a D b Bo))) x y=0) :
    modifiedExcess v a D b Bc Bo y =
      v y+b*Bc ((v y-a)/D)+cost x y+cTransform (modifiedDatum v a D b Bo) x := by
  dsimp only [contactGap] at hc
  dsimp only [modifiedExcess,modifiedDatum]
  linarith only [hc]

end ModifiedData
end WeakMTWTransport

end
end

end OAI
