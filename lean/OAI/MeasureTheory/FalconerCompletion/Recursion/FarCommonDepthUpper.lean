import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.ProfileChildCard

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Metric

lemma far_common_depth_upperND {b h k : ℕ} {D : ℝ}
    (hlo : 1/(4*(2:ℝ)^h)≤D) (hhi : D≤(2:ℝ)^k/(2:ℝ)^b) :
    b≤h+k+2 := by
  have hh := hlo.trans hhi
  have hp : 0<(2:ℝ)^b := by positivity
  have hq : 0<(4*(2:ℝ)^h) := by positivity
  have he := (div_le_div_iff₀ hq hp).mp hh
  have hpow : (2:ℝ)^b≤(2:ℝ)^(h+k+2) := by
    calc
      _ ≤ (2:ℝ)^k*(4*(2:ℝ)^h) := by simpa using he
      _ = _ := by rw [pow_add,pow_add]; ring
  exact (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp hpow

lemma mem_ambientGridCell_floorND {d : ℕ} (b : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    x∈ambientGridCell b (fun i => ⌊(2:ℝ)^b*x i⌋) := by
  apply mem_ambientGridCell_iff.mpr
  intro i
  rfl

lemma ambientGridCell_subset_of_common_pointND {d a b : ℕ} (hab : a≤b)
    {P Q : Fin d → ℤ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x∈ambientGridCell a P) (hy : x∈ambientGridCell b Q) :
    ambientGridCell b Q⊆ambientGridCell a P := by
  have hs := ambientGridCell_subset_ancestor hab Q
  have hz := hs hy
  have he : (fun i => Q i / (2:ℤ)^(b-a))=P := by
    funext i
    exact ((mem_ambientGridCell_iff.mp hz) i).symm.trans ((mem_ambientGridCell_iff.mp hx) i)
  simpa only [he] using hs

theorem exists_far_grid_coverND {d a h k : ℕ}
    (hK : 16*(d+1:ℝ)≤(2:ℝ)^k) {X Y : Fin d → ℤ}
    {x x' y y' : EuclideanSpace ℝ (Fin d)}
    (hx : x∈ambientGridCell a X) (hx' : x'∈ambientGridCell a X)
    (hy : y∈ambientGridCell a Y) (hy' : y'∈ambientGridCell a Y)
    (hfar : 1/(4*(2:ℝ)^h)≤ max (dist x x') (dist y y'))
    (hcomp : max (dist x x') (dist y y')≤2*min (dist x x') (dist y y')) :
    ∃ b∈Finset.Icc (a+1) (h+k+2),
      ∃ P P' Q Q' : Fin d → ℤ,
        x∈ambientGridCell b P ∧ x'∈ambientGridCell b P' ∧
        y∈ambientGridCell b Q ∧ y'∈ambientGridCell b Q' ∧
        ambientGridCell b P⊆ambientGridCell a X ∧
        ambientGridCell b P'⊆ambientGridCell a X ∧
        ambientGridCell b Q⊆ambientGridCell a Y ∧
        ambientGridCell b Q'⊆ambientGridCell a Y ∧
        farSeparatedGridND b ((2:ℝ)^k) P P' ∧ farSeparatedGridND b ((2:ℝ)^k) Q Q' := by
  have hD : 0< max (dist x x') (dist y y') :=
    (show 0<1/(4*(2:ℝ)^h) by positivity).trans_le hfar
  have hm : 0< min (dist x x') (dist y y') := by linarith
  have hD₁ := hm.trans_le (min_le_left _ _)
  have hD₂ := hm.trans_le (min_le_right _ _)
  have hupper : max (dist x x') (dist y y')≤(d+1:ℝ)/(2:ℝ)^a := by
    apply max_le
    · simpa only [dist_comm] using ambientGridCell_dist_le hx hx'
    · simpa only [dist_comm] using ambientGridCell_dist_le hy hy'
  have hsize : max (dist x x') (dist y y')≤(2:ℝ)^k := by
    have hs : 1≤(2:ℝ)^a := one_le_pow₀ (by norm_num)
    have hdu : (d+1:ℝ)/(2:ℝ)^a≤d+1 := div_le_self (by positivity) hs
    have hd : (0:ℝ)≤d := Nat.cast_nonneg d
    exact hupper.trans (hdu.trans (by linarith))
  obtain ⟨b,hbl₁,hbu₁,hbl₂,hbu₂,hbmax⟩ := exists_far_common_depthND hD₁ hD₂ hcomp hsize
  have hab := far_common_depth_strictND hK hbmax hupper
  have hbh := far_common_depth_upperND hfar (max_le hbu₁ hbu₂)
  let P : Fin d → ℤ := fun i => ⌊(2:ℝ)^b*x i⌋
  let P' : Fin d → ℤ := fun i => ⌊(2:ℝ)^b*x' i⌋
  let Q : Fin d → ℤ := fun i => ⌊(2:ℝ)^b*y i⌋
  let Q' : Fin d → ℤ := fun i => ⌊(2:ℝ)^b*y' i⌋
  have hxP : x∈ambientGridCell b P := mem_ambientGridCell_floorND b x
  have hxP' : x'∈ambientGridCell b P' := mem_ambientGridCell_floorND b x'
  have hyQ : y∈ambientGridCell b Q := mem_ambientGridCell_floorND b y
  have hyQ' : y'∈ambientGridCell b Q' := mem_ambientGridCell_floorND b y'
  exact ⟨b,Finset.mem_Icc.mpr ⟨hab,hbh⟩,P,P',Q,Q',hxP,hxP',hyQ,hyQ',
    ambientGridCell_subset_of_common_pointND hab.le hx hxP,
    ambientGridCell_subset_of_common_pointND hab.le hx' hxP',
    ambientGridCell_subset_of_common_pointND hab.le hy hyQ,
    ambientGridCell_subset_of_common_pointND hab.le hy' hyQ',
    farSeparatedGridND_of_lengths hK hxP hxP' hbl₁ hbu₁,
    farSeparatedGridND_of_lengths hK hyQ hyQ' hbl₂ hbu₂⟩

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
