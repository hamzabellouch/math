import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFarCoordinateTail
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteCoordinateBox

namespace OAI

/-! The finite boxes and the geometric tails bound the complete coordinate sums. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubic_finite_complement_sum {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ)
    (hc : Summable (fun p => if p∈S then 0 else f p)) :
    Summable f ∧ (∑' p,f p)=(∑ p∈S,f p)+(∑' p,if p∈S then 0 else f p) := by
  classical
  let g := fun p => if p∈S then f p else 0
  have hg : HasSum g (∑ p∈S,f p) := by
    have h : HasSum g (∑ p∈S,g p) := hasSum_sum_of_ne_finset_zero (s:=S) (f:=g) (fun p hp => by simp [g,hp])
    convert h using 1
    apply Finset.sum_congr rfl
    intro p hp
    simp [g,hp]
  have h : HasSum f ((∑ p∈S,f p)+(∑' p,if p∈S then 0 else f p)) := by
    convert hg.add hc.hasSum using 1
    funext p
    by_cases hp : p∈S <;> simp [g,hp]
  exact ⟨h.summable,h.tsum_eq⟩

lemma cubicThetaPrimary_coordinate_mass :
    Summable (fun p => if p=(0,0) then 0 else cubicThetaPrimaryTailMass p) ∧
    (∑' p,if p=(0,0) then 0 else cubicThetaPrimaryTailMass p)<13/200 := by
  classical
  let f := fun p : CubicThetaIntegerPoint => if p=(0,0) then 0 else cubicThetaPrimaryTailMass p
  have he : (fun p => if p∈cubicThetaIntegerBox 3 then 0 else f p)=
      (fun p => if 3<cubicThetaIntegerRadius p then cubicThetaPrimaryTailMass p else 0) := by
    funext p
    by_cases hr : 3<cubicThetaIntegerRadius p
    · have hm : p∉cubicThetaIntegerBox 3 := by
        intro hp; exact (not_lt_of_ge ((cubicThetaIntegerBox_mem p 3).mp hp)) hr
      have hp0 : p≠(0,0) := by intro hp; rw [hp] at hr; norm_num [cubicThetaIntegerRadius] at hr
      simp [hr,hm,f,hp0]
    · have hm := (cubicThetaIntegerBox_mem p 3).mpr (Nat.le_of_not_gt hr)
      simp [hr,hm]
  have hc : Summable (fun p => if p∈cubicThetaIntegerBox 3 then 0 else f p) := by
    rw [he]
    exact cubicThetaPrimary_far_tail.1
  have h := cubic_finite_complement_sum (cubicThetaIntegerBox 3) f hc
  refine ⟨h.1,?_⟩
  rw [h.2,he]
  have hb := cubicThetaPrimaryBox_sum
  have ht := cubicThetaPrimary_far_tail.2
  change (∑ p∈cubicThetaIntegerBox 3,if p=(0,0) then 0 else cubicThetaPrimaryTailMass p)+_<_
  linarith

lemma cubicThetaRamified_coordinate_mass :
    Summable (fun p => if p=(0,0) then 0 else cubicThetaRamifiedTailMass p) ∧
    (∑' p,if p=(0,0) then 0 else cubicThetaRamifiedTailMass p)<9/2000 := by
  classical
  let f := fun p : CubicThetaIntegerPoint => if p=(0,0) then 0 else cubicThetaRamifiedTailMass p
  have he : (fun p => if p∈cubicThetaIntegerBox 2 then 0 else f p)=
      (fun p => if 2<cubicThetaIntegerRadius p then cubicThetaRamifiedTailMass p else 0) := by
    funext p
    by_cases hr : 2<cubicThetaIntegerRadius p
    · have hm : p∉cubicThetaIntegerBox 2 := by
        intro hp; exact (not_lt_of_ge ((cubicThetaIntegerBox_mem p 2).mp hp)) hr
      have hp0 : p≠(0,0) := by intro hp; rw [hp] at hr; norm_num [cubicThetaIntegerRadius] at hr
      simp [hr,hm,f,hp0]
    · have hm := (cubicThetaIntegerBox_mem p 2).mpr (Nat.le_of_not_gt hr)
      simp [hr,hm]
  have hc : Summable (fun p => if p∈cubicThetaIntegerBox 2 then 0 else f p) := by
    rw [he]
    exact cubicThetaRamified_far_tail.1
  have h := cubic_finite_complement_sum (cubicThetaIntegerBox 2) f hc
  refine ⟨h.1,?_⟩
  rw [h.2,he]
  have hb := cubicThetaRamifiedBox_sum
  have ht := cubicThetaRamified_far_tail.2
  change (∑ p∈cubicThetaIntegerBox 2,if p=(0,0) then 0 else cubicThetaRamifiedTailMass p)+_<_
  linarith

end CubicFirstMoment

end

end OAI
