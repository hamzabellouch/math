import Mathlib

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I : Type} [DecidableEq I]

theorem nearest_fractional (U : Finset I) (y d : I → ℚ) (t : ℚ)
    (hy : ∀ i ∈ U, 0 ≤ y i) (ht : 0 ≤ t) (hm : t ≤ ∑ i ∈ U, y i) :
    ∃ x : I → ℚ,
      (∀ i, i ∉ U → x i=0) ∧ (∀ i ∈ U, 0 ≤ x i ∧ x i ≤ y i) ∧
      (∑ i ∈ U, x i)=t ∧
      ∀ i ∈ U, ∀ a ∈ U, 0 < x i → x a < y a → d i ≤ d a := by
  revert t hy
  refine U.strongInductionOn ?_
  intro U ih t hy ht hm
  by_cases hU : U.Nonempty
  · obtain ⟨a,ha,hmin⟩ := U.exists_min_image d hU
    by_cases hsmall : t ≤ y a
    · let x : I → ℚ := fun i => if i=a then t else 0
      refine ⟨x,?_,?_,?_,?_⟩
      · intro i hi
        change (if i=a then t else 0)=0
        exact ite_eq_right (fun (he : i=a) => hi (he.symm ▸ ha))
      · intro i hi
        by_cases he : i=a
        · subst i
          simpa only [x,ite_eq_left rfl] using And.intro ht hsmall
        · simp only [x,ite_eq_right he]
          exact ⟨le_rfl,hy i hi⟩
      · simp only [x,sum_ite_eq',ite_eq_left ha]
      · intro i hi b hb hix _
        have hei : i=a := by
          by_contra he
          simp only [x,ite_eq_right he,lt_self_iff_false] at hix
        subst i
        exact hmin b hb
    · have hlt : y a < t := lt_of_not_ge hsmall
      have hm' : t-y a ≤ ∑ i ∈ U.erase a, y i := by
        have hs := sum_erase_add U y ha
        linarith only [hm,hs]
      obtain ⟨z,hzout,hzcap,hzsum,hzorder⟩ := ih (U.erase a) (erase_ssubset ha)
        (t-y a) (fun i hi => hy i (mem_of_mem_erase hi)) (sub_nonneg.mpr hlt.le) hm'
      let x : I → ℚ := Function.update z a (y a)
      have hxa : x a=y a := Function.update_self _ _ _
      have hxi : ∀ i, i ≠ a → x i=z i := fun i hi => Function.update_of_ne hi _ _
      refine ⟨x,?_,?_,?_,?_⟩
      · intro i hi
        rw [hxi i (fun (he : i=a) => hi (he.symm ▸ ha))]
        exact hzout i (fun he => hi (mem_of_mem_erase he))
      · intro i hi
        by_cases he : i=a
        · subst i; rw [hxa]; exact ⟨hy a ha,le_rfl⟩
        · rw [hxi i he]
          exact hzcap i (mem_erase.mpr ⟨he,hi⟩)
      · rw [← sum_erase_add U x ha,hxa]
        have he : (∑ i ∈ U.erase a, x i)=∑ i ∈ U.erase a, z i :=
          sum_congr rfl (fun i hi => hxi i (mem_erase.mp hi).1)
        rw [he,hzsum]
        ring
      · intro i hi b hb hix hbx
        by_cases he : i=a
        · subst i; exact hmin b hb
        · have hbe : b ≠ a := by
            intro hb'; subst b; rw [hxa] at hbx; exact lt_irrefl _ hbx
          rw [hxi i he] at hix
          rw [hxi b hbe] at hbx
          exact hzorder i (mem_erase.mpr ⟨he,hi⟩) b (mem_erase.mpr ⟨hbe,hb⟩) hix hbx
  · have he : U=∅ := not_nonempty_iff_eq_empty.mp hU
    subst U
    have ht0 : t=0 := le_antisymm (by simpa only [sum_empty] using hm) ht
    refine ⟨fun _ => 0,fun _ _ => rfl,?_,?_,?_⟩ <;> simp [ht0]

omit [DecidableEq I] in

theorem nearest_fractional_cheaper (U : Finset I) (y d x w : I → ℚ) {t : ℚ}
    (ht : 0 < t) (hx : ∀ i ∈ U, 0 ≤ x i) (hw : ∀ i ∈ U, 0 ≤ w i ∧ w i ≤ y i)
    (hxs : ∑ i ∈ U, x i=t) (hws : ∑ i ∈ U, w i=t)
    (horder : ∀ i ∈ U, ∀ a ∈ U, 0 < x i → x a < y a → d i ≤ d a) :
    (∑ i ∈ U, x i*d i) ≤ ∑ i ∈ U, w i*d i := by
  let S := U.filter (fun i => 0 < x i)
  have hS : S.Nonempty := by
    by_contra hn
    have hz : ∀ i ∈ U, x i=0 := by
      intro i hi
      apply le_antisymm _ (hx i hi)
      exact le_of_not_gt (fun hh => hn ⟨i,mem_filter.mpr ⟨hi,hh⟩⟩)
    have hs : (∑ i ∈ U, x i)=0 := sum_eq_zero hz
    linarith only [hs,hxs,ht]
  obtain ⟨a,ha,hmax⟩ := S.exists_max_image d hS
  let R := d a
  have hamin := (mem_filter.mp ha).1
  have hapos := (mem_filter.mp ha).2
  have hterm : ∀ i ∈ U, (x i-w i)*(d i-R) ≤ 0 := by
    intro i hi
    by_cases he : x i=w i
    · rw [he,sub_self,zero_mul]
    · by_cases hle : x i ≤ w i
      · have hl : x i < y i := (lt_of_le_of_ne hle he).trans_le (hw i hi).2
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle)
          (sub_nonneg.mpr (horder a hamin i hi hapos hl))
      · have hgt : w i < x i := lt_of_not_ge hle
        have hxpos : 0 < x i := (hw i hi).1.trans_lt hgt
        exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hgt.le)
          (sub_nonpos.mpr (hmax i (mem_filter.mpr ⟨hi,hxpos⟩)))
  have hs := sum_nonpos hterm
  have hid : (∑ i ∈ U, (x i-w i)*(d i-R))=
      (∑ i ∈ U, x i*d i)-(∑ i ∈ U, w i*d i) := by
    simp_rw [sub_mul,mul_sub]
    rw [sum_sub_distrib,sum_sub_distrib,sum_sub_distrib,← sum_mul,← sum_mul,hxs,hws]
    ring
  rw [hid] at hs
  exact sub_nonpos.mp hs

end MetricKMedian.Preparation
end
end

end OAI
