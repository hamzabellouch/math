import OAI.Analysis.Pureness.GroupAlgebra.GroupRegularRepresentation

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped Classical
open scoped InnerProductSpace
variable {G : Type*}

def groupCoordinateProjection (s : Set G) : GroupOperator G :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun g => if g ∈ s then x g else 0,
        x.property.mono' (fun g => by split_ifs <;> simp)⟩
      map_add' := by
        intro x y; apply lp.ext; funext g
        change (if g ∈ s then x g+y g else 0) = (if g ∈ s then x g else 0)+(if g ∈ s then y g else 0)
        split_ifs <;> simp
      map_smul' := by
        intro c x; apply lp.ext; funext g
        change (if g ∈ s then c • x g else 0) = c • (if g ∈ s then x g else 0)
        split_ifs <;> simp }
    1 (fun x => by
      rw [one_mul]
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro g
      change ‖if g ∈ s then x g else 0‖ ≤ ‖x g‖
      split_ifs <;> simp)

lemma groupCoordinateProjection_apply (s : Set G) (x : GroupL2 G) (g : G) :
    groupCoordinateProjection s x g = if g ∈ s then x g else 0 := rfl

lemma groupCoordinateProjection_norm_le (s : Set G) : ‖groupCoordinateProjection s‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

lemma groupCoordinateProjection_star (s : Set G) : star (groupCoordinateProjection s) =
    groupCoordinateProjection s := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro g
  simp only [groupCoordinateProjection_apply]
  split_ifs <;> simp

lemma groupCoordinateProjection_compl (s : Set G) : groupCoordinateProjection sᶜ =
    1-groupCoordinateProjection s := by
  ext x g
  simp only [groupCoordinateProjection_apply, sub_apply,
    one_apply_eq_self, lp.coeFn_sub, Set.mem_compl_iff]
  by_cases hg : g ∈ s <;> simp [hg,groupCoordinateProjection_apply]

lemma groupCoordinateProjection_mul (s t : Set G) :
    groupCoordinateProjection s*groupCoordinateProjection t = groupCoordinateProjection (s ∩ t) := by
  ext x g
  simp only [mul_apply_eq_comp, groupCoordinateProjection_apply, Set.mem_inter_iff]
  by_cases hs : g ∈ s <;> by_cases ht : g ∈ t <;> simp [hs,ht]

lemma groupCoordinateProjection_disjoint (s t : Set G) (hst : Disjoint s t) :
    groupCoordinateProjection s*groupCoordinateProjection t = 0 := by
  rw [groupCoordinateProjection_mul, Set.disjoint_iff_inter_eq_empty.mp hst]
  ext x g
  simp [groupCoordinateProjection_apply]

variable [Group G]
lemma groupCoordinateProjection_conjugate (s : Set G) (k : G) :
    groupLeft k*groupCoordinateProjection s*star (groupLeft k) =
      groupCoordinateProjection ((fun g => k*g) '' s) := by
  ext x g
  simp only [mul_apply_eq_comp, groupLeft_star, groupLeft_apply,
    groupCoordinateProjection_apply, inv_inv, mul_inv_cancel_left]
  have hm : g ∈ (fun h => k*h) '' s ↔ k⁻¹*g ∈ s := by
    constructor
    · rintro ⟨h,hh,rfl⟩; simpa using hh
    · intro hg; exact ⟨k⁻¹*g,hg,mul_inv_cancel_left k g⟩
  rw [hm]

lemma groupCoordinateProjection_translation_zero (s : Set G) (k : G)
    (hs : ∀ g ∈ s, k*g ∉ s) :
    groupCoordinateProjection s*groupLeft k*groupCoordinateProjection s = 0 := by
  ext x g
  simp only [mul_apply_eq_comp, groupCoordinateProjection_apply,
    groupLeft_apply, zero_apply, lp.coeFn_zero]
  by_cases hg : g ∈ s <;> by_cases hk : k⁻¹*g ∈ s <;> simp [hg,hk]
  exact (hs (k⁻¹*g) hk (by simpa using hg)).elim
end CuntzPureness

end

end OAI
