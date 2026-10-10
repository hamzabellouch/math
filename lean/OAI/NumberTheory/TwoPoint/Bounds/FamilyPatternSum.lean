import OAI.NumberTheory.TwoPoint.Bounds.PatternHarmonicSum
import OAI.NumberTheory.TwoPoint.Bounds.SplitBadWordSum

namespace OAI

/-! Reciprocal pattern sums for an arbitrary finite family of prime pools. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem same_family_patterns_reciprocal_sum {I : Type*} [Fintype I] [DecidableEq I]
    {R : ℕ} (P : I → Finset ℕ)
    (F : Finset (((j : I) → Fin R → P j))) (template : ((j : I) → Fin R → P j))
    (hpattern : ∀ w ∈ F, ∀ j i k, w j i = w j k ↔ template j i = template j k) :
    (∑ w ∈ F, (∏ j, ∏ p ∈ univ.image (w j), (p.val : ℝ)⁻¹)) ≤
      ∏ j, primeHarmonicMass (P j) ^ (univ.image (template j)).card := by
  let C (j : I) := univ.image (template j)
  let rep (j : I) (c : C j) : Fin R := Classical.choose (mem_image.mp c.property)
  have hrep (j : I) (c : C j) : template j (rep j c) = c.val :=
    (Classical.choose_spec (mem_image.mp c.property)).2
  let classify (j : I) (i : Fin R) : C j :=
    ⟨template j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩
  have hconstant (w : ((j : I) → Fin R → P j)) (hw : w ∈ F) (j : I) (i : Fin R) :
      w j i = w j (rep j (classify j i)) :=
    (hpattern w hw j i _).mpr (hrep j (classify j i)).symm
  let encode (w : ((j : I) → Fin R → P j)) : (j : I) → C j → P j :=
    fun j c => w j (rep j c)
  have hinj : Set.InjOn encode F := by
    intro w hw v hv he
    funext j i
    exact (hconstant w hw j i).trans
      ((congrFun (congrFun he j) (classify j i)).trans (hconstant v hv j i).symm)
  have hweight (w : ((j : I) → Fin R → P j)) (hw : w ∈ F) :
      (∏ j, ∏ p ∈ univ.image (w j), (p.val : ℝ)⁻¹) = ∏ j, ∏ c : C j, ((encode w j c).val : ℝ)⁻¹ := by
    apply prod_congr rfl
    intro j _
    have himage : univ.image (fun c : C j => w j (rep j c)) = univ.image (w j) := by
      ext p
      constructor
      · rintro hp
        obtain ⟨c, _, rfl⟩ := mem_image.mp hp
        exact mem_image.mpr ⟨rep j c, mem_univ _, rfl⟩
      · rintro hp
        obtain ⟨i, _, rfl⟩ := mem_image.mp hp
        exact mem_image.mpr ⟨classify j i, mem_univ _, (hconstant w hw j i).symm⟩
    rw [← himage, prod_image]
    intro c _ d _ hcd
    apply Subtype.ext
    exact (hrep j c).symm.trans (((hpattern w hw j _ _).mp hcd).trans (hrep j d))
  calc
    _ = ∑ z ∈ F.image encode, ∏ j, ∏ c : C j, ((z j c).val : ℝ)⁻¹ := by
      rw [sum_image hinj]
      exact sum_congr rfl hweight
    _ ≤ ∑ z : (j : I) → C j → P j, ∏ j, ∏ c : C j, ((z j c).val : ℝ)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro z _ _
      positivity
    _ = ∏ j, ∑ z : C j → P j, ∏ c, ((z c).val : ℝ)⁻¹ := by rw [Fintype.prod_sum]
    _ = _ := by
      apply prod_congr rfl
      intro j _
      simpa only [Fintype.card_coe, C] using sum_reciprocal_assignments (ι := C j) (P j)

end TwoPointCorrelations

end OAI
