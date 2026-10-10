import OAI.NumberTheory.JointDickman.Counting.SamplingMoments
import Mathlib.Logic.Equiv.Prod

namespace OAI

/-! # Exact disintegration of independent site laws over a chosen set -/

namespace JointDickman
open Finset PublishedInputs

section
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

noncomputable def mergeSitePartition (I : Finset ι) (a : I → Ω)
    (b : {i : ι // i ∉ I} → Ω) (i : ι) : Ω :=
  if h : i ∈ I then a ⟨i,h⟩ else b ⟨i,h⟩

omit [Fintype ι] [Fintype Ω] in
theorem mergeSitePartition_restrict (I : Finset ι) (S : ι → Ω) :
    mergeSitePartition I (fun i => S i.val) (fun i => S i.val) = S := by
  funext i
  unfold mergeSitePartition
  split_ifs <;> rfl

omit [Fintype Ω] in
theorem siteProductMass_merge (p : ι → Ω → ℝ) (I : Finset ι)
    (a : I → Ω) (b : {i : ι // i ∉ I} → Ω) :
    siteProductMass p (mergeSitePartition I a b) =
      siteProductMass (fun i : I => p i.val) a*
        siteProductMass (fun i : {i : ι // i ∉ I} => p i.val) b := by
  unfold siteProductMass
  have hh := Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ I)
    (fun i => p i (mergeSitePartition I a b i))
  apply hh.symm.trans
  apply congrArg₂ (fun a b : ℝ => a*b)
  · apply Finset.prod_congr (by ext; simp)
    intro i _
    simp only [mergeSitePartition,dite_eq_left i.property]
  · apply Finset.prod_congr rfl
    intro i _
    simp only [mergeSitePartition,dite_eq_right i.property]

/-- The exposed endpoint block is integrated outside the independent law
of all remaining sites. No probability of the exposed event is divided out. -/
theorem siteProduct_partition (p : ι → Ω → ℝ) (I : Finset ι) (F : (ι → Ω) → ℝ) :
    finiteExpectation (siteProductMass p) F =
      finiteExpectation (siteProductMass (fun i : I => p i.val)) (fun a =>
        finiteExpectation (siteProductMass (fun i : {i : ι // i ∉ I} => p i.val))
          (fun b => F (mergeSitePartition I a b))) := by
  classical
  unfold finiteExpectation
  calc
    _ = ∑ ab : (I → Ω) × ({i : ι // i ∉ I} → Ω),
        siteProductMass p (mergeSitePartition I ab.1 ab.2)*F (mergeSitePartition I ab.1 ab.2) := by
      refine Fintype.sum_equiv (Equiv.piEquivPiSubtypeProd (fun i => i ∈ I) (fun _ => Ω)) _ _ ?_
      intro S
      change siteProductMass p S*F S =
        siteProductMass p (mergeSitePartition I (fun i => S i.val) (fun i => S i.val))*
          F (mergeSitePartition I (fun i => S i.val) (fun i => S i.val))
      rw [mergeSitePartition_restrict]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [siteProductMass_merge,mul_sum,mul_assoc]

end
end JointDickman

end OAI
