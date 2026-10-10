import OAI.Geometry.SurfaceImmersion.Whitney.OrderedArcSeparation
import Mathlib.Topology.UnitInterval

namespace OAI

/-! Exact compact subarc images under extension of a unit-interval path. -/
noncomputable section
open Set unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {N : Type*} {Γ : I → N}

lemma unitInterval_extension_injective (hΓ : Function.Injective Γ) :
    (Icc (0:ℝ) 1).InjOn (Γ ∘ projIcc 0 1 zero_le_one) := by
  intro s hs t ht he
  have hh := congrArg Subtype.val (hΓ he)
  simpa only [projIcc_of_mem zero_le_one hs,projIcc_of_mem zero_le_one ht] using hh

lemma unitInterval_extension_image {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (Γ ∘ projIcc 0 1 zero_le_one) '' Icc a b =
      Γ '' {t : I | a ≤ (t:ℝ) ∧ (t:ℝ) ≤ b} := by
  apply Set.Subset.antisymm
  · rintro y ⟨t,ht,rfl⟩
    have ht01 : t ∈ Icc (0:ℝ) 1 := ⟨ha.trans ht.1,ht.2.trans hb⟩
    refine ⟨projIcc 0 1 zero_le_one t,?_,rfl⟩
    simpa only [mem_ofPred_eq,mem_Icc,projIcc_of_mem zero_le_one ht01] using ht
  · rintro y ⟨t,ht,rfl⟩
    refine ⟨(t:ℝ),ht,?_⟩
    change Γ (projIcc 0 1 zero_le_one t) = Γ t
    rw [projIcc_val]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
