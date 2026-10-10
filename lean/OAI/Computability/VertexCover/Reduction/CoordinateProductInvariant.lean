import Mathlib
import OAI.Computability.VertexCover.Reduction.ConditionNested

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Restriction.EnergyForm.Projection
open scoped BigOperators
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {I C T : Type*} [DecidableEq I]

def coordinateKey (c0 : C) (i : I) (q : C → T) (s : I → C) :=
  (Function.update s i c0, q (s i))

@[simp] theorem coordinateKey_update (c0 : C) (i : I) (q : C → T)
    (s : I → C) (c : C) :
    coordinateKey c0 i q (Function.update s i c) = (Function.update s i c0, q c) := by
  simp [coordinateKey]

theorem coordinateKey_eq_iff (c0 : C) (i : I) (q : C → T) (s t : I → C) :
    coordinateKey c0 i q s = coordinateKey c0 i q t ↔
      (∀ j, j ≠ i → s j = t j) ∧ q (s i) = q (t i) := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, congrArg Prod.snd h⟩
    have he := congrFun (congrArg Prod.fst h) j
    simpa only [coordinateKey, Function.update_of_ne hj] using he
  · rintro ⟨h, hq⟩
    apply Prod.ext _ hq
    change Function.update s i c0 = Function.update t i c0
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp only [Function.update_of_ne hj, h j hj]

variable [Fintype I] [Fintype C]

open Classical in
theorem coordinateKey_fiber (c0 : C) (i : I) (q : C → T) (s : I → C) :
    (Finset.univ.filter (fun t => coordinateKey c0 i q t = coordinateKey c0 i q s)) =
      (Finset.univ.filter (fun c => q c = q (s i))).image (Function.update s i) := by
  classical
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro ht
    obtain ⟨ho, hq⟩ := (coordinateKey_eq_iff c0 i q t s).mp ht
    refine ⟨t i, hq, ?_⟩
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp only [Function.update_of_ne hj, ho j hj]
  · rintro ⟨c, hc, rfl⟩
    rw [coordinateKey_update]
    exact Prod.ext rfl hc

theorem conditionMap_coordinate (c0 : C) (i : I) (q : C → T)
    (f : (I → C) → E) (s : I → C) :
    conditionMap (coordinateKey c0 i q) f s =
      ∑ c, fiberKernel q (s i) c • f (Function.update s i c) := by
  classical
  have hi : Function.Injective (Function.update s i) := by
    intro a b h
    simpa only [Function.update_self] using congrFun h i
  have hc : fiberSize (coordinateKey c0 i q) (coordinateKey c0 i q s) =
      fiberSize q (q (s i)) := by
    have hf := congrArg Finset.card (coordinateKey_fiber c0 i q s)
    rw [Finset.card_image_of_injective _ hi] at hf
    unfold fiberSize
    convert hf using 2
    congr 1
  simp only [conditionMap_apply, fiberKernel, ite_smul, zero_smul,
    ← Finset.sum_filter, hc]
  rw [coordinateKey_fiber, Finset.sum_image]
  exact fun _ _ _ _ h => hi h

theorem conditionMap_coordinate_commute {R : Type*} (c0 : C)
    (i j : I) (hij : i ≠ j) (q : C → T) (r : C → R)
    (f : (I → C) → E) :
    conditionMap (coordinateKey c0 i q) (conditionMap (coordinateKey c0 j r) f) =
      conditionMap (coordinateKey c0 j r) (conditionMap (coordinateKey c0 i q) f) := by
  classical
  funext s
  simp only [conditionMap_coordinate, Finset.smul_sum, smul_smul,
    Function.update_of_ne hij, Function.update_of_ne hij.symm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [Function.update_comm hij, mul_comm]

omit [AddCommGroup E] [Module ℝ E] [Fintype C] in

theorem invariant_of_coordinate_invariant (q : I → C → T) (f : (I → C) → E)
    (hf : ∀ i s c, q i c = q i (s i) → f (Function.update s i c) = f s)
    (s t : I → C) (hst : ∀ i, q i (s i) = q i (t i)) : f s = f t := by
  classical
  let mix (A : Finset I) : I → C := fun i => if i ∈ A then t i else s i
  have hm : ∀ A : Finset I, f (mix A) = f s := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp [mix]
    | @insert i A hi ih =>
      have hu : mix (insert i A) = Function.update (mix A) i (t i) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [mix]
        · simp [mix, hj]
      rw [hu, hf i (mix A) (t i) (by simpa [mix, hi] using (hst i).symm)]
      exact ih
  have hall := hm Finset.univ
  simpa [mix] using hall.symm

variable (B : EnergyForm E)

noncomputable def coordinateCondition (c0 : C) (i : I) (q : C → T) :
    (B.finite (S := I → C)).Projection := condition (coordinateKey c0 i q)

theorem coordinateCondition_commute (c0 : C) (q : I → C → T) (i j : I)
    (f : (I → C) → E) :
    coordinateCondition B c0 i (q i) (coordinateCondition B c0 j (q j) f) =
      coordinateCondition B c0 j (q j) (coordinateCondition B c0 i (q i) f) := by
  by_cases hij : i = j
  · subst j; rfl
  · exact conditionMap_coordinate_commute c0 i j hij (q i) (q j) f

theorem coordinate_product_invariant (c0 : C) (q : I → C → T)
    (f : (I → C) → E) (s t : I → C) (hst : ∀ i, q i (s i) = q i (t i)) :
    productMap (fun i => coordinateCondition B c0 i (q i)) Finset.univ.toList f s =
      productMap (fun i => coordinateCondition B c0 i (q i)) Finset.univ.toList f t := by
  classical
  let F := productMap (fun i => coordinateCondition B c0 i (q i)) Finset.univ.toList f
  apply invariant_of_coordinate_invariant q F _ s t hst
  intro i seed c hc
  have he := productMap_fixed_of_mem (fun i => coordinateCondition B c0 i (q i))
    (coordinateCondition_commute B c0 q) Finset.univ.toList i
    (by simp) f
  change coordinateCondition B c0 i (q i) F = F at he
  rw [← he]
  apply conditionMap_eq_of_key_eq
  simp [coordinateKey, hc]

end VertexCover.Restriction.EnergyForm.Projection


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
