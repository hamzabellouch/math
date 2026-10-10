import OAI.Analysis.SegmentLenses.Subtrees

namespace OAI

/-!
# Finite-head ranges, dimensions, and outside-head density
-/

noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace SegmentLenses

attribute [local instance] instDecidableEqForestVertex

section HeadRange
variable {V : Type*} [DecidableEq V] [SegmentSystem V]


theorem primalHead_range (H : Finset V) :
    (primalHead H).range = Submodule.span ℝ (unitVector '' (H : Set V)) := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    change primalHead H x ∈ _
    rw [primalHead_apply]
    apply Submodule.sum_mem
    intro v hv
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v,hv,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨v,hv,rfl⟩
    change v ∈ H at hv
    refine ⟨unitVector v,?_⟩
    change primalHead H (unitVector v) = unitVector v
    rw [primalHead_apply]
    simp [coordinate_unitVector,hv]



theorem dualHead_range (H : Finset V) :
    (headLinear H).range = Submodule.span ℝ (coordinate '' (H : Set V)) := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    change head H x ∈ _
    unfold head
    apply Submodule.sum_mem
    intro v hv
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v,hv,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨v,hv,rfl⟩
    refine ⟨coordinate v,?_⟩
    change head H (coordinate v) = coordinate v
    apply (head_eq_iff _ _).mpr
    intro w hw
    have hn : v ≠ w := fun he => hw (he ▸ hv)
    simp [coordinate_unitVector,hn]

theorem primalHead_finiteDimensional (H : Finset V) :
    FiniteDimensional ℝ (primalHead H).range := by
  rw [primalHead_range]
  exact FiniteDimensional.span_of_finite ℝ (H.finite_toSet.image _)

theorem dualHead_finiteDimensional (H : Finset V) :
    FiniteDimensional ℝ (headLinear H).range := by
  rw [dualHead_range]
  exact FiniteDimensional.span_of_finite ℝ (H.finite_toSet.image _)

end HeadRange

section OutsideHeadDensity
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]

local instance : AddCommGroup (CoordinatePredual V) :=
  (inferInstance : NormedAddCommGroup (CoordinatePredual V)).toAddCommGroup
local instance : Module ℝ (CoordinatePredual V) :=
  (inferInstance : NormedSpace ℝ (CoordinatePredual V)).toModule



theorem predualHead_finiteDimensional {H : Finset V} (hH : Ancestral (· ≤ ·) H) :
    FiniteDimensional ℝ (predualHead hH).range := by
  have _ := locallyFiniteOrderBotV
  let := dualHead_finiteDimensional (V := V) H
  let f : (predualHead hH).range →ₗ[ℝ] (headLinear H).range :=
    { toFun := fun x => ⟨x.val.val,by
        obtain ⟨y,hy⟩ := x.property
        exact ⟨y.val,congrArg Subtype.val hy⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply FiniteDimensional.of_injective (V₂ := (headLinear H).range) f
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : (headLinear H).range => z.val) he




theorem predual_kernel_finite_approx {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x : CoordinatePredual V) (hx : predualHead hH x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Finset V, Disjoint K H ∧ ∃ z : CoordinatePredual V,
      head K z.val = z.val ∧ predualHead hH z = 0 ∧ ‖x-z‖ < ε := by
  classical
  obtain ⟨L,hL,z,hz,he⟩ := predual_finite_approx x hε
  let w := tail H z
  have hw : head (L \ H) w = w := by
    apply (head_eq_iff _ _).mpr
    intro v hv
    rw [tail_unitVector]
    by_cases hvH : v ∈ H
    · simp [hvH]
    · have hvL : v ∉ L := fun h => hv (Finset.mem_sdiff.mpr ⟨h,hvH⟩)
      simp [hvH,(head_eq_iff L z).mp hz v hvL]
  have hwm : w ∈ coordinateSpan V := by rw [← hw]; exact head_mem _ _
  refine ⟨L \ H,Finset.sdiff_disjoint,⟨w,hwm⟩,hw,?_,?_⟩
  · apply Subtype.ext
    apply dual_ext_coordinates
    intro v
    by_cases hv : v ∈ H <;> simp [w,head_unitVector,tail_unitVector,hv]
  · have hx0 : head H x.val = 0 := congrArg Subtype.val hx
    have heq : x.val-w = tail H (x.val-z) := by
      change x.val-tailLinear H z = tailLinear H (x.val-z)
      rw [map_sub]
      change x.val-tail H z = (x.val-head H x.val)-tail H z
      rw [hx0,sub_zero]
    change ‖x.val-w‖ < ε
    rw [heq]
    exact (norm_tail_le hH _).trans_lt he

end OutsideHeadDensity


section CompletedHeadTests
variable {V : Type*} [DecidableEq V] [SegmentSystem V]




theorem exists_test_of_primalHead_eq (H : Finset V) (p : Primal V)
    (hp : primalHead H p = p) :
    ∃ q : Test V, q.coeff.support ⊆ H ∧ (q : Primal V) = p ∧ ‖q‖ = ‖p‖ := by
  classical
  let q : Test V := ∑ v ∈ H, coordinate v p • Test.ofFinsupp (Finsupp.single v 1)
  have hq : (q : Primal V) = p := by
    rw [← hp, primalHead_apply]
    change (UniformSpace.Completion.toComplL : Test V →L[ℝ] Primal V)
      (∑ v ∈ H, coordinate v p • Test.ofFinsupp (Finsupp.single v 1)) = _
    simp only [map_sum,map_smul]
    rfl
  refine ⟨q,?_,hq,?_⟩
  · intro v hv
    by_contra hn
    have hz : q.coeff v = 0 := by
      change Test.evaluation v q = 0
      simp only [q,map_sum,map_smul]
      apply Finset.sum_eq_zero
      intro w hw
      change coordinate w p * Finsupp.single w (1 : ℝ) v = 0
      simp [show w ≠ v by rintro rfl; exact hn hw]
    exact (Finsupp.mem_support_iff.mp hv) hz
  · rw [← hq, UniformSpace.Completion.norm_coe]

end CompletedHeadTests


end SegmentLenses

end

end OAI
