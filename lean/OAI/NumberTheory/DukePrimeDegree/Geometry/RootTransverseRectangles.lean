import OAI.NumberTheory.DukePrimeDegree.Geometry.ShiftedRootPullback

namespace OAI

/-! # Product neighborhoods for the remaining-root transversals -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

structure RootTransverseRectangle {T B : Type*} [TopologicalSpace T] [TopologicalSpace B]
    (D : Set (T × B)) where
  first : Set T
  second : Set B
  first_open : IsOpen first
  second_open : IsOpen second
  inside : first ×ˢ second ⊆ D

namespace RootTransverseRectangle
variable {T B : Type*} [TopologicalSpace T] [TopologicalSpace B] {D : Set (T × B)}

def inclusion (C : RootTransverseRectangle D) (z : C.first × C.second) : D :=
  ⟨(z.1.val,z.2.val),C.inside ⟨z.1.prop,z.2.prop⟩⟩

lemma inclusion_isOpenEmbedding (C : RootTransverseRectangle D) (hD : IsOpen D) :
    Topology.IsOpenEmbedding C.inclusion := by
  have H := C.first_open.isOpenEmbedding_subtypeVal.prodMap
    C.second_open.isOpenEmbedding_subtypeVal
  exact Topology.IsOpenEmbedding.of_comp C.inclusion hD.isOpenEmbedding_subtypeVal H

end RootTransverseRectangle

theorem exists_shifted_root_rectangle
    {T B : Type*} [TopologicalSpace T] [TopologicalSpace B]
    {D : Set (T × B)} (hD : IsOpen D)
    {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (e : D → RootSlice a b k) (he : Topology.IsOpenEmbedding e)
    (τ : D → ℝ) (hτ : Continuous τ) (z : D) (t : ℝ) :
    ∃ (C : RootTransverseRectangle D) (A : RootBox hab k) (R : ℝ) (J : Set ℝ),
      IsOpen J ∧ z.val ∈ C.first ×ˢ C.second ∧ t ∈ J ∧
      A.transverse = Set.range (e ∘ C.inclusion) ∧
      A.time ⊆ rootLeafWindow R 0 ∧
      ∀ w : C.first × C.second, (Homeomorph.addRight (τ (C.inclusion w))) '' J ⊆ A.time := by
  obtain ⟨A,hA⟩ := exists_rootBox_at_coordinates hab (e z,t + τ z)
  let R := |t + τ z| + 1
  let V := A.time ∩ Ioo (-R) R
  have hV : IsOpen V := A.time_open.inter isOpen_Ioo
  have hzV : t + τ z ∈ V := by
    refine ⟨hA.2,?_⟩
    exact abs_lt.mp (lt_add_one _)
  let F : D × ℝ → RootSlice a b k × ℝ := fun x => (e x.1,x.2 + τ x.1)
  have hF : Continuous F := (he.continuous.comp continuous_fst).prodMk
    (continuous_snd.add (hτ.comp continuous_fst))
  have hO := (A.transverse_open.prod hV).preimage hF
  have hzO : (z,t) ∈ F ⁻¹' (A.transverse ×ˢ V) := ⟨hA.1,hzV⟩
  obtain ⟨Z,J,hZ,hzZ,hJ,htJ,hZJ⟩ := mem_nhds_prod_iff'.mp (hO.mem_nhds hzO)
  have hZi : IsOpen (Subtype.val '' Z : Set (T × B)) :=
    hD.isOpenEmbedding_subtypeVal.isOpenMap Z hZ
  obtain ⟨U,W,hU,hzU,hW,hzW,hUW⟩ :=
    mem_nhds_prod_iff'.mp (hZi.mem_nhds ⟨z,hzZ,rfl⟩)
  let C : RootTransverseRectangle D := ⟨U,W,hU,hW,by
    intro x hx
    obtain ⟨v,_,hv⟩ := hUW hx
    exact hv ▸ v.prop⟩
  have hCZ : ∀ w : C.first × C.second, C.inclusion w ∈ Z := by
    intro w
    obtain ⟨v,hv,hval⟩ := hUW
      (show (w.1.val,w.2.val) ∈ U ×ˢ W from ⟨w.1.prop,w.2.prop⟩)
    have heq : v = C.inclusion w := Subtype.ext hval
    exact heq ▸ hv
  have hslice := he.comp (C.inclusion_isOpenEmbedding hD)
  have hsub : Set.range (e ∘ C.inclusion) ⊆ A.transverse := by
    rintro _ ⟨w,rfl⟩
    exact (hZJ (show (C.inclusion w,t) ∈ Z ×ˢ J from ⟨hCZ w,htJ⟩)).1
  let A' := A.shrink (Set.range (e ∘ C.inclusion)) V hslice.isOpen_range hV hsub inter_subset_left
  refine ⟨C,A',R,J,hJ,⟨hzU,hzW⟩,htJ,rfl,?_,?_⟩
  · intro u hu
    simpa only [rootLeafWindow,Nat.cast_zero,add_zero] using hu.2
  · intro w u hu
    obtain ⟨r,hr,rfl⟩ := hu
    exact (hZJ (show (C.inclusion w,r) ∈ Z ×ˢ J from ⟨hCZ w,hr⟩)).2

end DukePrimeDegree

end

end OAI
