import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalWordDetection
import OAI.Combinatorics.Chromatic.Walls.FilteredDualIndependence

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*} [LinearOrder J]

abbrev PBWWord (w : J → SlopeWeight c η hc θ) :=
  {l : List J // PBWAdmissible a c η hc θ w l}

theorem globalPBW_independent (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f : J → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (hf : ∀ i,f i (globalUnit a c η hc θ)=0)
    (hfb : ∀ i j,f i (b j)=if i=j then 1 else 0) :
    LinearIndependent ℚ (fun l : PBWWord a c η hc θ w=>primitiveWord a c η hc θ b l.val) := by
  apply linearIndependent_of_filtered_dual
    (degree:=fun l=>l.val.length)
    (f:=fun l=>(functionalWord a c η hc θ f l.val).ofConv)
    (diag:=fun l=>(wordMultiplicity l.val:ℚ))
  · intro l
    exact_mod_cast (Nat.ne_of_gt (wordMultiplicity_pos l.val))
  · intro u v h
    by_cases huv : u=v
    · subst v
      rw [ite_eq_left rfl]
      exact functionalWord_diagonal a c η hc θ w b hb hp f hf hfb u.val u.property
    · rw [ite_eq_right huv]
      by_cases hlen : v.val.length=u.val.length
      · exact functionalWord_top_sorted_ne a c η hc θ w b hb hp f hf hfb u.val v.val
          u.property.sorted v.property.sorted hlen (fun hh=>huv (Subtype.ext hh))
      · exact functionalWord_longer a c η hc θ w b hb hp f hf u.val v.val (lt_of_le_of_ne h hlen)

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

noncomputable def globalPrimitiveProjection : UnitalShuffle a c η hc θ →ₗ[ℚ] globalPrimitives a c η hc θ :=
  (globalPrimitiveLog a c η hc θ).codRestrict (globalPrimitives a c η hc θ)
    (fun x=>(mem_globalPrimitives a c η hc θ _).mpr (globalPrimitiveLog_primitive a c η hc θ x))

lemma globalPrimitiveProjection_restrict (x : globalPrimitives a c η hc θ) :
    globalPrimitiveProjection a c η hc θ x.val=x :=
  Subtype.ext (globalPrimitiveLog_on_primitive a c η hc θ x.property)

lemma globalPrimitiveProjection_unit :
    globalPrimitiveProjection a c η hc θ (globalUnit a c η hc θ)=0 := by
  apply Subtype.ext
  change (convSeries a c η hc θ (convolutionJ a c η hc θ) (PowerSeries.log ℚ)).ofConv
    (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (0,0) (unitalGradeOne a c η hc θ))=0
  rw [convSeries_lof]
  simp [dimensionSize]

noncomputable def homogeneousPrimitives : Set (globalPrimitives a c η hc θ) :=
  {x | ∃ k,x.val ∈ globalHomogeneous a c η hc θ k}

lemma homogeneousPrimitives_span :
    ⊤ ≤ Submodule.span ℚ (homogeneousPrimitives a c η hc θ) := by
  intro x hx
  rw [←globalPrimitiveProjection_restrict a c η hc θ x]
  have hmain : ∀ y:UnitalShuffle a c η hc θ,globalPrimitiveProjection a c η hc θ y∈
      Submodule.span ℚ (homogeneousPrimitives a c η hc θ) := by
    intro y
    induction y using DirectSum.induction_on with
    | zero => simpa only [map_zero] using (Submodule.span ℚ (homogeneousPrimitives a c η hc θ)).zero_mem
    | add y z hy hz => simpa only [map_add] using (Submodule.span ℚ (homogeneousPrimitives a c η hc θ)).add_mem hy hz
    | of k y =>
      apply Submodule.subset_span
      exact ⟨k,globalPrimitiveLog_homogeneous a c η hc θ k y⟩
  exact hmain x.val

noncomputable def PrimitiveIndex : Type _ :=
  (linearIndepOn_empty ℚ (id : globalPrimitives a c η hc θ → globalPrimitives a c η hc θ)).extend
    (Set.empty_subset (homogeneousPrimitives a c η hc θ))

noncomputable def homogeneousPrimitiveBasis :
    Module.Basis (PrimitiveIndex a c η hc θ) ℚ (globalPrimitives a c η hc θ) :=
  Module.Basis.ofSpan (homogeneousPrimitives_span a c η hc θ)

noncomputable def homogeneousPrimitiveFamily (i : PrimitiveIndex a c η hc θ) : UnitalShuffle a c η hc θ :=
  (homogeneousPrimitiveBasis a c η hc θ i).val

lemma homogeneousPrimitiveFamily_primitive (i : PrimitiveIndex a c η hc θ) :
    homogeneousPrimitiveFamily a c η hc θ i ∈ globalPrimitives a c η hc θ :=
  (homogeneousPrimitiveBasis a c η hc θ i).property

lemma homogeneousPrimitiveFamily_exists_weight (i : PrimitiveIndex a c η hc θ) :
    ∃ k,homogeneousPrimitiveFamily a c η hc θ i ∈ globalHomogeneous a c η hc θ k :=
  Module.Basis.ofSpan_subset (homogeneousPrimitives_span a c η hc θ) (Set.mem_range_self i)

noncomputable def homogeneousPrimitiveWeight (i : PrimitiveIndex a c η hc θ) : SlopeWeight c η hc θ :=
  (homogeneousPrimitiveFamily_exists_weight a c η hc θ i).choose

lemma homogeneousPrimitiveFamily_weight (i : PrimitiveIndex a c η hc θ) :
    homogeneousPrimitiveFamily a c η hc θ i ∈
      globalHomogeneous a c η hc θ (homogeneousPrimitiveWeight a c η hc θ i) :=
  (homogeneousPrimitiveFamily_exists_weight a c η hc θ i).choose_spec

noncomputable def homogeneousPrimitiveDual (i : PrimitiveIndex a c η hc θ) :
    UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ :=
  (homogeneousPrimitiveBasis a c η hc θ).coord i ∘ₗ globalPrimitiveProjection a c η hc θ

lemma homogeneousPrimitiveDual_unit (i : PrimitiveIndex a c η hc θ) :
    homogeneousPrimitiveDual a c η hc θ i (globalUnit a c η hc θ)=0 := by
  change (homogeneousPrimitiveBasis a c η hc θ).coord i (globalPrimitiveProjection a c η hc θ _)=0
  rw [globalPrimitiveProjection_unit,map_zero]

lemma homogeneousPrimitiveDual_apply (i j : PrimitiveIndex a c η hc θ) :
    homogeneousPrimitiveDual a c η hc θ i (homogeneousPrimitiveFamily a c η hc θ j)=if i=j then 1 else 0 := by
  change (homogeneousPrimitiveBasis a c η hc θ).coord i
    (globalPrimitiveProjection a c η hc θ (homogeneousPrimitiveBasis a c η hc θ j).val)=_
  rw [globalPrimitiveProjection_restrict,Module.Basis.coord_apply,Module.Basis.repr_self_apply]
  congr 1
  exact propext eq_comm

noncomputable instance primitiveIndexLinearOrder : LinearOrder (PrimitiveIndex a c η hc θ) :=
  linearOrderOfSTO WellOrderingRel

lemma homogeneousPrimitiveWords_independent :
    LinearIndependent ℚ (fun l : PBWWord a c η hc θ (homogeneousPrimitiveWeight a c η hc θ)=>
      primitiveWord a c η hc θ (homogeneousPrimitiveFamily a c η hc θ) l.val) :=
  globalPBW_independent a c η hc θ _ _ (homogeneousPrimitiveFamily_weight a c η hc θ)
    (homogeneousPrimitiveFamily_primitive a c η hc θ) _ (homogeneousPrimitiveDual_unit a c η hc θ)
    (homogeneousPrimitiveDual_apply a c η hc θ)

end ElementaryPositivity.RawShuffle

end

end OAI
