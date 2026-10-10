import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalPBWIndependent
import OAI.Combinatorics.Chromatic.Histories.ColorWordReordering

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]

lemma homogeneousPrimitiveFamily_span :
    Submodule.span ℚ (Set.range (homogeneousPrimitiveFamily a c η hc θ))=globalPrimitives a c η hc θ := by
  have h := congrArg (Submodule.map (globalPrimitives a c η hc θ).subtype)
    (homogeneousPrimitiveBasis a c η hc θ).span_eq
  rw [Submodule.map_span,Submodule.map_top,Submodule.range_subtype] at h
  simp only [←Set.range_comp,Function.comp_def,Submodule.subtype_apply] at h
  exact h

lemma homogeneousPrimitiveFamily_adjoin :
    Algebra.adjoin ℚ (Set.range (homogeneousPrimitiveFamily a c η hc θ))=⊤ := by
  have hp : globalPrimitives a c η hc θ ≤
      (Algebra.adjoin ℚ (Set.range (homogeneousPrimitiveFamily a c η hc θ))).toSubmodule := by
    rw [←homogeneousPrimitiveFamily_span]
    apply Submodule.span_le.mpr
    exact fun _ hx=>Algebra.subset_adjoin hx
  apply top_unique
  rw [←globalPrimitiveLog_adjoin a c η hc θ]
  apply Algebra.adjoin_le
  rintro x ⟨y,rfl⟩
  exact hp ((mem_globalPrimitives a c η hc θ _).mpr (globalPrimitiveLog_primitive a c η hc θ y))

lemma primitive_mem_wordLength_one {x : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalPrimitives a c η hc θ) :
    x ∈ wordLengthFiltration (homogeneousPrimitiveFamily a c η hc θ) 1 := by
  apply wordLengthFiltration_span_range
  rwa [homogeneousPrimitiveFamily_span]

lemma homogeneousPrimitiveWords_span :
    Submodule.span ℚ (Set.range (fun l : PBWWord a c η hc θ (homogeneousPrimitiveWeight a c η hc θ)=>
      primitiveWord a c η hc θ (homogeneousPrimitiveFamily a c η hc θ) l.val))=⊤ := by
  let b := homogeneousPrimitiveFamily a c η hc θ
  let w := homogeneousPrimitiveWeight a c η hc θ
  let ε := fun i j=>globalColorSign a c η hc θ (w i) (w j)
  have he : ∀ i j,ε i j ≠ 0 := by
    intro i j h
    have hh := globalColorSign_sq a c η hc θ (w i) (w j)
    change ε i j*ε i j=1 at hh
    rw [h,zero_mul] at hh
    exact zero_ne_one hh
  have hcomm : ∀ i j,b i*b j-ε i j • (b j*b i) ∈ wordLengthFiltration b 1 := by
    intro i j
    exact primitive_mem_wordLength_one a c η hc θ
      (globalPrimitive_bracket a c η hc θ (homogeneousPrimitiveFamily_weight a c η hc θ i)
        (homogeneousPrimitiveFamily_weight a c η hc θ j)
        (homogeneousPrimitiveFamily_primitive a c η hc θ i)
        (homogeneousPrimitiveFamily_primitive a c η hc θ j))
  have hsquare : ∀ i,ε i i ≠ 1 → b i*b i ∈ wordLengthFiltration b 1 := by
    intro i hi
    have hs : ε i i= -1 := (mul_self_eq_one_iff.mp (globalColorSign_sq a c η hc θ (w i) (w i))).resolve_left hi
    exact primitive_mem_wordLength_one a c η hc θ
      (globalPrimitive_odd_square a c η hc θ (homogeneousPrimitiveFamily_weight a c η hc θ i)
        (homogeneousPrimitiveFamily_primitive a c η hc θ i) hs)
  have ht := colorWordSpan_top b ε he hcomm hsquare (homogeneousPrimitiveFamily_adjoin a c η hc θ)
  convert ht using 1
  unfold colorWordSpan
  congr 1
  ext x
  constructor
  · rintro ⟨l,rfl⟩
    exact ⟨l.val,l.property,rfl⟩
  · rintro ⟨l,hl,rfl⟩
    exact ⟨⟨l,hl⟩,rfl⟩

noncomputable def globalPBWBasis :
    Module.Basis (PBWWord a c η hc θ (homogeneousPrimitiveWeight a c η hc θ)) ℚ
      (UnitalShuffle a c η hc θ) :=
  Module.Basis.mk (homogeneousPrimitiveWords_independent a c η hc θ)
    (le_of_eq (homogeneousPrimitiveWords_span a c η hc θ).symm)

lemma globalPBWBasis_apply (l : PBWWord a c η hc θ (homogeneousPrimitiveWeight a c η hc θ)) :
    globalPBWBasis a c η hc θ l=
      primitiveWord a c η hc θ (homogeneousPrimitiveFamily a c η hc θ) l.val :=
  Module.Basis.mk_apply _ _ _

lemma globalPBWBasis_homogeneous (l : PBWWord a c η hc θ (homogeneousPrimitiveWeight a c η hc θ)) :
    globalPBWBasis a c η hc θ l ∈ globalHomogeneous a c η hc θ
      (wordWeight c η hc θ (homogeneousPrimitiveWeight a c η hc θ) l.val) := by
  rw [globalPBWBasis_apply]
  exact primitiveWord_homogeneous a c η hc θ _ _ (homogeneousPrimitiveFamily_weight a c η hc θ) l.val

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable Classical.decEq
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*} [LinearOrder J] (b : J → UnitalShuffle a c η hc θ)
  (w : J → SlopeWeight c η hc θ)
  (hw : ∀ i,b i∈globalHomogeneous a c η hc θ (w i))
  (hp : ∀ i,b i∈globalPrimitives a c η hc θ)
  (hspan : Submodule.span ℚ (Set.range b)=globalPrimitives a c η hc θ)
  (hli : LinearIndependent ℚ b)

noncomputable def primitiveBasisRetraction :
    UnitalShuffle a c η hc θ →ₗ[ℚ] Submodule.span ℚ (Set.range b) :=
  (globalPrimitiveLog a c η hc θ).codRestrict _ (fun x=>by
    rw [hspan]
    exact (mem_globalPrimitives a c η hc θ _).mpr (globalPrimitiveLog_primitive a c η hc θ x))

omit [LinearOrder J] in
lemma primitiveBasisRetraction_unit :
    primitiveBasisRetraction a c η hc θ b hspan (globalUnit a c η hc θ)=0 := by
  apply Subtype.ext
  change globalPrimitiveLog a c η hc θ (globalUnit a c η hc θ)=0
  exact congrArg (fun x : globalPrimitives a c η hc θ=>x.val) (globalPrimitiveProjection_unit a c η hc θ)

include hp in
omit [LinearOrder J] in
lemma primitiveBasisRetraction_apply (j : J) :
    primitiveBasisRetraction a c η hc θ b hspan (b j)=(Module.Basis.span hli) j := by
  apply Subtype.ext
  rw [Module.Basis.span_apply]
  exact globalPrimitiveLog_on_primitive a c η hc θ (hp j)

noncomputable def primitiveBasisDual (j : J) : UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ :=
  (Module.Basis.span hli).coord j ∘ₗ primitiveBasisRetraction a c η hc θ b hspan

omit [LinearOrder J] in
lemma primitiveBasisDual_unit (j : J) :
    primitiveBasisDual a c η hc θ b hspan hli j (globalUnit a c η hc θ)=0 := by
  change (Module.Basis.span hli).coord j (primitiveBasisRetraction a c η hc θ b hspan _)=0
  rw [primitiveBasisRetraction_unit,map_zero]

include hp in
omit [LinearOrder J] in
lemma primitiveBasisDual_apply (i j : J) :
    primitiveBasisDual a c η hc θ b hspan hli i (b j)=if i=j then 1 else 0 := by
  change (Module.Basis.span hli).coord i (primitiveBasisRetraction a c η hc θ b hspan _)=_
  rw [primitiveBasisRetraction_apply a c η hc θ b hp hspan hli,Module.Basis.coord_apply,
    Module.Basis.repr_self_apply]
  congr 1
  exact propext eq_comm

include hw hp hspan hli in
lemma primitiveBasisFamilyWords_independent :
    LinearIndependent ℚ (fun l : PBWWord a c η hc θ w=>primitiveWord a c η hc θ b l.val) :=
  globalPBW_independent a c η hc θ w b hw hp _
    (primitiveBasisDual_unit a c η hc θ b hspan hli)
    (primitiveBasisDual_apply a c η hc θ b hp hspan hli)

include hspan in
omit [LinearOrder J] in
lemma primitiveBasisFamily_adjoin :
    Algebra.adjoin ℚ (Set.range (b))=⊤ := by
  have hp : globalPrimitives a c η hc θ ≤
      (Algebra.adjoin ℚ (Set.range (b))).toSubmodule := by
    rw [←hspan]
    apply Submodule.span_le.mpr
    exact fun _ hx=>Algebra.subset_adjoin hx
  apply top_unique
  rw [←globalPrimitiveLog_adjoin a c η hc θ]
  apply Algebra.adjoin_le
  rintro x ⟨y,rfl⟩
  exact hp ((mem_globalPrimitives a c η hc θ _).mpr (globalPrimitiveLog_primitive a c η hc θ y))

include hspan in
omit [LinearOrder J] in
lemma primitiveBasisFamily_wordLength {x : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalPrimitives a c η hc θ) :
    x ∈ wordLengthFiltration (b) 1 := by
  apply wordLengthFiltration_span_range
  rwa [hspan]

include hw hp hspan in
lemma primitiveBasisFamilyWords_span :
    Submodule.span ℚ (Set.range (fun l : PBWWord a c η hc θ (w)=>
      primitiveWord a c η hc θ (b) l.val))=⊤ := by
  let ε := fun i j=>globalColorSign a c η hc θ (w i) (w j)
  have he : ∀ i j,ε i j ≠ 0 := by
    intro i j h
    have hh := globalColorSign_sq a c η hc θ (w i) (w j)
    change ε i j*ε i j=1 at hh
    rw [h,zero_mul] at hh
    exact zero_ne_one hh
  have hcomm : ∀ i j,b i*b j-ε i j • (b j*b i) ∈ wordLengthFiltration b 1 := by
    intro i j
    exact primitiveBasisFamily_wordLength a c η hc θ b hspan
      (globalPrimitive_bracket a c η hc θ (hw i)
        (hw j)
        (hp i)
        (hp j))
  have hsquare : ∀ i,ε i i ≠ 1 → b i*b i ∈ wordLengthFiltration b 1 := by
    intro i hi
    have hs : ε i i= -1 := (mul_self_eq_one_iff.mp (globalColorSign_sq a c η hc θ (w i) (w i))).resolve_left hi
    exact primitiveBasisFamily_wordLength a c η hc θ b hspan
      (globalPrimitive_odd_square a c η hc θ (hw i)
        (hp i) hs)
  have ht := colorWordSpan_top b ε he hcomm hsquare (primitiveBasisFamily_adjoin a c η hc θ b hspan)
  convert ht using 1
  unfold colorWordSpan
  congr 1
  ext x
  constructor
  · rintro ⟨l,rfl⟩
    exact ⟨l.val,l.property,rfl⟩
  · rintro ⟨l,hl,rfl⟩
    exact ⟨⟨l,hl⟩,rfl⟩

noncomputable def primitiveBasisPBW : Module.Basis (PBWWord a c η hc θ w) ℚ (UnitalShuffle a c η hc θ) :=
  Module.Basis.mk (primitiveBasisFamilyWords_independent a c η hc θ b w hw hp hspan hli)
    (le_of_eq (primitiveBasisFamilyWords_span a c η hc θ b w hw hp hspan).symm)

lemma primitiveBasisPBW_apply (l : PBWWord a c η hc θ w) :
    primitiveBasisPBW a c η hc θ b w hw hp hspan hli l=primitiveWord a c η hc θ b l.val :=
  Module.Basis.mk_apply _ _ _

end ElementaryPositivity.RawShuffle

end

end OAI
