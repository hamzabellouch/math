import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalCoproductCocommutative
import OAI.Combinatorics.Chromatic.Shuffle.UnitalGradeCoproductUnits

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearFiltration DimensionSplit
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable

noncomputable def slopeSplitZeroLeft (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
    (d : slopeDimensions c η hc θ) : SlopeSplit c η hc θ d.val :=
  ⟨ofPair 0 d.val (zero_add _),by
    constructor
    · exact Or.inl rfl
    · rw [right_ofPair]
      exact d.property⟩
noncomputable def slopeSplitZeroRight (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
    (d : slopeDimensions c η hc θ) : SlopeSplit c η hc θ d.val :=
  ⟨ofPair d.val 0 (add_zero _),by
    constructor
    · exact d.property
    · rw [right_ofPair]
      exact Or.inl rfl⟩

omit [DecidableEq I] in
lemma slopeSplit_ne_left_zero (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
    (d : slopeDimensions c η hc θ) (s : SlopeSplit c η hc θ d.val)
    (h : s≠slopeSplitZeroLeft c η hc θ d) : left s.val≠0 := by
  intro hz
  apply h
  exact Subtype.ext (DimensionSplit.ext hz)
omit [DecidableEq I] in
lemma slopeSplit_ne_right_zero (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
    (d : slopeDimensions c η hc θ) (s : SlopeSplit c η hc θ d.val)
    (h : s≠slopeSplitZeroRight c η hc θ d) : right s.val≠0 := by
  intro hz
  apply h
  apply Subtype.ext
  apply DimensionSplit.ext
  change left s.val=d.val
  simpa only [hz,add_zero] using left_add_right s.val

lemma globalLof_gradeOne_cast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (V : ℤ) (h : 0=V) :
    DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (0,V)
      (unitalGradeCast a c η hc θ rfl h (unitalGradeOne a c η hc θ))=
      globalUnit a c η hc θ := by
  subst V
  rfl

lemma globalSplitCoproduct_zero_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) :
    globalSplitCoproduct a c η hc θ k (slopeSplitZeroLeft c η hc θ k.1) x=
      globalUnit a c η hc θ⊗ₜ[ℚ]DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x := by
  rw [globalSplitCoproduct_dimensions a c η hc θ k
    (slopeSplitZeroLeft c η hc θ k.1) 0 k.1.val rfl (right_ofPair 0 k.1.val (zero_add _))
    (show OnSlopeOrZero c η θ 0 from (0 : slopeDimensions c η hc θ).property) k.1.property (zero_add _) x]
  rw [unitalGradeCoproduct_zero_left,globalTensorGradeInclusion_part]
  erw [unitalLof_cast]
  rfl

lemma globalSplitCoproduct_zero_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) :
    globalSplitCoproduct a c η hc θ k (slopeSplitZeroRight c η hc θ k.1) x=
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]globalUnit a c η hc θ := by
  rw [globalSplitCoproduct_dimensions a c η hc θ k
    (slopeSplitZeroRight c η hc θ k.1) k.1.val 0 rfl (right_ofPair k.1.val 0 (add_zero _))
    k.1.property (show OnSlopeOrZero c η θ 0 from (0 : slopeDimensions c η hc θ).property) (add_zero _) x]
  rw [unitalGradeCoproduct_zero_right,globalTensorGradeInclusion_part]
  exact congrArg (fun z=>DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ]z)
    (globalLof_gradeOne_cast a c η hc θ (k.2-k.2) (sub_self _).symm)

lemma globalCoproduct_counit_left_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.map (globalCounit a c η hc θ) LinearMap.id
      (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))=
      (1:ℚ)⊗ₜ[ℚ]DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x := by
  rw [globalCoproduct_lof,map_sum,Finset.sum_eq_single (slopeSplitZeroLeft c η hc θ k.1)]
  · rw [globalSplitCoproduct_zero_left,TensorProduct.map_tmul,globalCounit_unit,LinearMap.id_apply]
  · intro s _ hs
    exact globalCounit_tensor_nonzero_left a c η hc θ ⟨left s.val,s.property.1⟩
      ⟨right s.val,s.property.2⟩ (slopeSplit_ne_left_zero c η hc θ k.1 s hs) k.2 _
  · intro hs
    exact False.elim (hs (Finset.mem_univ _))

lemma globalCoproduct_counit_right_lof (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (k : SlopeWeight c η hc θ)
    (x : unitalComponent a c η hc θ k) :
    TensorProduct.map LinearMap.id (globalCounit a c η hc θ)
      (globalCoproduct a c η hc θ (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x))=
      DirectSum.lof ℚ _ (unitalComponent a c η hc θ) k x⊗ₜ[ℚ](1:ℚ) := by
  rw [globalCoproduct_lof,map_sum,Finset.sum_eq_single (slopeSplitZeroRight c η hc θ k.1)]
  · rw [globalSplitCoproduct_zero_right,TensorProduct.map_tmul,globalCounit_unit,LinearMap.id_apply]
  · intro s _ hs
    exact globalCounit_tensor_nonzero_right a c η hc θ ⟨left s.val,s.property.1⟩
      ⟨right s.val,s.property.2⟩ (slopeSplit_ne_right_zero c η hc θ k.1 s hs) k.2 _
  · intro hs
    exact False.elim (hs (Finset.mem_univ _))

lemma globalCoproduct_counit_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (x : UnitalShuffle a c η hc θ) :
    TensorProduct.map (globalCounit a c η hc θ) LinearMap.id (globalCoproduct a c η hc θ x)=
      (1:ℚ)⊗ₜ[ℚ]x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero,TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add,hx,hy,TensorProduct.tmul_add]
  | of k x => exact globalCoproduct_counit_left_lof a c η hc θ k x

lemma globalCoproduct_counit_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (x : UnitalShuffle a c η hc θ) :
    TensorProduct.map LinearMap.id (globalCounit a c η hc θ) (globalCoproduct a c η hc θ x)=
      x⊗ₜ[ℚ](1:ℚ) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero,TensorProduct.zero_tmul]
  | add x y hx hy => simp only [map_add,hx,hy,TensorProduct.add_tmul]
  | of k x => exact globalCoproduct_counit_right_lof a c η hc θ k x

lemma globalCoproduct_unit (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) :
    globalCoproduct a c η hc θ (globalUnit a c η hc θ)=
      globalUnit a c η hc θ⊗ₜ[ℚ]globalUnit a c η hc θ := by
  change globalCoproduct a c η hc θ
    (DirectSum.lof ℚ _ (unitalComponent a c η hc θ) (0,0) (unitalGradeOne a c η hc θ))=_
  rw [globalCoproduct_lof]
  have hh := Finset.sum_eq_single (s:=Finset.univ) (slopeSplitZeroLeft c η hc θ 0)
    (f:=fun s : SlopeSplit c η hc θ (0 : slopeDimensions c η hc θ).val=>
      globalSplitCoproduct a c η hc θ (0,0) s (unitalGradeOne a c η hc θ))
  rw [hh]
  · exact globalSplitCoproduct_zero_left a c η hc θ 0 _
  · intro s _ hs
    have hz : left s.val=0 := by
      funext i
      have hi := congrFun (left_add_right s.val) i
      change left s.val i+right s.val i=0 at hi
      exact (Nat.add_eq_zero_iff.mp hi).1
    exact False.elim ((slopeSplit_ne_left_zero c η hc θ 0 s hs) hz)
  · intro hs
    exact False.elim (hs (Finset.mem_univ _))
end ElementaryPositivity.RawShuffle

end

end OAI
