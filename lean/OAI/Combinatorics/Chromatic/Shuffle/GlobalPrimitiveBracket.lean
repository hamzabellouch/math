import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalPrimitiveGeneration
import OAI.Combinatorics.Chromatic.Shuffle.GlobalSeriesEvaluation

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [hχ : Fact (SlopeEulerSymmetric a c η θ)]

def globalColorSign (k l : SlopeWeight c η hc θ) : ℚ := (-1:ℚ)^eulerForm a k.1.val l.1.val

omit [DecidableEq I] in
lemma globalColorSign_symm (k l : SlopeWeight c η hc θ) :
    globalColorSign a c η hc θ k l=globalColorSign a c η hc θ l k := by
  unfold globalColorSign
  congr 1
  by_cases hk : k.1.val=0
  · rw [hk]; simp [eulerForm]
  by_cases hl : l.1.val=0
  · rw [hl]; simp [eulerForm]
  exact hχ.out _ _ hk hl (k.1.property.resolve_left hk) (l.1.property.resolve_left hl)

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma globalColorSign_sq (k l : SlopeWeight c η hc θ) :
    globalColorSign a c η hc θ k l*globalColorSign a c η hc θ k l=1 := by
  simp only [globalColorSign,neg_one_zpow_eq_ite]
  split <;> norm_num

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma globalColorSign_zero_left (k : SlopeWeight c η hc θ) :
    globalColorSign a c η hc θ 0 k=1 := by simp [globalColorSign,eulerForm]
omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma globalColorSign_zero_right (k : SlopeWeight c η hc θ) :
    globalColorSign a c η hc θ k 0=1 := by simp [globalColorSign,eulerForm]

omit hχ in
lemma globalHomogeneous_one : (1 : UnitalShuffle a c η hc θ) ∈ globalHomogeneous a c η hc θ 0 :=
  ⟨unitalGradeOne a c η hc θ,rfl⟩

lemma signedTensor_mul_homogeneous {k l m n : SlopeWeight c η hc θ}
    {x y z w : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalHomogeneous a c η hc θ k) (hy : y ∈ globalHomogeneous a c η hc θ l)
    (hz : z ∈ globalHomogeneous a c η hc θ m) (hw : w ∈ globalHomogeneous a c η hc θ n) :
    globalSignedTensorMultiply a c η hc θ (x⊗ₜ[ℚ]y) (z⊗ₜ[ℚ]w)=
      globalColorSign a c η hc θ l m • ((x*z)⊗ₜ[ℚ](y*w)) := by
  obtain ⟨x,rfl⟩ := hx
  obtain ⟨y,rfl⟩ := hy
  obtain ⟨z,rfl⟩ := hz
  obtain ⟨w,rfl⟩ := hw
  exact globalSignedTensorMultiply_tmul_lof a c η hc θ k l m n x y z w

lemma globalPrimitive_product_coproduct {k l : SlopeWeight c η hc θ}
    {x y : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalHomogeneous a c η hc θ k) (hy : y ∈ globalHomogeneous a c η hc θ l)
    (hpx : x ∈ globalPrimitives a c η hc θ) (hpy : y ∈ globalPrimitives a c η hc θ) :
    globalCoproduct a c η hc θ (x*y)=
      (x*y)⊗ₜ[ℚ](1:UnitalShuffle a c η hc θ)+x⊗ₜ[ℚ]y+
        globalColorSign a c η hc θ k l • (y⊗ₜ[ℚ]x)+
        (1:UnitalShuffle a c η hc θ)⊗ₜ[ℚ](x*y) := by
  rw [globalCoproduct_mul,(mem_globalPrimitives a c η hc θ x).mp hpx,
    (mem_globalPrimitives a c η hc θ y).mp hpy]
  change globalSignedTensorMultiply a c η hc θ (x⊗ₜ[ℚ]1+1⊗ₜ[ℚ]x) (y⊗ₜ[ℚ]1+1⊗ₜ[ℚ]y)=_
  simp only [map_add,LinearMap.add_apply]
  rw [signedTensor_mul_homogeneous a c η hc θ hx (globalHomogeneous_one a c η hc θ) hy (globalHomogeneous_one a c η hc θ),
    signedTensor_mul_homogeneous a c η hc θ hx (globalHomogeneous_one a c η hc θ) (globalHomogeneous_one a c η hc θ) hy,
    signedTensor_mul_homogeneous a c η hc θ (globalHomogeneous_one a c η hc θ) hx hy (globalHomogeneous_one a c η hc θ),
    signedTensor_mul_homogeneous a c η hc θ (globalHomogeneous_one a c η hc θ) hx (globalHomogeneous_one a c η hc θ) hy]
  simp only [globalColorSign_zero_left,globalColorSign_zero_right,one_smul]
  change ((x*y)⊗ₜ[ℚ]((1:UnitalShuffle a c η hc θ)*1)+
    globalColorSign a c η hc θ k l • ((1*y)⊗ₜ[ℚ](x*1)))+
    ((x*1)⊗ₜ[ℚ](1*y)+(1*1)⊗ₜ[ℚ](x*y))=_
  rw [show x*1=x from mul_one x,show (1:UnitalShuffle a c η hc θ)*1=1 from one_mul 1,
    show 1*y=y from one_mul y]
  abel

theorem globalPrimitive_bracket {k l : SlopeWeight c η hc θ}
    {x y : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalHomogeneous a c η hc θ k) (hy : y ∈ globalHomogeneous a c η hc θ l)
    (hpx : x ∈ globalPrimitives a c η hc θ) (hpy : y ∈ globalPrimitives a c η hc θ) :
    x*y-globalColorSign a c η hc θ k l • (y*x) ∈ globalPrimitives a c η hc θ := by
  rw [mem_globalPrimitives,map_sub,map_smul,
    globalPrimitive_product_coproduct a c η hc θ hx hy hpx hpy,
    globalPrimitive_product_coproduct a c η hc θ hy hx hpy hpx,
    globalColorSign_symm a c η hc θ l k]
  change _=(x*y-_ • (y*x))⊗ₜ[ℚ]1+1⊗ₜ[ℚ](x*y-_ • (y*x))
  simp only [smul_add,smul_smul,globalColorSign_sq,one_smul,
    TensorProduct.sub_tmul,TensorProduct.tmul_sub,TensorProduct.smul_tmul,TensorProduct.tmul_smul]
  abel

theorem globalPrimitive_odd_square {k : SlopeWeight c η hc θ}
    {x : UnitalShuffle a c η hc θ}
    (hx : x ∈ globalHomogeneous a c η hc θ k) (hpx : x ∈ globalPrimitives a c η hc θ)
    (hodd : globalColorSign a c η hc θ k k = -1) : x*x ∈ globalPrimitives a c η hc θ := by
  rw [mem_globalPrimitives,globalPrimitive_product_coproduct a c η hc θ hx hx hpx hpx,hodd]
  change (x*x)⊗ₜ[ℚ]1+x⊗ₜ[ℚ]x+(-1:ℚ) • (x⊗ₜ[ℚ]x)+1⊗ₜ[ℚ](x*x)=
    (x*x)⊗ₜ[ℚ]1+1⊗ₜ[ℚ](x*x)
  have hs : (-1:ℚ) • (x⊗ₜ[ℚ]x)= -(x⊗ₜ[ℚ]x) := neg_one_smul ℚ (x⊗ₜ[ℚ]x)
  rw [hs]
  abel

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*}

structure SignedWordCut (J : Type*) where
  left : List J
  right : List J
  coeff : ℚ

def wordWeight (w : J → SlopeWeight c η hc θ) (l : List J) := (l.map w).sum
noncomputable def primitiveWord (b : J → UnitalShuffle a c η hc θ) (l : List J) := (l.map b).prod

def SignedWordCut.prependLeft (i : J) (s : SignedWordCut J) : SignedWordCut J :=
  ⟨i::s.left,s.right,s.coeff⟩
def SignedWordCut.prependRight (w : J → SlopeWeight c η hc θ) (i : J)
    (s : SignedWordCut J) : SignedWordCut J :=
  ⟨s.left,i::s.right,s.coeff*globalColorSign a c η hc θ (w i) (wordWeight c η hc θ w s.left)⟩

def signedWordCuts (w : J → SlopeWeight c η hc θ) : List J → List (SignedWordCut J)
  | [] => [⟨[],[],1⟩]
  | i::l => (signedWordCuts w l).map (SignedWordCut.prependLeft i) ++
      (signedWordCuts w l).map (SignedWordCut.prependRight a c η hc θ w i)

lemma primitiveWord_nil (b : J → UnitalShuffle a c η hc θ) : primitiveWord a c η hc θ b []=1 := rfl
lemma primitiveWord_cons (b : J → UnitalShuffle a c η hc θ) (i : J) (l : List J) :
    primitiveWord a c η hc θ b (i::l)=b i*primitiveWord a c η hc θ b l := rfl

lemma primitiveWord_homogeneous (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (l : List J) : primitiveWord a c η hc θ b l ∈
      globalHomogeneous a c η hc θ (wordWeight c η hc θ w l) := by
  induction l with
  | nil => exact globalHomogeneous_one a c η hc θ
  | cons i l ih => exact globalHomogeneous_mul a c η hc θ (hb i) ih

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma signedWordCuts_lengths (w : J → SlopeWeight c η hc θ) (l : List J)
    (s : SignedWordCut J) (hs : s ∈ signedWordCuts a c η hc θ w l) :
    s.left.length+s.right.length=l.length := by
  induction l generalizing s with
  | nil => simp only [signedWordCuts,List.mem_singleton] at hs; subst s; rfl
  | cons i l ih =>
    simp only [signedWordCuts,List.mem_append,List.mem_map] at hs
    rcases hs with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · have h := ih s hs
      change (s.left.length+1)+s.right.length=l.length+1
      omega
    · have h := ih s hs
      change s.left.length+(s.right.length+1)=l.length+1
      omega

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma signedWordCuts_sublist (w : J → SlopeWeight c η hc θ) (l : List J)
    (s : SignedWordCut J) (hs : s ∈ signedWordCuts a c η hc θ w l) :
    s.left.Sublist l ∧ s.right.Sublist l := by
  induction l generalizing s with
  | nil => simp only [signedWordCuts,List.mem_singleton] at hs; subst s; exact ⟨.refl _,.refl _⟩
  | cons i l ih =>
    simp only [signedWordCuts,List.mem_append,List.mem_map] at hs
    rcases hs with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · exact ⟨(ih s hs).1.cons_cons i,(ih s hs).2.cons i⟩
    · exact ⟨(ih s hs).1.cons i,(ih s hs).2.cons_cons i⟩

noncomputable def wordCutTensor (b : J → UnitalShuffle a c η hc θ)
    (s : SignedWordCut J) : UnitalShuffle a c η hc θ⊗[ℚ]UnitalShuffle a c η hc θ :=
  s.coeff • (primitiveWord a c η hc θ b s.left⊗ₜ[ℚ]primitiveWord a c η hc θ b s.right)

lemma wordCutTensor_left (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (i : J) (s : SignedWordCut J) :
    globalSignedTensorMultiply a c η hc θ (b i⊗ₜ[ℚ]1) (wordCutTensor a c η hc θ b s)=
      wordCutTensor a c η hc θ b (s.prependLeft i) := by
  unfold wordCutTensor
  rw [map_smul,signedTensor_mul_homogeneous a c η hc θ (hb i) (globalHomogeneous_one a c η hc θ)
    (primitiveWord_homogeneous a c η hc θ w b hb s.left)
    (primitiveWord_homogeneous a c η hc θ w b hb s.right),globalColorSign_zero_left,one_smul]
  rw [show (1:UnitalShuffle a c η hc θ)*primitiveWord a c η hc θ b s.right=_ from one_mul _]
  rfl

lemma wordCutTensor_right (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (i : J) (s : SignedWordCut J) :
    globalSignedTensorMultiply a c η hc θ (1⊗ₜ[ℚ]b i) (wordCutTensor a c η hc θ b s)=
      wordCutTensor a c η hc θ b (s.prependRight a c η hc θ w i) := by
  unfold wordCutTensor
  rw [map_smul,signedTensor_mul_homogeneous a c η hc θ (globalHomogeneous_one a c η hc θ) (hb i)
    (primitiveWord_homogeneous a c η hc θ w b hb s.left)
    (primitiveWord_homogeneous a c η hc θ w b hb s.right)]
  rw [show (1:UnitalShuffle a c η hc θ)*primitiveWord a c η hc θ b s.left=_ from one_mul _,smul_smul]
  rfl

theorem globalCoproduct_primitiveWord (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ) (l : List J) :
    globalCoproduct a c η hc θ (primitiveWord a c η hc θ b l)=
      ((signedWordCuts a c η hc θ w l).map (wordCutTensor a c η hc θ b)).sum := by
  induction l with
  | nil =>
    change globalCoproduct a c η hc θ (globalUnit a c η hc θ)=_
    rw [globalCoproduct_unit]
    simp only [signedWordCuts,List.map_singleton,List.sum_singleton,wordCutTensor,
      primitiveWord_nil,one_smul]
    rfl
  | cons i l ih =>
    rw [primitiveWord_cons,globalCoproduct_mul,(mem_globalPrimitives a c η hc θ (b i)).mp (hp i),ih]
    change globalSignedTensorMultiply a c η hc θ (b i⊗ₜ[ℚ]1+1⊗ₜ[ℚ]b i) _=_
    rw [map_add,LinearMap.add_apply]
    simp only [map_list_sum,List.map_map,Function.comp_def,signedWordCuts,List.map_append,List.sum_append]
    congr 1
    · congr 1
      apply List.map_congr_left
      intro s hs
      exact wordCutTensor_left a c η hc θ w b hb i s
    · congr 1
      apply List.map_congr_left
      intro s hs
      exact wordCutTensor_right a c η hc θ w b hb i s

end ElementaryPositivity.RawShuffle

end

end OAI
