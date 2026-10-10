import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalPrimitiveBracket

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J K : Type*}

noncomputable def functionalWord (f : K → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ)
    (l : List K) : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) := (l.map (fun i=>toConv (f i))).prod

lemma functionalWord_cons (f : K → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (i : K) (l : List K) :
    functionalWord a c η hc θ f (i::l)=toConv (f i)*functionalWord a c η hc θ f l := rfl

lemma convolution_mul_unit (f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ)) :
    (f*g).ofConv (globalUnit a c η hc θ)=
      f.ofConv (globalUnit a c η hc θ)*g.ofConv (globalUnit a c η hc θ) := by
  rw [LinearMap.convMul_apply]
  change LinearMap.mul' ℚ ℚ (TensorProduct.map f.ofConv g.ofConv
    (globalCoproduct a c η hc θ (globalUnit a c η hc θ)))=_
  rw [globalCoproduct_unit,TensorProduct.map_tmul,LinearMap.mul'_apply]

lemma functionalWord_unit (f : K → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ)
    (hf : ∀ i,f i (globalUnit a c η hc θ)=0) (i : K) (l : List K) :
    (functionalWord a c η hc θ f (i::l)).ofConv (globalUnit a c η hc θ)=0 := by
  rw [functionalWord_cons,convolution_mul_unit,ofConv_toConv,hf,zero_mul]

lemma convolution_primitiveWord (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f g : WithConv (UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ)) (l : List J) :
    (f*g).ofConv (primitiveWord a c η hc θ b l)=
      ((signedWordCuts a c η hc θ w l).map fun s=>s.coeff*
        (f.ofConv (primitiveWord a c η hc θ b s.left)*
          g.ofConv (primitiveWord a c η hc θ b s.right))).sum := by
  rw [LinearMap.convMul_apply]
  change LinearMap.mul' ℚ ℚ (TensorProduct.map f.ofConv g.ofConv
    (globalCoproduct a c η hc θ (primitiveWord a c η hc θ b l)))=_
  rw [globalCoproduct_primitiveWord a c η hc θ w b hb hp l]
  simp only [map_list_sum,List.map_map,Function.comp_def,wordCutTensor,map_smul,
    TensorProduct.map_tmul,LinearMap.mul'_apply,smul_eq_mul]

theorem functionalWord_longer (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f : K → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (hf : ∀ i,f i (globalUnit a c η hc θ)=0)
    (u : List K) (v : List J) (h : v.length<u.length) :
    (functionalWord a c η hc θ f u).ofConv (primitiveWord a c η hc θ b v)=0 := by
  induction u generalizing v with
  | nil => simp at h
  | cons i u ih =>
    rw [functionalWord_cons,convolution_primitiveWord a c η hc θ w b hb hp]
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz
    by_cases he : s.left=[]
    · change s.coeff*(f i (primitiveWord a c η hc θ b s.left)*_)=0
      rw [he,primitiveWord_nil]
      change s.coeff*(f i (globalUnit a c η hc θ)*_)=0
      rw [hf,zero_mul,mul_zero]
    · have hl := signedWordCuts_lengths a c η hc θ w v s hs
      have hpos : 0<s.left.length := List.length_pos_iff.mpr he
      have hr : s.right.length<u.length := by simp only [List.length_cons] at h; omega
      rw [ih s.right hr,mul_zero,mul_zero]

theorem functionalWord_top_cuts (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f : K → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (hf : ∀ i,f i (globalUnit a c η hc θ)=0)
    (i : K) (u : List K) (v : List J) (h : v.length=u.length+1) :
    (functionalWord a c η hc θ f (i::u)).ofConv (primitiveWord a c η hc θ b v)=
      ((signedWordCuts a c η hc θ w v).map fun s=>if s.left.length=1 then s.coeff*
        (f i (primitiveWord a c η hc θ b s.left)*
          (functionalWord a c η hc θ f u).ofConv (primitiveWord a c η hc θ b s.right)) else 0).sum := by
  rw [functionalWord_cons,convolution_primitiveWord a c η hc θ w b hb hp]
  congr 1
  apply List.map_congr_left
  intro s hs
  by_cases h1 : s.left.length=1
  · simp only [h1,ite_eq_left]
  rw [ite_eq_right h1]
  by_cases he : s.left=[]
  · change s.coeff*(f i (primitiveWord a c η hc θ b s.left)*_)=0
    rw [he,primitiveWord_nil]
    change s.coeff*(f i (globalUnit a c η hc θ)*_)=0
    rw [hf,zero_mul,mul_zero]
  · have hl := signedWordCuts_lengths a c η hc θ w v s hs
    have hpos : 0<s.left.length := List.length_pos_iff.mpr he
    have hr : s.right.length<u.length := by omega
    rw [functionalWord_longer a c η hc θ w b hb hp f hf u s.right hr,mul_zero,mul_zero]

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
variable {J : Type*}

noncomputable def emptyCutSum (w : J → SlopeWeight c η hc θ) (l : List J) (g : List J → ℚ) : ℚ :=
  ((signedWordCuts a c η hc θ w l).map fun s => if s.left=[] then s.coeff*g s.right else 0).sum

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma emptyCutSum_eq (w : J → SlopeWeight c η hc θ) (l : List J) (g : List J → ℚ) :
    emptyCutSum a c η hc θ w l g=g l := by
  induction l generalizing g with
  | nil => simp [emptyCutSum,signedWordCuts]
  | cons i l ih =>
    unfold emptyCutSum
    simp only [signedWordCuts,List.map_append,List.sum_append,List.map_map,Function.comp_def]
    have hl : ((signedWordCuts a c η hc θ w l).map fun s =>
        if (s.prependLeft i).left=[] then (s.prependLeft i).coeff*g (s.prependLeft i).right else 0).sum=0 := by
      simp [SignedWordCut.prependLeft]
    rw [hl,zero_add]
    have hr : ((signedWordCuts a c η hc θ w l).map fun s =>
        if (SignedWordCut.prependRight a c η hc θ w i s).left=[] then
          (SignedWordCut.prependRight a c η hc θ w i s).coeff*g (SignedWordCut.prependRight a c η hc θ w i s).right else 0).sum=
        emptyCutSum a c η hc θ w l (fun r=>g (i::r)) := by
      unfold emptyCutSum
      congr 1
      apply List.map_congr_left
      intro s hs
      by_cases h : s.left=[]
      · simp [SignedWordCut.prependRight,h,wordWeight,globalColorSign_zero_right]
      · simp [SignedWordCut.prependRight,h]
    rw [hr,ih]

noncomputable def singletonCutSum (w : J → SlopeWeight c η hc θ) (i : J) (l : List J)
    (g : List J → ℚ) : ℚ :=
  ((signedWordCuts a c η hc θ w l).map fun s => if s.left=[i] then s.coeff*g s.right else 0).sum

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma singletonCutSum_nil (w : J → SlopeWeight c η hc θ) (i : J) (g : List J → ℚ) :
    singletonCutSum a c η hc θ w i [] g=0 := by simp [singletonCutSum,signedWordCuts]

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma singletonCutSum_cons (w : J → SlopeWeight c η hc θ) (i j : J) (l : List J) (g : List J → ℚ) :
    singletonCutSum a c η hc θ w i (j::l) g=
      (if j=i then g l else 0)+globalColorSign a c η hc θ (w j) (w i)*
        singletonCutSum a c η hc θ w i l (fun r=>g (j::r)) := by
  unfold singletonCutSum
  simp only [signedWordCuts,List.map_append,List.sum_append,List.map_map,Function.comp_def]
  congr 1
  · by_cases h : j=i
    · subst j
      rw [ite_eq_left rfl]
      convert emptyCutSum_eq a c η hc θ w l g using 1
      unfold emptyCutSum
      congr 1
      apply List.map_congr_left
      intro s hs
      simp [SignedWordCut.prependLeft]
    · rw [ite_eq_right h]
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz
      simp [SignedWordCut.prependLeft,h]
  · rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro s hs
    by_cases h : s.left=[i]
    · simp [SignedWordCut.prependRight,h,wordWeight,mul_left_comm,mul_comm,mul_assoc]
    · simp [SignedWordCut.prependRight,h]

lemma functionalWord_top_singleton (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f : J → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (hf : ∀ i,f i (globalUnit a c η hc θ)=0)
    (hfb : ∀ i j,f i (b j)=if i=j then 1 else 0)
    (i : J) (u v : List J) (h : v.length=u.length+1) :
    (functionalWord a c η hc θ f (i::u)).ofConv (primitiveWord a c η hc θ b v)=
      singletonCutSum a c η hc θ w i v
        (fun r=>(functionalWord a c η hc θ f u).ofConv (primitiveWord a c η hc θ b r)) := by
  rw [functionalWord_top_cuts a c η hc θ w b hb hp f hf i u v h]
  unfold singletonCutSum
  congr 1
  apply List.map_congr_left
  intro s hs
  by_cases h1 : s.left.length=1
  · obtain ⟨j,hj⟩ := List.length_eq_one_iff.mp h1
    rw [hj]
    simp only [List.length_singleton,ite_eq_left,primitiveWord_cons,primitiveWord_nil]
    rw [show b j*(1:UnitalShuffle a c η hc θ)=b j from mul_one _,hfb]
    by_cases hji : i=j
    · subst j; simp
    · simp [hji,Ne.symm hji]
  · rw [ite_eq_right h1]
    have hne : s.left ≠ [i] := fun hh=>h1 (by rw [hh]; rfl)
    rw [ite_eq_right hne]

end ElementaryPositivity.RawShuffle

end

end OAI
