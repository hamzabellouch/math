import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.GlobalWordPairing

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open WithConv
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] Classical.propDecidable
variable (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i) (θ : ℝ)
  [Fact (SlopeEulerSymmetric a c η θ)]
variable {J : Type*}

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma signedWordCuts_perm (w : J → SlopeWeight c η hc θ) (l : List J)
    (s : SignedWordCut J) (hs : s ∈ signedWordCuts a c η hc θ w l) :
    (s.left++s.right).Perm l := by
  induction l generalizing s with
  | nil => simp only [signedWordCuts,List.mem_singleton] at hs; subst s; exact .refl _
  | cons i l ih =>
    simp only [signedWordCuts,List.mem_append,List.mem_map] at hs
    rcases hs with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · exact (ih s hs).cons i
    · exact List.perm_middle.trans ((ih s hs).cons i)

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma singletonCutSum_not_mem (w : J → SlopeWeight c η hc θ) (i : J) (l : List J)
    (g : List J → ℚ) (hi : i ∉ l) : singletonCutSum a c η hc θ w i l g=0 := by
  unfold singletonCutSum
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz
  apply ite_eq_right
  intro h
  apply hi
  exact (signedWordCuts_sublist a c η hc θ w l s hs).1.subset (by simp [h])

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma singletonCutSum_congr (w : J → SlopeWeight c η hc θ) (i : J) (l : List J)
    (g h : List J → ℚ)
    (he : ∀ s ∈ signedWordCuts a c η hc θ w l, s.left=[i] → g s.right=h s.right) :
    singletonCutSum a c η hc θ w i l g=singletonCutSum a c η hc θ w i l h := by
  unfold singletonCutSum
  congr 1
  apply List.map_congr_left
  intro s hs
  by_cases hi : s.left=[i]
  · rw [ite_eq_left hi,ite_eq_left hi,he s hs hi]
  · rw [ite_eq_right hi,ite_eq_right hi]

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma singletonCutSum_unique (w : J → SlopeWeight c η hc θ) (i : J) (l : List J)
    (g : List J → ℚ) (hi : i ∉ l) : singletonCutSum a c η hc θ w i (i::l) g=g l := by
  rw [singletonCutSum_cons,ite_eq_left rfl,singletonCutSum_not_mem a c η hc θ w i l _ hi,mul_zero,add_zero]

lemma functionalWord_top_not_perm (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f : J → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (hf : ∀ i,f i (globalUnit a c η hc θ)=0)
    (hfb : ∀ i j,f i (b j)=if i=j then 1 else 0)
    (u v : List J) (h : v.length=u.length) (hne : ¬u.Perm v) :
    (functionalWord a c η hc θ f u).ofConv (primitiveWord a c η hc θ b v)=0 := by
  induction u generalizing v with
  | nil =>
    have hv : v=[] := List.length_eq_zero_iff.mp h
    subst v
    exact (hne (.refl _)).elim
  | cons i u ih =>
    rw [functionalWord_top_singleton a c η hc θ w b hb hp f hf hfb i u v h]
    unfold singletonCutSum
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz
    by_cases hi : s.left=[i]
    · rw [ite_eq_left hi]
      have hpv := signedWordCuts_perm a c η hc θ w v s hs
      rw [hi,List.singleton_append] at hpv
      have hl := signedWordCuts_lengths a c η hc θ w v s hs
      rw [hi,List.length_singleton] at hl
      have hn : ¬u.Perm s.right := fun hh=>hne ((hh.cons i).trans hpv)
      change s.coeff * (functionalWord a c η hc θ f u).ofConv (primitiveWord a c η hc θ b s.right)=0
      rw [ih s.right (by simp only [List.length_cons] at h; omega) hn,mul_zero]
    · rw [ite_eq_right hi]

section Ordered
variable [LinearOrder J]

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma singletonCutSum_even_sorted (w : J → SlopeWeight c η hc θ) (i : J) (v : List J)
    (hv : v.Pairwise (· ≤ ·)) (hmin : ∀ j∈v,i≤j)
    (he : globalColorSign a c η hc θ (w i) (w i)=1) (r : ℚ) :
    singletonCutSum a c η hc θ w i v (fun _=>r)=(v.count i:ℚ)*r := by
  induction v with
  | nil => simp [singletonCutSum_nil]
  | cons j v ih =>
    rw [singletonCutSum_cons]
    have hv' := List.pairwise_cons.mp hv
    by_cases hij : j=i
    · subst j
      rw [ite_eq_left rfl,he,one_mul,ih hv'.2 (fun j hj=>hmin j (List.mem_cons_of_mem _ hj))]
      simp only [List.count_cons_self,Nat.cast_add,Nat.cast_one]
      ring
    · have hi : i∉j::v := by
        intro hm
        rcases List.mem_cons.mp hm with hh | hh
        · exact hij hh.symm
        · exact hij (le_antisymm (hv'.1 i hh) (hmin j (by simp)))
      have hit : i∉v := fun hm=>hi (List.mem_cons_of_mem _ hm)
      rw [ite_eq_right hij,singletonCutSum_not_mem a c η hc θ w i v _ hit,mul_zero,add_zero]
      rw [List.count_eq_zero.mpr hi,Nat.cast_zero,zero_mul]

lemma functionalWord_top_sorted_ne (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f : J → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (hf : ∀ i,f i (globalUnit a c η hc θ)=0)
    (hfb : ∀ i j,f i (b j)=if i=j then 1 else 0)
    (u v : List J) (hu : u.Pairwise (· ≤ ·)) (hv : v.Pairwise (· ≤ ·))
    (h : v.length=u.length) (hne : u≠v) :
    (functionalWord a c η hc θ f u).ofConv (primitiveWord a c η hc θ b v)=0 := by
  apply functionalWord_top_not_perm a c η hc θ w b hb hp f hf hfb u v h
  intro hpv
  exact hne (hpv.eq_of_pairwise' hu hv)

end Ordered
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
variable {J : Type*} [LinearOrder J]

def PBWAdmissible (w : J → SlopeWeight c η hc θ) (l : List J) : Prop :=
  l.Pairwise (fun i j=>i≤j ∧ (i=j → globalColorSign a c η hc θ (w i) (w i)=1))

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma PBWAdmissible.sorted {w : J → SlopeWeight c η hc θ} {l : List J}
    (h : PBWAdmissible a c η hc θ w l) : l.Pairwise (· ≤ ·) := h.imp (fun h=>h.1)

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma PBWAdmissible.tail {w : J → SlopeWeight c η hc θ} {i : J} {l : List J}
    (h : PBWAdmissible a c η hc θ w (i::l)) : PBWAdmissible a c η hc θ w l :=
  (List.pairwise_cons.mp h).2

omit [DecidableEq I] [Fact (SlopeEulerSymmetric a c η θ)] in
lemma singletonCutSum_sorted_self (w : J → SlopeWeight c η hc θ) (i : J) (l : List J)
    (h : PBWAdmissible a c η hc θ w (i::l)) (g : List J → ℚ) :
    singletonCutSum a c η hc θ w i (i::l) g=((l.count i+1:ℕ):ℚ)*g l := by
  by_cases hi : i∈l
  · have he := (List.pairwise_cons.mp h).1 i hi |>.2 rfl
    have hcst : singletonCutSum a c η hc θ w i (i::l) g=
        singletonCutSum a c η hc θ w i (i::l) (fun _=>g l) := by
      apply singletonCutSum_congr
      intro s hs hsi
      have hp := signedWordCuts_perm a c η hc θ w (i::l) s hs
      rw [hsi,List.singleton_append] at hp
      have hr := (signedWordCuts_sublist a c η hc θ w (i::l) s hs).2
      have heq : s.right=l := hp.cons_inv.eq_of_pairwise' (h.sorted.sublist hr) h.tail.sorted
      rw [heq]
    rw [hcst,singletonCutSum_even_sorted a c η hc θ w i (i::l) h.sorted
      (fun j hj=>by
        rcases List.mem_cons.mp hj with rfl | hj
        · exact le_rfl
        · exact (List.pairwise_cons.mp h.sorted).1 j hj) he,List.count_cons_self]
  · rw [singletonCutSum_unique a c η hc θ w i l g hi,List.count_eq_zero.mpr hi]
    simp

noncomputable def wordMultiplicity : List J → ℕ
  | [] => 1
  | i::l => (l.count i+1)*wordMultiplicity l

omit [LinearOrder J] in
lemma wordMultiplicity_pos (l : List J) : 0<wordMultiplicity l := by
  induction l with
  | nil => exact Nat.zero_lt_one
  | cons i l ih => exact Nat.mul_pos (Nat.succ_pos _) ih

lemma functionalWord_diagonal (w : J → SlopeWeight c η hc θ)
    (b : J → UnitalShuffle a c η hc θ) (hb : ∀ i,b i ∈ globalHomogeneous a c η hc θ (w i))
    (hp : ∀ i,b i ∈ globalPrimitives a c η hc θ)
    (f : J → UnitalShuffle a c η hc θ →ₗ[ℚ] ℚ) (hf : ∀ i,f i (globalUnit a c η hc θ)=0)
    (hfb : ∀ i j,f i (b j)=if i=j then 1 else 0)
    (l : List J) (hl : PBWAdmissible a c η hc θ w l) :
    (functionalWord a c η hc θ f l).ofConv (primitiveWord a c η hc θ b l)=(wordMultiplicity l:ℚ) := by
  induction l with
  | nil => exact globalCounit_unit a c η hc θ
  | cons i l ih =>
    rw [functionalWord_top_singleton a c η hc θ w b hb hp f hf hfb i l (i::l) rfl,
      singletonCutSum_sorted_self a c η hc θ w i l hl]
    rw [ih hl.tail]
    exact (Nat.cast_mul _ _).symm

end ElementaryPositivity.RawShuffle

end

end OAI
