import Mathlib
import OAI.Analysis.Commutator.FreeMoments

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} {S T : ι → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

variable (hsub : ∀ i, T i≤S i)

def Letter.enlarge (a : Letter T τ) : Letter S τ :=
  ⟨a.color,a.val,hsub a.color a.mem,a.centered⟩

@[simp] lemma word_enlarge (w : List (Letter T τ)) :
    word (w.map (Letter.enlarge hsub))=word w := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa only [List.map_cons,word_cons,Letter.enlarge] using congrArg (a.val*·) ih

lemma Reduced.enlarge {w : List (Letter T τ)} (hw : Reduced w) :
    Reduced (w.map (Letter.enlarge hsub)) := by
  exact (List.isChain_map (Letter.enlarge hsub)).mpr hw

variable (hstar : ∀ a : A, τ (star a)=star (τ a)) (h1 : τ 1=1) (hfree : Free S τ)

include hsub hstar h1 hfree in
lemma residual_word_pairing {j : ι} {a : A} (ha : a∈S j) (ha0 : τ a=0)
    (haT : ∀ b∈T j, τ (a*b)=0) (w : List (Letter T τ)) (hw : Reduced w) :
    τ (a*word w)=0 := by
  let b : Letter S τ := ⟨j,star a,star_mem ha,by rw [hstar,ha0,star_zero]⟩
  have hg := gram_word hstar h1 hfree [b] (w.map (Letter.enlarge hsub))
    (reduced_singleton b) (hw.enlarge hsub)
  simp only [word_enlarge,word_cons,word_nil,mul_one,b,star_star] at hg
  change τ (a*word w)=gram [b] (w.map (Letter.enlarge hsub)) at hg
  rw [hg]
  cases w with
  | nil => rfl
  | cons c w =>
    cases w with
    | nil =>
      by_cases hj : j=c.color
      · simp only [List.map_cons,List.map_nil,gram,b,Letter.enlarge,ite_eq_left hj,
          star_star,mul_one]
        exact haT c.val (hj ▸ c.mem)
      · simp [gram,b,Letter.enlarge,hj]
    | cons c' w =>
      simp only [List.map_cons,gram,b,Letter.enlarge,star_star]
      split_ifs <;> simp

include hsub hstar h1 hfree in
lemma residual_generated_pairing {j : ι} {a x : A} (ha : a∈S j) (ha0 : τ a=0)
    (haT : ∀ b∈T j, τ (a*b)=0) (hx : x∈⨆ i,T i) : τ (a*x)=0 := by
  rw [←reducedAlgebra_eq_iSup (S := T) hstar h1] at hx
  change x∈wordSpan T τ at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,hw,rfl⟩ := hx
    exact residual_word_pairing hsub hstar h1 hfree ha ha0 haT w hw
  | zero => simp
  | add x y _ _ hx hy => simp only [mul_add,map_add,hx,hy,add_zero]
  | smul z x _ hx => simp only [mul_smul_comm,map_smul,hx,smul_zero]

end Kadison.FreeMoments

namespace Kadison.SymmetryAlgebra

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable (s : A) (hs : star s=s) (hs2 : s*s=1)

def algebra : StarSubalgebra ℂ A where
  carrier := {a | ∃ z w : ℂ, a=z • (1:A)+w • s}
  zero_mem' := ⟨0,0,by simp⟩
  one_mem' := ⟨1,0,by simp⟩
  add_mem' := by
    rintro a b ⟨z,w,rfl⟩ ⟨z',w',rfl⟩
    exact ⟨z+z',w+w',by module⟩
  mul_mem' := by
    rintro a b ⟨z,w,rfl⟩ ⟨z',w',rfl⟩
    refine ⟨z*z'+w*w',z*w'+w*z',?_⟩
    simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
      one_mul,mul_one,hs2]
    module
  algebraMap_mem' z := ⟨z,0,by simp [Algebra.algebraMap_eq_smul_one]⟩
  star_mem' := by
    rintro a ⟨z,w,rfl⟩
    exact ⟨star z,star w,by simp only [star_add,star_smul,star_one,hs]⟩

@[simp] lemma mem_algebra {a : A} : a∈algebra s hs hs2 ↔ ∃ z w : ℂ,a=z • (1:A)+w • s := Iff.rfl

lemma self_mem : s∈algebra s hs hs2 := ⟨0,1,by simp⟩

lemma le_factor (D : StarSubalgebra ℂ A) (h : s∈D) : algebra s hs hs2≤D := by
  rintro a ⟨z,w,rfl⟩
  exact D.add_mem (D.smul_mem D.one_mem z) (D.smul_mem h w)

variable (S : Bool → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)

def factors : Bool → StarSubalgebra ℂ A := fun i => if i then algebra s hs hs2 else S false

variable (hsS : s∈S true) (hs0 : τ s=0) (hstar : ∀ a : A, τ (star a)=star (τ a))
  (h1 : τ 1=1) (hfree : FreeMoments.Free S τ)

include hsS in
lemma factors_le (i : Bool) : factors s hs hs2 S i≤S i := by
  cases i
  · exact le_rfl
  · exact le_factor s hs hs2 (S true) hsS

include hsS hs0 hstar h1 hfree in
theorem pairing_projection {a x : A} (ha : a∈S true)
    (hx : x∈⨆ i,factors s hs hs2 S i) :
    τ (a*x)=τ a*τ x+τ (a*s)*τ (s*x) := by
  let r := a-τ a • (1:A)-τ (a*s) • s
  have hr : r∈S true := (S true).sub_mem
    ((S true).sub_mem ha ((S true).smul_mem (S true).one_mem _)) ((S true).smul_mem hsS _)
  have hr0 : τ r=0 := by simp [r,map_sub,map_smul,h1,hs0]
  have hrs : τ (r*s)=0 := by
    simp [r,sub_mul,map_sub,map_smul,hs2,h1,hs0]
  have hrT : ∀ b∈factors s hs hs2 S true, τ (r*b)=0 := by
    rintro b ⟨z,w,rfl⟩
    simp only [mul_add,mul_smul_comm,mul_one,map_add,map_smul,hr0,hrs,smul_zero,add_zero]
  have hz := FreeMoments.residual_generated_pairing
    (factors_le s hs hs2 S hsS) hstar h1 hfree hr hr0 hrT hx
  dsimp only [r] at hz
  simp only [sub_mul,smul_mul_assoc,one_mul,map_sub,map_smul,smul_eq_mul] at hz
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hz)).trans (add_comm _ _)

end Kadison.SymmetryAlgebra

end

end
end

end OAI
