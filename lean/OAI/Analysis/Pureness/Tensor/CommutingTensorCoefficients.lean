import OAI.Analysis.Pureness.Operators.SimpleCStarAlgebraic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Algebra.Hom

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped BigOperators
variable {A B N : Type*} [NormedRing A] [CompleteSpace A] [Nontrivial A]
variable [NormedAlgebra ℂ A] [Ring B] [Algebra ℂ B] [Ring N] [Algebra ℂ N]
variable (φ : A →ₐ[ℂ] N) (ψ : B →ₐ[ℂ] N)
variable (hc : ∀ a b, Commute (φ a) (ψ b))

include hc in
omit [CompleteSpace A] [Nontrivial A] in
lemma commuting_relation_finiteIdealSum {ι : Type*} (s : Finset ι)
    (a : ι → A) (b : ι → B) (h : ∑ i ∈ s, φ (a i)*ψ (b i) = 0)
    (l : List (A × A)) :
    ∑ i ∈ s, φ (finiteIdealSum (a i) l)*ψ (b i) = 0 := by
  induction l with
  | nil => simp [finiteIdealSum]
  | cons p l ih =>
    have he (i : ι) : φ (p.1*a i*p.2)*ψ (b i) =
        φ p.1*(φ (a i)*ψ (b i))*φ p.2 := by
      simp only [map_mul]
      rw [mul_assoc (φ p.1 * φ (a i)), (hc p.2 (b i)).eq]
      simp only [mul_assoc]
    simp only [finiteIdealSum,List.map_cons,List.sum_cons,map_add,add_mul,
      Finset.sum_add_distrib] at *
    simp_rw [he]
    rw [← Finset.sum_mul,← Finset.mul_sum,h,mul_zero,zero_mul,ih,add_zero]

omit [NormedAlgebra ℂ A] in
lemma exists_finiteIdealSum_one (hsimple : TopologicallySimple A)
    (a : A) (ha : a ≠ 0) : ∃ l : List (A × A), finiteIdealSum a l = 1 := by
  let := topologicallySimple_isSimpleRing hsimple
  apply exists_finiteIdealSum
  exact IsSimpleRing.one_mem_of_ne_zero_mem (TwoSidedIdeal.span {a}) ha
    (TwoSidedIdeal.subset_span (Set.mem_singleton a))

include hc in

theorem commuting_relation_coefficients_zero (hsimple : TopologicallySimple A)
    (hψ : Function.Injective ψ) {ι : Type*} (b : ι → B)
    (hb : LinearIndependent ℂ b) (s : Finset ι) (a : ι → A)
    (h : ∑ i ∈ s, φ (a i)*ψ (b i)=0) : ∀ i ∈ s, a i=0 := by
  classical
  induction s using Finset.induction_on generalizing a with
  | empty => simp
  | @insert k s hks ih =>
    by_cases hak : a k=0
    · have hs : ∑ i ∈ s, φ (a i)*ψ (b i)=0 := by
        simpa [Finset.sum_insert hks,hak] using h
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hak
      · exact ih a hs i hi
    · obtain ⟨l, hl⟩ := exists_finiteIdealSum_one hsimple (a k) hak
      let c : ι → A := fun i => finiteIdealSum (a i) l
      have hck : c k=1 := hl
      have hrel : ∑ i ∈ insert k s, φ (c i)*ψ (b i)=0 :=
        commuting_relation_finiteIdealSum φ ψ hc _ a b h l
      have hcentral (i : ι) (hi : i ∈ insert k s) (x : A) : x*c i=c i*x := by
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simp [hck]
        have hr : ∑ j ∈ s, φ (x*c j-c j*x)*ψ (b j)=0 := by
          have he (j : ι) : φ (x*c j-c j*x)*ψ (b j) =
              φ x*(φ (c j)*ψ (b j))-(φ (c j)*ψ (b j))*φ x := by
            rw [map_sub,map_mul,map_mul,sub_mul]
            congr 1
            · exact mul_assoc _ _ _
            · rw [mul_assoc, (hc x (b j)).eq, ← mul_assoc]
          have hz : ∑ j ∈ insert k s, φ (x*c j-c j*x)*ψ (b j)=0 := by
            simp_rw [he]
            rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,
              hrel,mul_zero,zero_mul,sub_self]
          simpa [Finset.sum_insert hks,hck] using hz
        exact sub_eq_zero.mp (ih (fun j => x*c j-c j*x) hr i hi)
      have hs : ∀ i, ∃ d : ℂ, i ∈ insert k s → algebraMap ℂ A d=c i := by
        intro i
        by_cases hi : i ∈ insert k s
        · obtain ⟨d, hd⟩ := simple_complex_center_scalar hsimple (c i) (hcentral i hi)
          exact ⟨d, fun _ => hd⟩
        · exact ⟨0, fun h => (hi h).elim⟩
      choose d hd using hs
      have hz : ∑ i ∈ insert k s, d i • b i=0 := by
        apply hψ
        rw [map_zero,map_sum]
        convert hrel using 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul,← hd i hi,AlgHom.commutes,Algebra.smul_def]
      have hdk := (linearIndependent_iff'.mp hb) _ d hz k (Finset.mem_insert_self _ _)
      have hn : (0 : A)=1 := by
        rw [← hck,← hd k (Finset.mem_insert_self _ _),hdk,map_zero]
      exact (zero_ne_one hn).elim
end CuntzPureness

end

end OAI
