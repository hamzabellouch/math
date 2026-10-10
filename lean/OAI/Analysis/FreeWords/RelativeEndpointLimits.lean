import Mathlib
import OAI.Analysis.FreeWords.MatrixLeftEndpoint
import OAI.Analysis.FreeWords.RelativeEndpointLimitsDefinitions

namespace OAI

noncomputable section

namespace KKRelativeEndpoints

noncomputable section

open Filter KKHaarEndpoints KKControlledConjugation KKRelativeMatrix

open scoped Topology

variable {A:Type*} [Ring A] [StarRing A] [Algebra ℂ A]

def balancedWord {n:ℕ}
    (w:List (Matrix (Fin n) (Fin n) A×Matrix (Fin n) (Fin n) A)) :=
  w.flatMap fun z => [((1:ℤ),z.1),(-1,z.2)]

theorem amplifyConj_diagonal (n:ℕ) (u:unitary A) (X:Matrix (Fin n) (Fin n) A) :
    amplifyConj n u X=Matrix.diagonal (fun _:Fin n => u.val)*X*
      Matrix.diagonal (fun _:Fin n => (u⁻¹).val) := by
  ext i j
  simp only [amplifyConj_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  rfl

theorem balancedWord_value {n:ℕ} (u:unitary A)
    (w:List (Matrix (Fin n) (Fin n) A×Matrix (Fin n) (Fin n) A)) :
    matrixWord (fun k => (u^k).val) (balancedWord w)=relativePair u w := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    simp only [matrixWord,balancedWord,List.flatMap_cons,List.map_append,List.prod_append,
      List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,zpow_one,zpow_neg_one]
    change _* matrixWord (fun k => (u^k).val) (balancedWord w)=_
    rw [ih]
    simp only [relativePair,List.map_cons,List.prod_cons,amplifyConj_diagonal,mul_assoc]

omit [StarRing A] in
theorem balancedWord_centered (τ:A →ₗ[ℂ] ℂ) {n:ℕ}
    (w:List (Matrix (Fin n) (Fin n) A×Matrix (Fin n) (Fin n) A))
    (hw:∀z∈w,∀a b,τ (z.1 a b)=0 ∧ τ (z.2 a b)=0) :
    ∀z∈balancedWord w,z.1≠0 ∧ ∀a b,z.2 a b∈(⊤:Subalgebra ℂ A) ∧ τ (z.2 a b)=0 := by
  intro z hz
  obtain ⟨c,hc,hz⟩ := List.mem_flatMap.mp hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl
  · exact ⟨by norm_num,fun a b => ⟨by trivial,(hw c hc a b).1⟩⟩
  · exact ⟨by norm_num,fun a b => ⟨by trivial,(hw c hc a b).2⟩⟩

theorem oddWord_value {n:ℕ} (u:unitary A)
    (z:Matrix (Fin n) (Fin n) A×Matrix (Fin n) (Fin n) A)
    (w:List (Matrix (Fin n) (Fin n) A×Matrix (Fin n) (Fin n) A))
    (c:Matrix (Fin n) (Fin n) A) :
    relativePair u (z::w)*amplifyConj n u c=
      amplifyConj n u (z.1*matrixWord (fun k => (u^k).val)
        ((-1,z.2)::balancedWord w++[(1,c)])) := by
  simp only [relativePair,List.map_cons,List.prod_cons,amplifyConj_diagonal,matrixWord,
    List.map_append,List.prod_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    mul_one,zpow_neg_one,zpow_one]
  have hb := balancedWord_value u w
  simp only [matrixWord] at hb
  rw [hb]
  simp only [relativePair,amplifyConj_diagonal,mul_assoc]

theorem relative_endpoint_limits : RelativeEndpointLimits (A := A) := by
  intro ι L τ u h1 htr hH hC n w hw
  have hleft := matrix_left_endpoint_limits ι L τ ⊤ u h1 htr hH hC
  refine ⟨?_,?_⟩
  · intro hn a b
    have hbn : balancedWord w≠[] := by
      cases w with
      | nil => exact (hn rfl).elim
      | cons z w => simp [balancedWord]
    have hh := hleft n (balancedWord w) hbn (balancedWord_centered τ w hw) 1
      (fun _ _ => by trivial) a b
    simpa only [one_mul,balancedWord_value] using hh
  · intro c hc a b
    cases w with
    | nil =>
      simpa only [relativePair,List.map_nil,List.prod_nil,one_mul,amplifyConj_apply,
        conj_trace τ htr,hc] using (tendsto_const_nhds : Tendsto (fun _:ι => (0:ℂ)) L (𝓝 0))
    | cons z w =>
      have hz := hw z List.mem_cons_self
      have hwt := fun x hx => hw x (List.mem_cons_of_mem _ hx)
      have hcw : ∀x∈(-1,z.2)::balancedWord w++[(1,c)],
          x.1≠0 ∧ ∀a b,x.2 a b∈(⊤:Subalgebra ℂ A) ∧ τ (x.2 a b)=0 := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨by norm_num,fun a b => ⟨by trivial,(hz a b).2⟩⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact balancedWord_centered τ w hwt x hx
        · have he := List.mem_singleton.mp hx
          subst x
          exact ⟨by norm_num,fun a b => ⟨by trivial,hc a b⟩⟩
      have hh := hleft n ((-1,z.2)::balancedWord w++[(1,c)]) (by simp) hcw z.1
        (fun _ _ => by trivial) a b
      simpa only [oddWord_value,amplifyConj_apply,conj_trace τ htr] using hh

end

end KKRelativeEndpoints
end

end OAI
