import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder ContinuousFunctionalCalculus

namespace Kadison.CFCTraceMoments

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local instance : ContinuousFunctionalCalculus ℂ (A × A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

local instance : ContinuousFunctionalCalculus ℝ (A × A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

lemma trace_cfc_of_powers (τ : A →ₚ[ℂ] ℂ) (a b : A)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hpow : ∀ n : ℕ,τ (a^n)=τ (b^n)) (f : ℝ → ℝ) (hf : Continuous f) :
    τ (cfc f a)=τ (cfc f b) := by
  have hab : IsSelfAdjoint (a,b) := Prod.ext ha hb
  have hpoly (p : Polynomial ℝ) : τ (Polynomial.aeval a p)=τ (Polynomial.aeval b p) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add,hp,hq]
    | monomial n r =>
      simp only [Polynomial.aeval_monomial,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
      change τ.toLinearMap (r • a^n)=τ.toLinearMap (r • b^n)
      rw [LinearMap.map_smul_of_tower,LinearMap.map_smul_of_tower]
      exact congrArg (fun z : ℂ => r • z) (hpow n)
  let S : Set C(spectrum ℝ (a,b),ℝ) :=
    {g | τ (cfcHom hab g).1=τ (cfcHom hab g).2}
  have hS : IsClosed S := isClosed_eq
    ((map_continuous τ).comp (cfcHom_continuous hab).fst)
    ((map_continuous τ).comp (cfcHom_continuous hab).snd)
  have hsub : (polynomialFunctions (spectrum ℝ (a,b)) : Set C(spectrum ℝ (a,b),ℝ))⊆S := by
    rw [polynomialFunctions_coe]
    rintro g ⟨p,rfl⟩
    change τ (cfcHom hab (Polynomial.toContinuousMapOnAlgHom (spectrum ℝ (a,b)) p)).1=
      τ (cfcHom hab (Polynomial.toContinuousMapOnAlgHom (spectrum ℝ (a,b)) p)).2
    have he : cfcHom hab (Polynomial.toContinuousMapOnAlgHom (spectrum ℝ (a,b)) p)=
        Polynomial.aeval (a,b) p := by
      rw [← cfc_polynomial p (a,b) hab,cfc_apply p.eval (a,b) hab p.continuous.continuousOn]
      rfl
    rw [he,Polynomial.aeval_prod_apply]
    exact hpoly p
  have hd : closure (polynomialFunctions (spectrum ℝ (a,b)) : Set C(spectrum ℝ (a,b),ℝ))=Set.univ := by
    rw [←Subalgebra.topologicalClosure_coe,polynomialFunctions.topologicalClosure]
    rfl
  have all : ∀ g : C(spectrum ℝ (a,b),ℝ),g∈S :=
    fun g => closure_minimal hsub hS (hd.symm ▸ Set.mem_univ g)
  have hm : τ (cfc f (a,b)).1=τ (cfc f (a,b)).2 := by
    rw [cfc_apply f (a,b) hab hf.continuousOn]
    exact all _
  rw [cfc_map_prod (S := ℂ) f a b hf.continuousOn hab ha hb] at hm
  exact hm

omit [StarOrderedRing A] in
lemma trace_cyclic_powers (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))
    (a b : A) (n : ℕ) : τ ((a*b)^n)=τ ((b*a)^n) := by
  cases n with
  | zero => simp
  | succ n =>
    have h : SemiconjBy a (b*a) (a*b) := (mul_assoc a b a).symm
    have hn := h.pow_right n
    change a*(b*a)^n=(a*b)^n*a at hn
    calc
      τ ((a*b)^(n+1))=τ (((a*b)^n*a)*b) := by rw [pow_succ,mul_assoc]
      _=τ ((a*(b*a)^n)*b) := by rw [hn]
      _=τ ((b*a)^n*(b*a)) := by rw [mul_assoc,hτ a ((b*a)^n*b),mul_assoc]
      _=τ ((b*a)^(n+1)) := by rw [pow_succ]

end Kadison.CFCTraceMoments

end

end
end

end OAI
