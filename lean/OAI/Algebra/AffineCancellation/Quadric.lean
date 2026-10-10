import OAI.Algebra.AffineCancellation.Clearing
import OAI.Algebra.AffineCancellation.DeterminantRigidity

namespace OAI

noncomputable section

namespace ComplexCancellation.Quadric
open MvPolynomial
abbrev Poly := MvPolynomial (Fin 4) ℂ
abbrev Base := MvPolynomial (Fin 3) ℂ
abbrev K := FractionRing Base
def relation : Poly := X 0*X 1-X 2*(X 2+1)
abbrev R := Poly ⧸ Ideal.span {relation}
def π : Poly →ₐ[ℂ] R := Ideal.Quotient.mkₐ ℂ _
def x : R := π (X 0)
def y : R := π (X 1)
def z : R := π (X 2)
def u : R := π (X 3)
def s : R := y-x*(x-u^3)
def f : R := x-s^2-u^3
def g : R := z-s*x

def baseEmbedding : Base →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ Base K
lemma baseEmbedding_injective : Function.Injective baseEmbedding := IsFractionRing.injective Base K
lemma x_field_nonzero : baseEmbedding (X 0) ≠ 0 := by
  simpa only [map_zero] using baseEmbedding_injective.ne (X_ne_zero (0 : Fin 3))
def values : Fin 4 → K := ![baseEmbedding (X 0),
  baseEmbedding (X 1)*(baseEmbedding (X 1)+1)/baseEmbedding (X 0),
  baseEmbedding (X 1),baseEmbedding (X 2)]
def eval : Poly →ₐ[ℂ] K := aeval values
lemma eval_relation : eval relation = 0 := by
  simp only [relation,eval,map_sub,map_mul,map_add,map_one,aeval_X,values,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
  field_simp [x_field_nonzero]
  ring

def embedding : R →ₐ[ℂ] K := Ideal.Quotient.liftₐ _ eval (by
  intro r hr
  obtain ⟨s,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,eval_relation,zero_mul])
@[simp] lemma embedding_π (r : Poly) : embedding (π r) = eval r := Ideal.Quotient.lift_mk _ _ _
lemma equation : x*y=z*(z+1) := by
  apply sub_eq_zero.mp
  have h : π relation = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simpa only [relation,map_sub,map_mul,map_add,map_one,x,y,z] using h
lemma x_regular : IsLeftRegular x := by
  apply Determinant.regular_quotient_of_prime (MvPolynomial.X_prime (i := 0))
  intro h
  have he := map_dvd (MvPolynomial.eval (fun i : Fin 4 => if i=2 then (1:ℂ) else 0)) h
  norm_num [relation,Fin.ext_iff] at he

def baseMap : Base →ₐ[ℂ] R := aeval ![x,z,u]
lemma baseMap_X_zero : baseMap (X 0) = x := by simp [baseMap]
lemma embedding_baseMap : embedding.comp baseMap = baseEmbedding := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [baseMap,x,z,u,eval,values]
lemma clears : Clearing.subalgebra baseMap (X 0) = ⊤ := by
  apply Clearing.top_of_generators π (Ideal.Quotient.mkₐ_surjective ℂ _) _ _
  intro i
  fin_cases i
  · exact ⟨0,X 0,by simp [baseMap,x]⟩
  · refine ⟨1,X 1*(X 1+1),?_⟩
    simp only [pow_one,baseMap,map_mul,map_add,map_one,aeval_X]
    exact equation
  · exact ⟨0,X 1,by simp [baseMap,z]⟩
  · exact ⟨0,X 2,by simp [baseMap,u]⟩
lemma embedding_injective : Function.Injective embedding := by
  apply Clearing.injective_of_clearing embedding baseMap (X 0)
  · rw [embedding_baseMap]; exact baseEmbedding_injective
  · rw [baseMap_X_zero]; exact x_regular
  · exact clears
instance : IsDomain R := Function.Injective.isDomain embedding embedding_injective
lemma baseMap_injective : Function.Injective baseMap := by
  apply Function.Injective.of_comp (f := embedding)
  rw [← AlgHom.coe_comp,embedding_baseMap]
  exact baseEmbedding_injective
lemma x_ne_zero : x ≠ 0 := by
  rw [← baseMap_X_zero]
  simpa only [map_zero] using baseMap_injective.ne (X_ne_zero (0 : Fin 3))

end ComplexCancellation.Quadric

end

end OAI
