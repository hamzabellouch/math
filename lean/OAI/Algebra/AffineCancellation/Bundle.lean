import OAI.Algebra.AffineCancellation.Degeneration
import OAI.Algebra.AffineCancellation.Modification

namespace OAI

noncomputable section

namespace ComplexCancellation.Bundle
open MvPolynomial
open Determinant

def quadricEval : Quadric.Poly →ₐ[ℂ] T := aeval ![a*b,d*c,d*b,Determinant.u]
lemma quadricEval_relation : quadricEval Quadric.relation=0 := by
  simp only [Quadric.relation,quadricEval,aeval_X,map_sub,map_mul,map_add,map_one,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  linear_combination b*d*determinant
def inclusion : Quadric.R →ₐ[ℂ] T := Ideal.Quotient.liftₐ _ quadricEval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,quadricEval_relation,zero_mul])
@[simp] lemma inclusion_π (r : Quadric.Poly) : inclusion (Quadric.π r)=quadricEval r :=
  Ideal.Quotient.lift_mk _ _ _
@[simp] lemma inclusion_x : inclusion Quadric.x=a*b := by simp [Quadric.x,quadricEval]
@[simp] lemma inclusion_y : inclusion Quadric.y=d*c := by simp [Quadric.y,quadricEval]
@[simp] lemma inclusion_z : inclusion Quadric.z=d*b := by simp [Quadric.z,quadricEval,Matrix.cons_val]
@[simp] lemma inclusion_u : inclusion Quadric.u=Determinant.u := by simp [Quadric.u,quadricEval,Matrix.cons_val]

abbrev K := FractionRing Quadric.R
def ι : Quadric.R →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ Quadric.R K
lemma ι_injective : Function.Injective ι := IsFractionRing.injective Quadric.R K
lemma x_ne_zero : ι Quadric.x ≠ 0 := by simpa using ι_injective.ne Quadric.x_ne_zero
def chartEval : Poly →ₐ[ℂ] K := aeval ![1,ι Quadric.z/ι Quadric.x,ι Quadric.x,
  ι Quadric.z+1,ι Quadric.u]
lemma chartEval_relation : chartEval relation=0 := by
  simp only [relation,chartEval,aeval_X,map_sub,map_mul,map_one,Matrix.cons_val,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  field_simp [x_ne_zero]
  ring
def chart : T →ₐ[ℂ] K := Ideal.Quotient.liftₐ _ chartEval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,chartEval_relation,zero_mul])
@[simp] lemma chart_π (r : Poly) : chart (π r)=chartEval r := Ideal.Quotient.lift_mk _ _ _
lemma chart_inclusion : chart.comp inclusion=ι := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change chart (inclusion Quadric.x)=ι Quadric.x
    rw [inclusion_x]
    simp [a,b,chartEval,Matrix.cons_val]
  · change chart (inclusion Quadric.y)=ι Quadric.y
    rw [inclusion_y]
    simp only [map_mul,d,c,chart_π,chartEval,aeval_X,Matrix.cons_val,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff x_ne_zero).mpr
    have he := congrArg ι Quadric.equation
    simp only [map_mul,map_add,map_one] at he
    linear_combination -he
  · change chart (inclusion Quadric.z)=ι Quadric.z
    simp [inclusion_z,d,b,chartEval,Matrix.cons_val,x_ne_zero]
  · change chart (inclusion Quadric.u)=ι Quadric.u
    simp [Determinant.u,chartEval,Matrix.cons_val]
lemma inclusion_injective : Function.Injective inclusion := by
  apply Function.Injective.of_comp (f := chart)
  rw [← AlgHom.coe_comp,chart_inclusion]
  exact ι_injective

def h : T := a*b-Determinant.u^3
def C₁ : T := c^2-b^2*h
def α : T := a^2*(1-2*b*d)
def β : T := d^2*(3+2*b*d)+α*h
lemma inclusion_s : inclusion Quadric.s=d*c-a*b*h := by
  simp only [Quadric.s,map_sub,map_mul,map_pow,inclusion_x,inclusion_y,inclusion_u,h]
lemma inclusion_f : inclusion Quadric.f=C₁*v := by
  simp only [Quadric.f,map_sub,map_pow,inclusion_x,inclusion_s,inclusion_u,C₁,h,v]
  linear_combination -(a*b-Determinant.u^3)*(a*c-b*d+1)*determinant
lemma inclusion_g : inclusion Quadric.g=b^2*v := by
  simp only [Quadric.g,map_sub,map_mul,inclusion_z,inclusion_s,inclusion_x,h,v]
  linear_combination -b*d*determinant
lemma certificate : α*C₁+β*b^2=1 := by
  simp only [α,β,C₁]
  linear_combination (1-2*b*d)*(a*c+b*d+1)*determinant
lemma v_ne_zero : v ≠ 0 := by
  intro hv
  have he : baseMap (X 1^3*X 3-X 1^2*X 0^3-X 2^2)=0 := by
    simpa [baseMap,baseValues,Matrix.cons_val,v] using hv
  have hp := baseMap_injective (he.trans (map_zero baseMap).symm)
  have hs := congrArg (MvPolynomial.eval (fun i : Fin 4 => if i=2 then (1:ℂ) else 0)) hp
  norm_num [Fin.ext_iff] at hs
abbrev B := AffineModification.T T v
instance : IsDomain B := Function.Injective.isDomain (AffineModification.embedding T v)
  (AffineModification.embedding_injective T v v_ne_zero)
def j : T →ₐ[ℂ] B := IsScalarTower.toAlgHom ℂ T B
def τ : B := AffineModification.τ T v
def V : B := AffineModification.V T v
lemma τ_ne_zero : τ ≠ 0 := by
  intro hz
  have he := congrArg (AffineModification.embedding T v) hz
  have hx : (RatFunc.X : AffineModification.K T)=0 := by
    simpa [τ,AffineModification.τ,AffineModification.eval,AffineModification.values] using he
  exact RatFunc.X_ne_zero hx
lemma equation : τ^2*V=j v := AffineModification.equation T v

def values : Fin 5 → B := ![τ,j (inclusion Quadric.s),j Determinant.u,j C₁*V,j (b^2)*V]
def eval : Degeneration.P →ₐ[ℂ] B := aeval values
lemma eval_xp : eval Degeneration.xp=j (inclusion Quadric.x) := by
  simp only [Degeneration.xp,eval,map_add,map_mul,map_pow,aeval_X,values,
    Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hf := congrArg j inclusion_f
  simp only [Quadric.f,map_sub,map_pow,inclusion_u,map_mul] at hf
  linear_combination -hf + j C₁*equation
lemma eval_yp : eval Degeneration.yp=j (inclusion Quadric.y) := by
  simp only [Degeneration.yp,map_add,map_mul,map_sub,map_pow,eval_xp]
  simp only [eval,aeval_X,values,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp only [Quadric.s,map_sub,map_mul,map_pow,inclusion_u]
  ring
lemma eval_zp : eval Degeneration.zp=j (inclusion Quadric.z) := by
  simp only [Degeneration.zp,map_add,map_mul,map_pow,eval_xp]
  simp only [eval,aeval_X,values,Matrix.cons_val,Matrix.cons_val_zero,Matrix.cons_val_one]
  have hg := congrArg j inclusion_g
  simp only [Quadric.g,map_sub,map_mul] at hg
  linear_combination -hg + j (b^2)*equation
lemma eval_relation : eval Degeneration.relation=0 := by
  have hi := congrArg eval Degeneration.identity
  simp only [map_sub,map_mul,map_add,map_pow,map_one,eval_xp,eval_yp,eval_zp] at hi
  have he := congrArg (j.comp inclusion) Quadric.equation
  simp only [AlgHom.comp_apply,map_mul,map_add,map_one] at he
  rw [sub_eq_zero.mpr he] at hi
  have hp : eval (X 0)≠0 := by simpa [eval,values] using τ_ne_zero
  exact (mul_eq_zero.mp hi.symm).resolve_left (pow_ne_zero 2 hp)
def pullback : Degeneration.G →ₐ[ℂ] B := Ideal.Quotient.liftₐ _ eval (by
  intro r hr
  obtain ⟨t,rfl⟩ := Ideal.mem_span_singleton.mp hr
  rw [map_mul,eval_relation,zero_mul])
@[simp] lemma pullback_π (r : Degeneration.P) : pullback (Degeneration.π r)=eval r :=
  Ideal.Quotient.lift_mk _ _ _
lemma pullback_coefficientMap : pullback.comp Degeneration.coefficientMap=j.comp inclusion := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change pullback (Degeneration.coefficientMap Quadric.x)=j (inclusion Quadric.x)
    rw [Degeneration.coefficientMap_x,Degeneration.x,pullback_π,eval_xp]
  · change pullback (Degeneration.coefficientMap Quadric.y)=j (inclusion Quadric.y)
    rw [Degeneration.coefficientMap_y,Degeneration.y,pullback_π,eval_yp]
  · change pullback (Degeneration.coefficientMap Quadric.z)=j (inclusion Quadric.z)
    rw [Degeneration.coefficientMap_z,Degeneration.z,pullback_π,eval_zp]
  · change pullback (Degeneration.coefficientMap Quadric.u)=j (inclusion Quadric.u)
    rw [Degeneration.coefficientMap_u,inclusion_u,Degeneration.u,pullback_π]
    simp [eval,values,Matrix.cons_val]
def base : Polynomial T →ₐ[ℂ] B := (AffineModification.baseMap T v).restrictScalars ℂ
lemma base_injective : Function.Injective base := by
  apply Function.Injective.of_comp (f := AffineModification.embedding T v)
  intro r s he
  change AffineModification.embedding T v (AffineModification.baseMap T v r)=
    AffineModification.embedding T v (AffineModification.baseMap T v s) at he
  have ht := AffineModification.embedding_baseMap T v
  simp only [← AlgHom.comp_apply,ht] at he
  exact AffineModification.baseEmbedding_injective T he
lemma pullback_baseMap : pullback.comp Degeneration.baseMap =
    base.comp (Polynomial.mapAlgHom inclusion) := by
  apply Polynomial.algHom_ext'
  · ext r
    simp only [AlgHom.comp_apply,Polynomial.CAlgHom_apply,Polynomial.coe_mapAlgHom,Polynomial.map_C]
    rw [Degeneration.baseMap_C]
    simp only [base,AlgHom.restrictScalars_apply,AffineModification.baseMap,Polynomial.aeval_C]
    change pullback (Degeneration.coefficientMap r)=j (inclusion r)
    exact DFunLike.congr_fun pullback_coefficientMap r
  · simp only [AlgHom.comp_apply,Polynomial.coe_mapAlgHom,Polynomial.map_X]
    rw [Degeneration.baseMap_X]
    simp only [base,AlgHom.restrictScalars_apply,AffineModification.baseMap,Polynomial.aeval_X]
    change pullback (Degeneration.π (X 0))=τ
    rw [pullback_π]
    simp [eval,values]
lemma pullback_injective : Function.Injective pullback := by
  apply Clearing.injective_of_clearing (S := Polynomial Quadric.R) pullback Degeneration.baseMap Polynomial.X
  · rw [pullback_baseMap]
    exact base_injective.comp (Polynomial.map_injective _ inclusion_injective)
  · rw [Degeneration.baseMap_X]; exact Degeneration.p_regular
  · exact Degeneration.clears
end ComplexCancellation.Bundle

end

end OAI
