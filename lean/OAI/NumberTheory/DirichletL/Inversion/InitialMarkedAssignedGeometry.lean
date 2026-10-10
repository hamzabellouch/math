import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceProducts
import OAI.NumberTheory.DirichletL.Inversion.InitialQuotientGeometry

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialMarkedAssignedGeometry
open HeckeFamily ConcretePrimeRowBridge
open DetectorDictionaryInverseMarkedReference InverseInitialQuotientGeometry
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

 def assignedGenerator (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)(i:ι):O:=
  if h:i∈J then idealGenerator (x ⟨i,h⟩).val else 1

omit [Fintype ι] in
 theorem assignedGenerator_mem (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (i:ι)(hi:i∈J):assignedGenerator L J x i=idealGenerator (x ⟨i,hi⟩).val:=by
  simp only [assignedGenerator,dite_eq_left hi]

omit [Fintype ι] in
 theorem assignedGenerator_span (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (i:ι)(hi:i∈J):Ideal.span {assignedGenerator L J x i}=(x ⟨i,hi⟩).val:=by
  rw [assignedGenerator_mem L J x i hi,span_idealGenerator]

omit [Fintype ι] in
 theorem assignedGenerator_ne_zero (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (hne:∀i∈J,∀P∈L i,P≠0)(i:ι)(hi:i∈J):assignedGenerator L J x i≠0:=by
  rw [assignedGenerator_mem L J x i hi]
  exact idealGenerator_ne_zero _ (hne i hi _ (x ⟨i,hi⟩).property)

omit [Fintype ι] in
 theorem assignedElement_span (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J):
    Ideal.span {assignedElement J (assignedGenerator L J x)}=assignedIdeal L J x:=by
  rw [assignedElement,FiniteGaussPhase.span_finset_prod,←Finset.prod_coe_sort]
  unfold assignedIdeal
  apply Finset.prod_congr rfl
  intro i hi
  exact assignedGenerator_span L J x i.val i.property

omit [Fintype ι] in
 theorem assignedGenerator_window_live (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (U:ℝ)(ell:ι→ℝ)(W:ι→ℝ→ℂ)
    (hW:∀i∈J,∀P∈L i,W i ((P.absNorm:ℝ)/U^(ell i))≠0):
    ∀i∈J,W i ((Ideal.absNorm (Ideal.span {assignedGenerator L J x i}):ℝ)/U^(ell i))≠0:=by
  intro i hi
  rw [assignedGenerator_span L J x i hi]
  exact hW i hi _ (x ⟨i,hi⟩).property

omit [Fintype ι] [DecidableEq ι] in
 theorem assigned_ratio_product (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (U:ℝ)(hU:0<U)(ell:ι→ℝ):
    (Ideal.absNorm (assignedIdeal L J x):ℝ)/U^(assignedCenter J ell)=
      ∏i:↥J,((x i).val.absNorm:ℝ)/U^(ell i.val):=by
  simp only [assignedIdeal,map_prod,Nat.cast_prod,Finset.prod_div_distrib,
    ←Real.rpow_sum_of_pos hU,Finset.sum_coe_sort,assignedCenter]

omit [Fintype ι] [DecidableEq ι] in
 theorem assigned_ratio_interval (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (U:ℝ)(hU:0<U)(ell:ι→ℝ)(K:ℕ)(hK:J.card≤K)
    (hL:∀i∈J,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2):
    ((Ideal.absNorm (assignedIdeal L J x):ℝ)/U^(assignedCenter J ell))∈Set.Icc (1:ℝ) ((2:ℝ)^K):=by
  rw [assigned_ratio_product L J x U hU ell]
  constructor
  · have hh:=Finset.prod_le_prod₀ (s:=Finset.univ)
      (f:=fun _i:↥J=>(1:ℝ)) (g:=fun i=>((x i).val.absNorm:ℝ)/U^(ell i.val))
      (fun _ _=>zero_le_one) (fun i _=>(hL i.val i.property _ (x i).property).1)
    simpa only [Finset.prod_const_one] using hh
  · calc
      _≤∏_i:↥J,(2:ℝ):=Finset.prod_le_prod₀
        (fun i _=>(zero_le_one.trans (hL i.val i.property _ (x i).property).1))
        (fun i _=>(hL i.val i.property _ (x i).property).2)
      _=(2:ℝ)^J.card:=by simp
      _≤(2:ℝ)^K:=pow_le_pow_right₀ (by norm_num) hK

end SevenEighths.InverseInitialMarkedAssignedGeometry

end

end OAI
