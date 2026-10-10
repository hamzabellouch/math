import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceEnergy
import OAI.NumberTheory.DirichletL.Dictionary.InverseAssignedCount

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily DetectorDictionaryInverseAssignedCount
local notation "O"=>HeckeFamily.O

private theorem sum_tuple_real {ι:Type*}[Fintype ι](L:ι→Finset (Ideal O))
    (f:(ι→Ideal O)→ℝ) :
    (∑q:Tuple L,f (fun i=>(q i).val))=∑q∈assignedTuples L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i,(mem_assignedTuples L q).mp hq i⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i
    exact congrArg Subtype.val (congrFun he i)
  · intro q hq
    refine ⟨fun i=>(q i).val,(mem_assignedTuples L _).mpr (fun i=>(q i).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [Fintype ι] in
theorem assignedMass_sum_le (K:ℕ){b U:ℝ}(hb:1≤b)(hU:1≤U)
    (L:ι→Finset (Ideal O))(J:Finset ι)(hJ:J.card≤K)(ell:ι→ℝ)
    (hL:∀i∈J,∀P∈L i,P≠0 ∧ (P.absNorm:ℝ)≤b*U^(ell i))
    (coeff:ι→Ideal O→ℂ)(hc:∀i∈J,∀P∈L i,‖coeff i P‖≤1) :
    (∑x:Assigned L J,assignedMass L J x coeff U (∑i∈J,ell i))≤assignedConstant K b := by
  have he:=assigned_sum_normalized_le K hb hU (by simpa using hJ)
    (fun i:↥J=>ell i) (fun i:↥J=>L i)
    (fun i P hP=>hL i i.property P hP)
    (fun i:↥J=>coeff i) (fun i P hP=>hc i i.property P hP)
  rw [←sum_tuple_real] at he
  simp only [assignedMass,assignedCoefficient,Finset.sum_coe_sort] at he ⊢
  convert he using 1
  congr 1
  ext x
  simp

theorem all_assignedMass_sum_le (K:ℕ){b U:ℝ}(hb:1≤b)(hU:1≤U)
    (hK:Fintype.card ι≤K)(L:ι→Finset (Ideal O))(ell:ι→ℝ)
    (hL:∀i,∀P∈L i,P≠0 ∧ (P.absNorm:ℝ)≤b*U^(ell i))
    (coeff:ι→Ideal O→ℂ)(hc:∀i,∀P∈L i,‖coeff i P‖≤1) :
    (∑J∈Finset.univ.powerset,∑x:Assigned L J,assignedMass L J x coeff U (∑i∈J,ell i))≤
      (2:ℝ)^K*assignedConstant K b := by
  calc
    _≤∑J∈(Finset.univ:Finset ι).powerset,assignedConstant K b := by
      apply Finset.sum_le_sum
      intro J hJ
      exact assignedMass_sum_le K hb hU L J ((Finset.card_le_univ J).trans hK) ell
        (fun i _=>hL i) coeff (fun i _=>hc i)
    _=(2:ℝ)^Fintype.card ι*assignedConstant K b := by
      simp
    _≤_:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hK)
      (assignedConstant_pos K hb).le

theorem original_energy_with_assigned_count (K:ℕ){b U:ℝ}(hb:1≤b)(hU:1≤U)
    (hK:Fintype.card ι≤K)(S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hp:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(ell:ι→ℝ)
    (hL:∀i,∀P∈L i,P≠0 ∧ (P.absNorm:ℝ)≤b*U^(ell i))
    (coeff:ι→Ideal O→ℂ)(hc:∀i,∀P∈L i,‖coeff i P‖≤1)(η:Ideal O→*ℂ)
    (hj:∀J:Finset ι,∀x:Assigned L J,CanonicalQuadraticSieve.Admissible (assignedIdeal L J x))
    (hη:∀J:Finset ι,∀x:Assigned L J,‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(r z:ℝ)(rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u)(E:ℝ)(hE:0≤E)
    (hres:∀J:Finset ι,∀x:Assigned L J,
      (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W U r z (∑i∈J,ell i) u‖^2)≤E) :
    (∑u∈rows,w u*‖∑q:Tuple L,(∏i,coeff i (q i).val)*
      InverseInitialConjugateEnergy.originalTotalPolynomial S (∏i,(q i).val) η (fun _=>1) W U r z u‖^2)≤
      ((2:ℝ)^K*assignedConstant K b)^2*E := by
  have hU0:0<U:=zero_lt_one.trans_le hU
  refine (original_energy_of_remaining S L hp hdis coeff η hj hη W U r z
    (fun J=>∑i∈J,ell i) hU0 rows w hw E hE hres).trans ?_
  apply mul_le_mul_of_nonneg_right _ hE
  apply pow_le_pow_left₀
    (Finset.sum_nonneg (fun J _=>Finset.sum_nonneg
      (fun x _=>assignedMass_nonneg L J x coeff U (∑i∈J,ell i) hU0)))
  exact all_assignedMass_sum_le K hb hU hK L ell hL coeff hc

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
