import Mathlib
import OAI.Analysis.Commutator.FiniteFunctionalFactorization

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorFunctionals

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (K : Submodule ℂ H) [K.HasOrthogonalProjection]

def extendOperator : (K →L[ℂ] K) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := fun (R : K →L[ℂ] K) => K.subtypeL.comp (R.comp K.orthogonalProjectionOnto)
      map_add' := by intro R S; ext x; rfl
      map_smul' := by intro z R; ext x; rfl }
    1 (by
      intro R
      rw [one_mul]
      apply opNorm_le_bound _ (norm_nonneg R)
      intro x
      change ‖R (K.orthogonalProjectionOnto x)‖≤‖R‖*‖x‖
      exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (K.norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg R)))

omit [CompleteSpace H] in
@[simp] lemma extendOperator_apply (R : K →L[ℂ] K) (x : H) :
    extendOperator K R x=(R (K.orthogonalProjectionOnto x) : H) := rfl

local instance : NormedSpace ℂ (K →L[ℂ] K) := ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup (K →L[ℂ] K) := ContinuousLinearMap.toNormedAddCommGroup

lemma extendOperator_norm : ‖extendOperator K‖≤1 := by
  apply LinearMap.mkContinuous_norm_le _ zero_le_one

variable {ι : Type*} [Fintype ι]

def finiteFunctional (x y : ι → H) : StrongDual ℂ (H →L[ℂ] H) :=
  ∑ i, (innerSL ℂ (y i)).comp (ContinuousLinearMap.apply ℂ H (x i))

omit [CompleteSpace H] in
@[simp] lemma finiteFunctional_apply (x y : ι → H) (T : H →L[ℂ] H) :
    finiteFunctional x y T=∑ i, inner ℂ (y i) (T (x i)) := by
  simp [finiteFunctional]

omit [CompleteSpace H] [K.HasOrthogonalProjection] in
lemma tuple_coe_norm {n : ℕ} (x : PiLp 2 (fun _ : Fin n => K)) :
    ‖(WithLp.toLp 2 (fun i => (x i : H)) : PiLp 2 (fun _ : Fin n => H))‖=‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2]
  rfl

theorem exists_finite_support_factorization (a b : ι → H) :
    ∃ (n : ℕ) (x y : PiLp 2 (fun _ : Fin n => H)),
      (∀ T : H →L[ℂ] H, finiteFunctional a b T=∑ i, inner ℂ (y i) (T (x i))) ∧
        ‖x‖*‖y‖≤‖finiteFunctional a b‖ := by
  let L : Submodule ℂ H := Submodule.span ℂ (Set.range a ∪ Set.range b)
  let : FiniteDimensional ℂ L := FiniteDimensional.span_of_finite ℂ
    ((Set.finite_range a).union (Set.finite_range b))
  have ha : ∀ i, a i∈L := fun i => Submodule.subset_span (Or.inl ⟨i,rfl⟩)
  have hb : ∀ i, b i∈L := fun i => Submodule.subset_span (Or.inr ⟨i,rfl⟩)
  let ψ := (finiteFunctional a b).comp (extendOperator L)
  obtain ⟨x,y,hxy,hn⟩ := exists_finite_factorization ψ
  let x' : PiLp 2 (fun _ : Fin (Module.finrank ℂ L) => H) := WithLp.toLp 2 (fun i => (x i : H))
  let y' : PiLp 2 (fun _ : Fin (Module.finrank ℂ L) => H) := WithLp.toLp 2 (fun i => (y i : H))
  refine ⟨Module.finrank ℂ L,x',y',?_,?_⟩
  · intro T
    let Tc : L →L[ℂ] L := L.orthogonalProjectionOnto.comp (T.comp L.subtypeL)
    have he : ψ Tc=finiteFunctional a b T := by
      change finiteFunctional a b (extendOperator L Tc)=finiteFunctional a b T
      simp only [finiteFunctional_apply,extendOperator_apply]
      apply Finset.sum_congr rfl
      intro i _
      have hpa : L.orthogonalProjectionOnto (a i)=⟨a i,ha i⟩ :=
        L.orthogonalProjectionOnto_mem_subspace_eq_self ⟨a i,ha i⟩
      rw [hpa]
      change inner ℂ (⟨b i,hb i⟩ : L) (L.orthogonalProjectionOnto (T (a i)))=_
      exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨b i,hb i⟩ _
    rw [←he,hxy Tc]
    apply Finset.sum_congr rfl
    intro i _
    exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (y i) (T (x i))
  · rw [tuple_coe_norm L x,tuple_coe_norm L y]
    exact hn.trans ((opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (extendOperator_norm L)))

end Kadison.OperatorFunctionals

end

end
end

end OAI
