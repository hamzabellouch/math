import Mathlib
import OAI.Algebra.FiniteTensor.FormalEvaluation

namespace OAI

/-! Relative derivations, graph evaluation and top exterior coefficients. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (R σ : Type*) [CommRing R]
  (p : ℕ) [CharP R p]

theorem pderiv_mem_uniform (i : σ) (f : MvPolynomial σ R)
    (hf : f∈ideal R σ (fun _ => p)) : MvPolynomial.pderiv i f∈ideal R σ (fun _ => p) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j,rfl⟩ := hf
    simp only [MvPolynomial.pderiv_pow,CharP.cast_eq_zero,zero_mul]
    exact Ideal.zero_mem _
  | zero => simp
  | add f g hf hg ihf ihg => simpa only [map_add] using (ideal R σ (fun _ => p)).add_mem ihf ihg
  | smul a f hf ih =>
    rw [smul_eq_mul,MvPolynomial.pderiv_mul]
    exact (ideal R σ (fun _ => p)).add_mem ((ideal R σ (fun _ => p)).mul_mem_left _ hf)
      ((ideal R σ (fun _ => p)).mul_mem_left _ ih)

 

def relativeDeriv (i : σ) : Ring R σ (fun _ => p) →ₗ[R] Ring R σ (fun _ => p) :=
  ((ideal R σ (fun _ => p)).restrictScalars R).liftQ
    ((Ideal.Quotient.mkₐ R (ideal R σ (fun _ => p))).toLinearMap.comp
      (MvPolynomial.pderiv i).toLinearMap) (by
      intro f hf
      change Ideal.Quotient.mk (ideal R σ (fun _ => p)) (MvPolynomial.pderiv i f)=0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (pderiv_mem_uniform R σ p i f hf))

@[simp] theorem partial_mk (i : σ) (f : MvPolynomial σ R) :
    relativeDeriv R σ p i (Ideal.Quotient.mk (ideal R σ (fun _ => p)) f)=
      Ideal.Quotient.mk (ideal R σ (fun _ => p)) (MvPolynomial.pderiv i f) := rfl

@[simp] theorem partial_coord [DecidableEq σ] (i j : σ) :
    relativeDeriv R σ p i (coord R σ (fun _ => p) j)=if i=j then 1 else 0 := by
  rw [coord,partial_mk,MvPolynomial.pderiv_X]
  by_cases h : i=j
  · subst j; simp
  · simp [Ne.symm h,h]

@[simp] theorem partial_scalar (i : σ) (a : R) :
    relativeDeriv R σ p i (algebraMap R (Ring R σ (fun _ => p)) a)=0 := by
  change relativeDeriv R σ p i (Ideal.Quotient.mk (ideal R σ (fun _ => p)) (MvPolynomial.C a))=0
  rw [partial_mk,MvPolynomial.pderiv_C,map_zero]

theorem partial_mul (i : σ) (a b : Ring R σ (fun _ => p)) :
    relativeDeriv R σ p i (a*b)=relativeDeriv R σ p i a*b+a*relativeDeriv R σ p i b := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [←map_mul,partial_mk,MvPolynomial.pderiv_mul]
  simp only [map_add,map_mul,partial_mk]

private theorem pderiv_commute (i j : σ) (f : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f)=
      MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  classical
  by_cases hij : i=j
  · subst j; rfl
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp [hf,hg]
  | mul_X f k hf =>
    by_cases hi : k=i <;> by_cases hj : k=j <;>
      simp [MvPolynomial.pderiv_X,hi,hj,hij,Ne.symm hij,eq_comm,hf] <;> ring

theorem partial_commute (i j : σ) (a : Ring R σ (fun _ => p)) :
    relativeDeriv R σ p i (relativeDeriv R σ p j a)=relativeDeriv R σ p j (relativeDeriv R σ p i a) := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [partial_mk,pderiv_commute]

def partialDerivation (i : σ) : Derivation R (Ring R σ (fun _ => p)) (Ring R σ (fun _ => p)) where
  toLinearMap := relativeDeriv R σ p i
  map_one_eq_zero' := by
    rw [←map_one (algebraMap R (Ring R σ (fun _ => p))),partial_scalar]
  leibniz' a b := by
    simpa only [smul_eq_mul,mul_comm,add_comm] using partial_mul R σ p i a b

 

theorem partial_nilEval [Fintype σ] (i : σ) (q : MvPowerSeries σ R) :
    relativeDeriv R σ p i (nilEval R (coord R σ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩) q)=
      nilEval R (coord R σ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩)
        (MvPowerSeries.pderiv i q) := by
  classical
  exact nilEval_pderiv (coord R σ (fun _ => p)) (fun j => ⟨p,coord_pow _ _ _ j⟩)
    i (partialDerivation R σ p i) (partial_coord R σ p i) q

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor
noncomputable section
variable {R A σ τ : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Finite σ] [Finite τ]

@[simp] theorem nilEval_rename (f : σ → τ) (v : τ → A) (hv : ∀ j, IsNilpotent (v j))
    (q : MvPowerSeries σ R) :
    nilEval R v hv (MvPowerSeries.rename f q)=nilEval R (v ∘ f) (fun i => hv (f i)) q := by
  rw [MvPowerSeries.rename_eq_subst,nilEval_subst (MvPowerSeries.X ∘ f) (MvPowerSeries.HasSubst.X_comp f)]
  simp only [Function.comp_apply,nilEval_X]
  rfl

 

theorem ideal_span_range_map {B ι : Type*} [CommRing B] [Fintype ι]
    (f : A →+* B) (a : A) (v : ι → A) (ha : a∈Ideal.span (Set.range v)) :
    f a∈Ideal.span (Set.range (fun i => f (v i))) := by
  obtain ⟨b,hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
  refine Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun i => f (b i),?_⟩
  rw [←hb]
  simp only [map_sum,map_mul]

variable {p : ℕ}
  {B : Type*} [CommRing B] [Algebra R B]

 

theorem graph_eval (H : σ → MvPowerSeries τ R) (hH : MvPowerSeries.HasSubst H)
    (v : τ → B) (hv : ∀ j, IsNilpotent (v j))
    (r : FiniteCoordinates.Ring R σ (fun _ => p) →ₐ[R] B)
    (hr : ∀ i, r (FiniteCoordinates.coord R σ (fun _ => p) i)=nilEval R v hv (H i))
    (q : MvPowerSeries σ R) :
    r (nilEval R (FiniteCoordinates.coord R σ (fun _ => p))
      (fun i => ⟨p,FiniteCoordinates.coord_pow _ _ _ i⟩) q)=
      nilEval R v hv (MvPowerSeries.subst H q) := by
  calc
    r (nilEval R (FiniteCoordinates.coord R σ (fun _ => p))
        (fun i => ⟨p,FiniteCoordinates.coord_pow _ _ _ i⟩) q) =
      nilEval R (fun i => r (FiniteCoordinates.coord R σ (fun _ => p) i))
        (fun i => (show IsNilpotent (FiniteCoordinates.coord R σ (fun _ => p) i) from
          ⟨p,FiniteCoordinates.coord_pow _ _ _ i⟩).map r) q :=
      nilEval_map r _ _ q
    _ = _ := by
      conv_rhs => rw [nilEval_subst H hH]
      simp only [hr]

end
end PD4Tensor

namespace PD4Tensor.Forms
noncomputable section
open scoped TensorProduct BigOperators
variable (K A : Type*) [Field K] [CommRing A] [Algebra K A] (N : ℕ)

 
def topExterior : E K (Fin N) →ₗ[K] K :=
  ExteriorAlgebra.liftAlternating (fun r =>
    if h : r=N then h.symm ▸ (Matrix.detRowAlternating : (Fin N → K) [⋀^Fin N]→ₗ[K] K)
    else 0)

@[simp] theorem topExterior_ιMulti (v : Fin N → Fin N → K) :
    topExterior K N (ExteriorAlgebra.ιMulti K N v) = Matrix.det v := by
  simp only [topExterior, ExteriorAlgebra.liftAlternating_apply_ιMulti]
  rfl

 
def topCoefficient : Ω K A (Fin N) →ₗ[A] A :=
  (TensorProduct.AlgebraTensorModule.rid K A A).toLinearMap.comp
    (TensorProduct.AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) (topExterior K N))

@[simp] theorem topCoefficient_tmul (a : A) (e : E K (Fin N)) :
    topCoefficient K A N (a ⊗ₜ[K] e) = topExterior K N e • a := by
  rfl

 
def oneFormLinear : (Fin N → A) →ₗ[A] Ω K A (Fin N) where
  toFun := oneForm K A (Fin N)
  map_add' := by
    intro v w
    simp only [oneForm, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' := by
    intro a v
    simp only [oneForm, Pi.smul_apply, Finset.smul_sum, TensorProduct.smul_tmul']
    rfl

variable [Invertible (2 : K)]
def exteriorScalarExtension : ExteriorAlgebra A (Fin N → A) →ₐ[A] Ω K A (Fin N) :=
  ExteriorAlgebra.lift A ⟨oneFormLinear K A N, fun v => oneForm_sq_zero v⟩

@[simp] theorem exteriorScalarExtension_ι (v : Fin N → A) :
    exteriorScalarExtension K A N (ExteriorAlgebra.ι A v) = oneForm K A (Fin N) v := by
  exact ExteriorAlgebra.lift_ι_apply A (oneFormLinear K A N) _ v

@[simp] theorem exteriorScalarExtension_ιMulti {r : ℕ} (v : Fin r → Fin N → A) :
    exteriorScalarExtension K A N (ExteriorAlgebra.ιMulti A r v) =
      (List.ofFn (fun i => oneForm K A (Fin N) (v i))).prod := by
  simp only [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact exteriorScalarExtension_ι K A N (v i)

 
theorem topCoefficient_oneForm_product (v : Fin N → Fin N → A) :
    topCoefficient K A N (List.ofFn (fun i => oneForm K A (Fin N) (v i))).prod = Matrix.det v := by
  let f : (Fin N → A) [⋀^Fin N]→ₗ[A] A :=
    ((topCoefficient K A N).comp (exteriorScalarExtension K A N).toLinearMap).compAlternatingMap
      (ExteriorAlgebra.ιMulti A N)
  have hf (v : Fin N → Fin N → A) : f v =
      topCoefficient K A N (List.ofFn (fun i => oneForm K A (Fin N) (v i))).prod := by
    exact congrArg (topCoefficient K A N) (exteriorScalarExtension_ιMulti K A N v)
  have hstd (i : Fin N) : oneForm K A (Fin N) (Pi.basisFun A (Fin N) i) =
      (1 : A) ⊗ₜ[K] dx K (Fin N) i := by
    simp only [oneForm, Pi.basisFun_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · simp
  have hprod : (List.ofFn (fun i => oneForm K A (Fin N) (Pi.basisFun A (Fin N) i))).prod =
      (1 : A) ⊗ₜ[K] ExteriorAlgebra.ιMulti K N (Pi.basisFun K (Fin N)) := by
    simp only [hstd, ExteriorAlgebra.ιMulti_apply]
    have hg : (List.ofFn (fun i => (1 : A) ⊗ₜ[K] dx K (Fin N) i)).prod =
        (1 : A) ⊗ₜ[K] (List.ofFn (fun i => dx K (Fin N) i)).prod := by
      have h := (Algebra.TensorProduct.includeRight : E K (Fin N) →ₐ[K] Ω K A (Fin N)).map_list_prod
        (List.ofFn (fun i => dx K (Fin N) i))
      change (1 : A) ⊗ₜ[K] (List.ofFn (fun i => dx K (Fin N) i)).prod =
        (List.map (fun e : E K (Fin N) => (1 : A) ⊗ₜ[K] e)
          (List.ofFn (fun i => dx K (Fin N) i))).prod at h
      rw [List.map_ofFn] at h
      exact h.symm
    convert hg using 1
    simp only [dx, Pi.basisFun_apply]
  have he : f (Pi.basisFun A (Fin N)) = 1 := by
    rw [hf, hprod, topCoefficient_tmul, topExterior_ιMulti]
    have hdet : Matrix.det (fun i => Pi.basisFun K (Fin N) i)=1 := by
      have h := (Pi.basisFun K (Fin N)).det_self
      change Matrix.detRowAlternating (Pi.basisFun K (Fin N))=1
      simpa only [Pi.basisFun_det] using h
    rw [hdet, one_smul]
  have h := f.eq_smul_basis_det (Pi.basisFun A (Fin N))
  rw [he, one_smul] at h
  rw [← hf, h, Pi.basisFun_det]
  rfl

end
end PD4Tensor.Forms
end

end OAI
