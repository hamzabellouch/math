import Mathlib

namespace OAI

namespace FiberFunctorProof
open scoped TensorProduct
universe u
variable (k : Type u) [Field k]
attribute [local instance 1100] HahnSeries.instAlgebra

abbrev planeCompletion := AdicCompletion (MvPolynomial.idealOfVars (Fin 2) k)
  (MvPolynomial (Fin 2) k)

 
def formalLineEmbedding : Unit ↪ Fin 2 := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩

noncomputable def formalLineMap : planeCompletion k →ₐ[k] PowerSeries k :=
  (MvPowerSeries.killCompl (formalLineEmbedding)).comp
    ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin 2) k).symm.restrictScalars k).toAlgHom

 

noncomputable def formalLineFieldMap : planeCompletion k →ₐ[k] LaurentSeries k :=
  (HahnSeries.ofPowerSeriesAlg ℤ k).comp (formalLineMap k)

lemma formalLineMap_poly :
    (formalLineMap k).comp (IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k) (planeCompletion k)) =
    MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then (PowerSeries.X : PowerSeries k) else 0) := by
  ext i : 1
  change MvPowerSeries.killCompl (formalLineEmbedding)
    ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin 2) k).symm
      (algebraMap (MvPolynomial (Fin 2) k) (planeCompletion k) (MvPolynomial.X i))) = _
  rw [AlgEquiv.commutes]
  rw [MvPowerSeries.algebraMap_apply', MvPolynomial.coe_X, MvPowerSeries.map_X]
  fin_cases i
  · simp only [MvPolynomial.aeval_X]
    change MvPowerSeries.killCompl (R := k) formalLineEmbedding (MvPowerSeries.X 0) = PowerSeries.X
    exact MvPowerSeries.killCompl_X (R := k) (e := formalLineEmbedding) ()
  · rw [MvPowerSeries.killCompl_X_eq_zero]
    · simp
    · rintro ⟨u,hu⟩
      exact Fin.zero_ne_one (show (0 : Fin 2) = 1 from hu)

@[simp] lemma formalLineMap_of (P : MvPolynomial (Fin 2) k) :
    formalLineMap k (algebraMap (MvPolynomial (Fin 2) k) (planeCompletion k) P) =
      MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then (PowerSeries.X : PowerSeries k) else 0) P :=
  congrArg (fun f : MvPolynomial (Fin 2) k →ₐ[k] PowerSeries k => f P) (formalLineMap_poly k)

@[simp] lemma formalLineMap_X :
    formalLineMap k (algebraMap (MvPolynomial (Fin 2) k) (planeCompletion k) (MvPolynomial.X 0)) =
      PowerSeries.X := by simp

@[simp] lemma formalLineMap_Y :
    formalLineMap k (algebraMap (MvPolynomial (Fin 2) k) (planeCompletion k) (MvPolynomial.X 1)) = 0 := by
  simp

lemma formalLineFieldMap_X_ne_zero :
    formalLineFieldMap k (algebraMap (MvPolynomial (Fin 2) k) (planeCompletion k)
      (MvPolynomial.X 0)) ≠ 0 := by
  change HahnSeries.ofPowerSeries ℤ k (formalLineMap k _) ≠ 0
  rw [formalLineMap_X]
  intro hz
  apply PowerSeries.X_ne_zero (R := k)
  exact (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k))
    (hz.trans (map_zero _).symm)

 

lemma formalLineMap_coeff_eq (n : ℕ) (x y : planeCompletion k)
    (h : x.val (n+1) = y.val (n+1)) :
    PowerSeries.coeff n (formalLineMap k x) = PowerSeries.coeff n (formalLineMap k y) := by
  change MvPowerSeries.coeff (Finsupp.single () n)
      (MvPowerSeries.killCompl (formalLineEmbedding) ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin 2) k).symm x)) =
    MvPowerSeries.coeff (Finsupp.single () n)
      (MvPowerSeries.killCompl (formalLineEmbedding) ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin 2) k).symm y))
  simp only [MvPowerSeries.coeff_killCompl, Finsupp.embDomain_single]
  change MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
      ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin 2) k).symm x) =
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
      ((MvPowerSeries.toAdicCompletionAlgEquiv (Fin 2) k).symm y)
  simp only [MvPowerSeries.toAdicCompletionAlgEquiv_symm_apply,
    MvPowerSeries.coeff_toAdicCompletionInv]
  apply congrArg (fun polynomial : MvPolynomial (Fin 2) k =>
    polynomial.coeff (Finsupp.single (0 : Fin 2) n))
  have h' : x.val ((Finsupp.single (0 : Fin 2) n).degree + 1) =
      y.val ((Finsupp.single (0 : Fin 2) n).degree + 1) := by
    rw [Finsupp.degree_single]
    exact h
  exact congrArg Quotient.out h'
end FiberFunctorProof

end OAI
