import Mathlib
import OAI.Analysis.AffineBernstein.CapInverseBound
import OAI.Analysis.AffineBernstein.ActualFlatInverse

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section FixedBasisCoordinates
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
def targetBasisCoordinates {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ G) :
    G ≃L[ℝ] (Space n × ℝ) :=
  (b.equiv (graphAmbientBasis n) (Equiv.refl _)).toContinuousLinearEquiv
lemma targetBasisCoordinates_map {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ G) :
    b.map (targetBasisCoordinates b).toLinearEquiv = graphAmbientBasis n := by
  simp [targetBasisCoordinates,Module.Basis.map_equiv]
lemma targetBasisCoordinates_det {n : ℕ} (b : Module.Basis (Fin n ⊕ Unit) ℝ G)
    (L : G ≃L[ℝ] (Space n × ℝ)) :
    (L.symm.trans (targetBasisCoordinates b)).toContinuousLinearMap.det =
      b.det ((graphAmbientBasis n).map L.symm.toLinearEquiv) := by
  let T := targetBasisCoordinates b
  have hm := Module.Basis.det_map b T.toLinearEquiv
    (fun i => (L.symm.trans T) (graphAmbientBasis n i))
  rw [targetBasisCoordinates_map] at hm
  have hc : ((L.symm.trans T).toContinuousLinearMap.det) =
      (graphAmbientBasis n).det (fun i => (L.symm.trans T) (graphAmbientBasis n i)) := by
    change LinearMap.det (L.symm.trans T).toLinearEquiv.toLinearMap = _
    simpa only [Module.Basis.det_self,mul_one,Function.comp_def,LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] using
      (Module.Basis.det_comp (graphAmbientBasis n)
        (L.symm.trans T).toLinearEquiv.toLinearMap (graphAmbientBasis n)).symm
  rw [hc,hm]
  congr 1
  funext i
  simp [ContinuousLinearEquiv.trans_apply]

end FixedBasisCoordinates

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Restriction of a pulled target-base covector to the original graph is literally affine
in the original ambient coordinates. The coefficients are derived, not postulated. -/
lemma pulledBaseGraphFunction_coefficients {n : ℕ} (u : Space n → ℝ)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ)) (ℓ : S →L[ℝ] ℝ) :
    ∃ (α : Space n →L[ℝ] ℝ) (β d : ℝ),
      pulledBaseGraphFunction u a L ℓ = graphAffineFunction u α β d ∧
      ∀ p : Space n × ℝ, ℓ (L.symm (p-a)).1 = α p.1 + β*p.2+d := by
  let F : (Space n × ℝ) →L[ℝ] ℝ :=
    ℓ.comp ((ContinuousLinearMap.fst ℝ S E).comp L.symm.toContinuousLinearMap)
  let α := F.comp (ContinuousLinearMap.inl ℝ (Space n) ℝ)
  let β := F (0,1)
  let d := -F a
  have he (p : Space n × ℝ) : F p = α p.1 + β*p.2 := by
    have hsplit : p = (p.1,0) + p.2 • ((0:Space n),1) := by ext <;> simp
    calc
      F p = F ((p.1,0) + p.2 • ((0:Space n),1)) := congrArg F hsplit
      _ = α p.1 + β*p.2 := by
        rw [map_add,map_smul]
        change α p.1 + p.2*β = _
        rw [mul_comm p.2]
  have h (p : Space n × ℝ) : ℓ (L.symm (p-a)).1 = α p.1+β*p.2+d := by
    change F (p-a) = _
    rw [map_sub,he p]
    rfl
  refine ⟨α,β,d,?_,h⟩
  funext x
  exact h (x,u x)

lemma inverseMatrixPair_graphAffineFunction {n : ℕ} (u : Space n → ℝ)
    (α : Space n →L[ℝ] ℝ) (β d : ℝ) (x : Space n) :
    inverseMatrixPair (hessian u x)
      (fun i => dirDeriv (coordinateVector n i) (graphAffineFunction u α β d) x)
      (fun i => dirDeriv (coordinateVector n i) (graphAffineFunction u α β d) x) =
      graphInverseMetric u α β d x := by
  unfold inverseMatrixPair graphInverseMetric
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end AffineBernstein
end

end OAI
