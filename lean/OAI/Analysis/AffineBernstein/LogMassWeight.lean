import Mathlib
import OAI.Analysis.AffineBernstein.ActualLogMeasure

namespace OAI

noncomputable section

namespace AffineBernstein

section DependencyScope
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LogMassWeight
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Exact coordinate formula for the true inverse-block logarithmic norm. -/
lemma tubeBasePair_coordinate_log {k : ℕ} (H : Space k × E → ℝ) (q : Space k × E)
    (i : Fin k) (hq : q.1 i ≠ 0) :
    tubeBasePair H (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
      (fun z => Real.log (z.1 i)) (fun z => Real.log (z.1 i)) q =
      H q*(tubeBaseMatrix H q (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹ i i/(q.1 i)^2 := by
  let ℓ : (Space k × E) →L[ℝ] ℝ := (EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (Space k) E)
  have hd : HasFDerivAt (fun z : Space k × E => Real.log (z.1 i)) ((q.1 i)⁻¹ • ℓ) q :=
    ℓ.hasFDerivAt.log hq
  have hv (j : Fin k) : dirDeriv ((EuclideanSpace.basisFun (Fin k) ℝ) j,(0:E))
      (fun z : Space k × E => Real.log (z.1 i)) q = (q.1 i)⁻¹*(if i=j then 1 else 0) := by
    rw [dirDeriv,hd.fderiv]
    simp [ℓ,EuclideanSpace.basisFun_apply]
  simp only [tubeBasePair,flatInversePair,OrthonormalBasis.coe_toBasis,hv]
  simp only [mul_ite,ite_mul,mul_one,mul_zero,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  field_simp [hq]

/- On a positive base collar, the manuscript's sigma weight is bounded by
one plus the actual inverse-Hessian trace, with the exact support-height factor. -/
lemma tubeLogMassWeight_le_trace {k : ℕ} (H : Space k × E → ℝ) (q : Space k × E)
    {r M : ℝ} (hr : 0 < r) (hs : ∀ i, r ≤ q.1 i)
    (hh : 0 ≤ H q) (hhM : H q ≤ M)
    (hB : (tubeBaseMatrix H q (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).PosDef) :
    tubeLogMassWeight H q ≤ 1 + (M/r^2)*(tubeBaseMatrix H q
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹.trace := by
  unfold tubeLogMassWeight
  refine add_le_add le_rfl ?_
  rw [Matrix.trace,Finset.mul_sum]
  simp only [Matrix.diag_apply]
  apply Finset.sum_le_sum
  intro i _
  rw [tubeBasePair_coordinate_log H q i (ne_of_gt (hr.trans_le (hs i)))]
  have hb : 0 ≤ (tubeBaseMatrix H q (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹ i i :=
    hB.inv.posSemidef.diag_nonneg
  have hden : r^2 ≤ (q.1 i)^2 := sq_le_sq₀ hr.le (hr.le.trans (hs i)) |>.mpr (hs i)
  calc
    _ ≤ (M * (tubeBaseMatrix H q (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹ i i)/r^2 :=
      div_le_div₀ (mul_nonneg (hh.trans hhM) hb) (mul_le_mul_of_nonneg_right hhM hb) (sq_pos_of_pos hr) hden
    _ = _ := by ring
end LogMassWeight

/- Real positive densities can be interpolated before or after `ofReal`. -/

end DependencyScope

end AffineBernstein

end

end OAI
