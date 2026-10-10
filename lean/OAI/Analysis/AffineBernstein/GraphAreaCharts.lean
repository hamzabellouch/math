import Mathlib
import OAI.Analysis.AffineBernstein.Basic

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {n : ℕ}

lemma det_updateCol_identity (i : Fin n) (v : Fin n → ℝ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ).updateCol i v).det = v i := by
  have hh := Matrix.det_updateCol_sum (1 : Matrix (Fin n) (Fin n) ℝ) i v
  simpa only [Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true,Matrix.det_one] using hh

lemma toMatrix_fderiv_euclidean {F : Space n → Space n} {x : Space n}
    (hd : DifferentiableAt ℝ F x) (i j : Fin n) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (fderiv ℝ F x).toLinearMap i j =
      fderiv ℝ (fun y => F y i) x (coordinateVector n j) := by
  have he := ((EuclideanSpace.proj i : Space n →L[ℝ] ℝ).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  rw [LinearMap.toMatrix_apply]
  change ((EuclideanSpace.basisFun (Fin n) ℝ).repr
    (fderiv ℝ F x ((EuclideanSpace.basisFun (Fin n) ℝ) j))) i = _
  rw [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply]
  exact (congrArg (fun T : Space n →L[ℝ] ℝ => T (coordinateVector n j)) he).symm

/-- Reciprocal projective chart of the Gauss covector. In the chart where
coordinate `i` dominates the normal, its image lies in a fixed cube. -/
def reciprocalChart (i : Fin n) (p : Space n) : Space n :=
  WithLp.toLp 2 (fun j => if j=i then (p i)⁻¹ else p j / p i)

lemma reciprocalChart_involutive (i : Fin n) {p : Space n} (hp : p i ≠ 0) :
    reciprocalChart i (reciprocalChart i p) = p := by
  ext j
  by_cases hj : j=i
  · subst j
    simp [reciprocalChart]
  · simp [reciprocalChart,hj,hp]

lemma reciprocalChart_injOn (i : Fin n) :
    Set.InjOn (reciprocalChart i) {p : Space n | p i ≠ 0} := by
  intro p hp q hq he
  have hh := congrArg (reciprocalChart i) he
  rwa [reciprocalChart_involutive i hp,reciprocalChart_involutive i hq] at hh

lemma contDiffAt_reciprocalChart (i : Fin n) {p : Space n} (hp : p i ≠ 0) :
    ContDiffAt ℝ ∞ (reciprocalChart i) p := by
  apply (contDiffAt_piLp 2).mpr
  intro j
  by_cases hj : j=i
  · simpa only [reciprocalChart,WithLp.ofLp_toLp,hj,ite_true,Pi.inv_def,EuclideanSpace.coe_proj] using
      ((EuclideanSpace.proj i : Space n →L[ℝ] ℝ).contDiff.contDiffAt.inv hp)
  · simpa only [reciprocalChart,WithLp.ofLp_toLp,hj,ite_false,Pi.div_def,EuclideanSpace.coe_proj] using
      ((EuclideanSpace.proj j : Space n →L[ℝ] ℝ).contDiff.contDiffAt).div
        ((EuclideanSpace.proj i : Space n →L[ℝ] ℝ).contDiff.contDiffAt) hp

lemma det_fderiv_reciprocalChart (i : Fin n) {p : Space n} (hp : p i ≠ 0) :
    (fderiv ℝ (reciprocalChart i) p).det = -((p i)⁻¹)^(n+1) := by
  let v : Fin n → ℝ := fun j => if j=i then -(p i)⁻¹ else -p j / p i
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hm : LinearMap.toMatrix b b (fderiv ℝ (reciprocalChart i) p).toLinearMap =
      (p i)⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ).updateCol i v := by
    ext j k
    rw [toMatrix_fderiv_euclidean ((contDiffAt_reciprocalChart i hp).differentiableAt (by simp))]
    have hi : HasFDerivAt (fun z : Space n => (z i)⁻¹)
        (-(p i ^ 2)⁻¹ • (EuclideanSpace.proj i : Space n →L[ℝ] ℝ)) p :=
      (hasDerivAt_inv hp).comp_hasFDerivAt p
        (EuclideanSpace.proj i : Space n →L[ℝ] ℝ).hasFDerivAt
    by_cases hj : j=i
    · subst j
      simp only [reciprocalChart,WithLp.ofLp_toLp,ite_true]
      rw [hi.fderiv]
      by_cases hk : k=i
      · subst k
        simp [Matrix.smul_apply,v,coordinateVector,pow_two,mul_inv_rev]
      · simp [Matrix.smul_apply,v,coordinateVector,hk,Ne.symm hk]
    · simp only [reciprocalChart,WithLp.ofLp_toLp,hj,ite_false,div_eq_mul_inv]
      have hmul := ((EuclideanSpace.proj j : Space n →L[ℝ] ℝ).hasFDerivAt.fun_mul hi).fderiv
      simp only [EuclideanSpace.coe_proj] at hmul
      rw [hmul]
      by_cases hk : k=i
      · subst k
        simp [Matrix.smul_apply,v,coordinateVector,hj,pow_two,div_eq_mul_inv]
        ring
      · by_cases hkj : k=j
        · subst k
          simp [Matrix.smul_apply,v,coordinateVector,hj,Ne.symm hj]
        · simp [Matrix.smul_apply,v,coordinateVector,hk,Ne.symm hk,Ne.symm hkj]
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix b,hm,Matrix.det_smul,
    det_updateCol_identity]
  simp only [Fintype.card_fin,v,ite_true,pow_succ,mul_neg]

end AffineBernstein
end

end OAI
