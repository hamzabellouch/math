import Mathlib
import OAI.Analysis.AffineBernstein.AffineFamily

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Matrix

lemma posDef_quadratic_linear_equiv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : ∃ L : Space n ≃ₗ[ℝ] Space n,
      ∀ x, (∑ i, (L x i)^2) = ∑ i, ∑ j, x i*A i j*x j := by
  open scoped MatrixOrder in
  classical
  let S := CFC.sqrt A
  have hS : S.IsSymm := Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hSS : S*S=A := by simpa only [S,pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hSd : IsUnit S.det := by
    apply isUnit_iff_ne_zero.mpr
    intro H
    have hd := congrArg Matrix.det hSS
    rw [Matrix.det_mul,H,zero_mul] at hd
    exact hA.det_pos.ne' hd.symm
  let L := Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis S hSd
  refine ⟨L,fun x => ?_⟩
  have hL : (fun i => L x i) = S*ᵥ (fun i => x i) := funext (matrixLinearEquiv_apply S hSd x)
  calc
    _ = (S*ᵥ (fun i => x i)) ⬝ᵥ (S*ᵥ (fun i => x i)) := by
      rw [← hL]
      simp only [dotProduct,pow_two]
    _ = (fun i => x i) ⬝ᵥ ((S*S)*ᵥ (fun i => x i)) := by
      rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,hS.eq]
      exact dotProduct_comm _ _
    _ = _ := by rw [hSS]; simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

def paraboloidLinearEquiv {n : ℕ} (L : Space n ≃ₗ[ℝ] Space n)
    (ℓ : Space n →L[ℝ] ℝ) : (Space n × ℝ) ≃ₗ[ℝ] (Space n × ℝ) where
  toFun p := (L.symm p.1,(1/2:ℝ)*p.2+ℓ (L.symm p.1))
  invFun p := (L p.1,2*(p.2-ℓ p.1))
  left_inv := by
    intro p
    apply Prod.ext
    · simp
    · ring
  right_inv := by
    intro p
    apply Prod.ext
    · simp
    · simp only [LinearEquiv.symm_apply_apply]
      ring
  map_add' := by
    intro p q
    apply Prod.ext
    · simp
    · simp only [Prod.fst_add,Prod.snd_add,map_add]
      ring
  map_smul' := by
    intro a p
    apply Prod.ext
    · simp
    · change (1/2:ℝ)*(a*p.2)+ℓ (L.symm (a • p.1)) = a*((1/2:ℝ)*p.2+ℓ (L.symm p.1))
      rw [map_smul,map_smul]
      simp only [smul_eq_mul]
      ring

lemma quadratic_graph_affine_image {n : ℕ} {u : Space n → ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (ℓ : Space n →L[ℝ] ℝ) (c : ℝ)
    (hu : ∀ x, u x=(1/2:ℝ)*(∑ i, ∑ j, x i*A i j*x j)+ℓ x+c) :
    ∃ e : (Space n × ℝ) ≃ᵃ[ℝ] (Space n × ℝ),
      e '' standardParaboloid n=graph univ u := by
  obtain ⟨L,hL⟩ := posDef_quadratic_linear_equiv hA
  let e := (paraboloidLinearEquiv L ℓ).toAffineEquiv.trans
    (AffineEquiv.constVAdd ℝ (Space n × ℝ) ((0:Space n),c))
  have he (p : Space n × ℝ) : e p=(L.symm p.1,(1/2:ℝ)*p.2+ℓ (L.symm p.1)+c) := by
    apply Prod.ext <;> simp [e,paraboloidLinearEquiv,add_comm]
  refine ⟨e,?_⟩
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    change q.2=∑ i, (q.1 i)^2 at hq
    rw [he]
    refine ⟨mem_univ _,?_⟩
    rw [hu,← hL,hq]
    simp
  · intro hp
    have hp' : p.2=u p.1 := hp.2
    refine ⟨(L p.1,∑ i, (L p.1 i)^2),rfl,?_⟩
    rw [he]
    apply Prod.ext
    · simp
    · simp only [LinearEquiv.symm_apply_apply]
      rw [hL,← hu,← hp']

end AffineBernstein

end

end OAI
