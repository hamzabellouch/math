import OAI.Geometry.Perimeter.Regularity.EllipticCurl

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem inner_fderiv_gradient {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (x a b : Euc n) :
    inner ℝ (fderiv ℝ (gradient φ) x a) b=fderiv ℝ (fderiv ℝ φ) x a b := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have he : fderiv ℝ (gradient φ) x=
      (InnerProductSpace.toDual ℝ (Euc n)).symm.toContinuousLinearMap.comp
        (fderiv ℝ (fderiv ℝ φ) x) := by
    exact (((InnerProductSpace.toDual ℝ (Euc n)).symm.toContinuousLinearMap).hasFDerivAt.comp x
      (hd.differentiable (by simp) x).hasFDerivAt).fderiv
  rw [he]
  change inner ℝ ((InnerProductSpace.toDual ℝ (Euc n)).symm (fderiv ℝ (fderiv ℝ φ) x a)) b=_
  exact InnerProductSpace.toDual_symm_apply

theorem gradient_scalarDirection {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (x a : Euc n) : gradient (scalarDirection φ a) x=fderiv ℝ (gradient φ) x a := by
  apply ext_inner_right ℝ
  intro b
  rw [inner_gradient_left,scalarDirection_fderiv hφ,inner_fderiv_gradient hφ]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) b a

theorem laplacian_scalarDirection_sum {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (x : Euc n) :
    divergence (gradient φ) x=∑ j : Fin n, scalarDirection (scalarDirection φ
      ((EuclideanSpace.basisFun (Fin n) ℝ) j)) ((EuclideanSpace.basisFun (Fin n) ℝ) j) x := by
  unfold divergence
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm,inner_fderiv_gradient hφ]
  symm
  exact scalarDirection_fderiv hφ _ _ _

theorem div_curl_test_identity {φ : Euc n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (a x : Euc n) :
    divergence (gradient φ) x • a=gradient (scalarDirection φ a) x+
      ∑ j : Fin n, curlTest (scalarDirection φ ((EuclideanSpace.basisFun (Fin n) ℝ) j))
        ((EuclideanSpace.basisFun (Fin n) ℝ) j) a x := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hs : (∑ j : Fin n, scalarDirection (scalarDirection φ (b j)) a x • b j)=
      gradient (scalarDirection φ a) x := by
    calc
      _ = ∑ j : Fin n, inner ℝ (b j) (gradient (scalarDirection φ a) x) • b j := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        rw [real_inner_comm,inner_gradient_left]
        change fderiv ℝ (scalarDirection φ (b j)) x a=fderiv ℝ (scalarDirection φ a) x (b j)
        rw [scalarDirection_fderiv hφ,scalarDirection_fderiv hφ]
        exact (hφ.contDiffAt.isSymmSndFDerivAt (by
          simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) a (b j)
      _ = _ := by simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_repr (gradient (scalarDirection φ a) x)
  change divergence (gradient φ) x • a=gradient (scalarDirection φ a) x+
    ∑ j : Fin n, curlTest (scalarDirection φ (b j)) (b j) a x
  simp only [curlTest,Finset.sum_sub_distrib,←Finset.sum_smul,hs]
  rw [show (∑ j : Fin n, scalarDirection (scalarDirection φ (b j)) (b j) x)=
    divergence (gradient φ) x from (laplacian_scalarDirection_sum hφ x).symm]
  abel

end RPISingularHarnack

end

end OAI
