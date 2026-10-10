import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.EigenOrder
import OAI.Analysis.BiholderTransport.LinearAlgebra.CompactConorm

namespace OAI

section
section
noncomputable section
open Module

namespace WeakMTWTransport
section NormDetCoercivity
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

lemma singularValue_le_of_conorm_det (A : E →ₗ[ℝ] F) {b K : ℝ} (hb : 0<b)
    (hA : ∀ v,b*‖v‖≤‖A v‖) (hK : A.normDet≤K) (i : Fin (finrank ℝ E)) :
    A.singularValues i≤K/b^(finrank ℝ E-1) := by
  classical
  have H : ∀ j : Fin (finrank ℝ E),b≤A.singularValues j := by
    intro j
    have H := hA (A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl j)
    rw [(A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).norm_eq_one,mul_one,
      norm_eigenvector_image_eq_singularValue] at H
    exact H
  have hp := Finset.prod_le_prod₀ (s := Finset.univ.erase i)
    (fun _ _ => hb.le) (fun index _ => H index)
  have hp' : b^(finrank ℝ E-1)≤∏ j∈Finset.univ.erase i,A.singularValues j := by
    simpa only [Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ,Fintype.card_fin] using hp
  apply (le_div_iff₀ (pow_pos hb _)).mpr
  calc
    A.singularValues i*b^(finrank ℝ E-1) ≤
        A.singularValues i*(∏ j∈Finset.univ.erase i,A.singularValues j) :=
      mul_le_mul_of_nonneg_left hp' (A.singularValues_nonneg i)
    _ = A.normDet := by
      rw [A.normDet_eq_prod_singularValues,←Fin.prod_univ_eq_prod_range]
      exact Finset.mul_prod_erase Finset.univ (fun j : Fin (finrank ℝ E) => A.singularValues j) (Finset.mem_univ i)
    _ ≤ K := hK

lemma norm_le_of_conorm_det (A : E →ₗ[ℝ] F) {b K : ℝ} (hb : 0<b)
    (hA : ∀ v,b*‖v‖≤‖A v‖) (hK : A.normDet≤K) (v : E) :
    ‖A v‖≤((finrank ℝ E:ℝ)*K/b^(finrank ℝ E-1))*‖v‖ := by
  classical
  let e := A.isSymmetric_adjoint_comp_self.eigenvectorBasis (rfl : finrank ℝ E=finrank ℝ E)
  have hσ := singularValue_le_of_conorm_det A hb hA hK
  have hK0 : 0≤K := A.normDet_nonneg.trans hK
  have hC : 0≤K/b^(finrank ℝ E-1) := div_nonneg hK0 (pow_pos hb _).le
  calc
    ‖A v‖ = ‖∑ j : Fin (finrank ℝ E), e.repr v j • A (e j)‖ := by
      simp_rw [←map_smul]
      rw [←map_sum,e.sum_repr]
    _ ≤ ∑ j : Fin (finrank ℝ E),‖e.repr v j • A (e j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin (finrank ℝ E),(K/b^(finrank ℝ E-1))*‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul,norm_eigenvector_image_eq_singularValue]
      have he : ‖e.repr v j‖≤‖v‖ := by
        rw [e.repr_apply_apply]
        simpa only [e.norm_eq_one,mul_one,one_mul] using (norm_inner_le_norm (e j) v)
      calc
        ‖e.repr v j‖*A.singularValues j ≤ ‖v‖*(K/b^(finrank ℝ E-1)) :=
          mul_le_mul he (hσ j) (A.singularValues_nonneg j) (norm_nonneg v)
        _ = _ := mul_comm _ _
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end NormDetCoercivity
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section CoerciveBilinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma bilinearOperator_conorm {W : E →L[ℝ] E →L[ℝ] ℝ} {m : ℝ}
    (hW : ∀ d:E,m*‖d‖^2≤W d d) (d : E) : m*‖d‖≤‖bilinearOperator W d‖ := by
  by_cases hd : d=0
  · simp [hd]
  apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hd)).mp
  calc
    (m*‖d‖)*‖d‖=m*‖d‖^2 := by ring
    _ ≤ W d d := hW d
    _ = inner ℝ (bilinearOperator W d) d := (bilinearOperator_inner W d d).symm
    _ ≤ ‖bilinearOperator W d‖*‖d‖ := real_inner_le_norm _ _

lemma bilinear_quadratic_bound_of_det {W : E →L[ℝ] E →L[ℝ] ℝ} {m K : ℝ}
    (hm : 0 < m) (hW : ∀ d:E,m*‖d‖^2≤W d d)
    (hK : |(bilinearOperator W).det|≤K) (d : E) :
    W d d≤((finrank ℝ E:ℝ)*K/m^(finrank ℝ E-1))*‖d‖^2 := by
  have hK' : (bilinearOperator W).toLinearMap.normDet≤K := by
    rwa [LinearMap.normDet_eq_abs_det]
  have H := norm_le_of_conorm_det (bilinearOperator W).toLinearMap hm
    (bilinearOperator_conorm hW) hK' d
  calc
    W d d = inner ℝ (bilinearOperator W d) d := (bilinearOperator_inner W d d).symm
    _ ≤ ‖bilinearOperator W d‖*‖d‖ := real_inner_le_norm _ _
    _ ≤ (((finrank ℝ E:ℝ)*K/m^(finrank ℝ E-1))*‖d‖)*‖d‖ :=
      mul_le_mul_of_nonneg_right H (norm_nonneg d)
    _ = _ := by ring
end CoerciveBilinear

end WeakMTWTransport
end
end
end

end OAI
