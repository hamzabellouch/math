import Mathlib

namespace OAI

section
section
noncomputable section
open Module Set
open scoped BigOperators

namespace WeakMTWTransport

lemma matrix_norm_det_le_factorial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) {R : ℝ} (hR : 0≤R) (hA : ∀ i j, ‖A i j‖≤R) :
    ‖A.det‖≤(Fintype.card ι).factorial*R^(Fintype.card ι) := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, R^(Fintype.card ι) := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [norm_units_zsmul,norm_prod]
      calc
        _ ≤ ∏ _i : ι, |R| := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun index _ => (hA (σ index) index).trans (le_abs_self R))
        _ = _ := by simp [abs_of_nonneg hR]
    _ = _ := by simp [Fintype.card_perm]

lemma normDet_le_factorial_opNorm {U V : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (F : U →L[ℝ] V) (hd : Module.finrank ℝ U=Module.finrank ℝ V) :
    F.toLinearMap.normDet≤(Module.finrank ℝ U).factorial*‖F‖^(Module.finrank ℝ U) := by
  classical
  let b := stdOrthonormalBasis ℝ U
  let d : OrthonormalBasis (Fin (finrank ℝ U)) ℝ V :=
    (stdOrthonormalBasis ℝ V).reindex (finCongr hd).symm
  rw [LinearMap.normDet_eq_norm_det_toMatrix F.toLinearMap b d]
  have hA : ∀ i j, ‖(F.toLinearMap.toMatrix b.toBasis d.toBasis) i j‖≤‖F‖ := by
    intro i j
    rw [LinearMap.toMatrix_apply,d.coe_toBasis_repr_apply]
    change ‖d.repr (F (b j)) i‖≤‖F‖
    rw [d.repr_apply_apply]
    calc
      _ ≤ ‖d i‖*‖F (b j)‖ := norm_inner_le_norm _ _
      _ = ‖F (b j)‖ := by rw [d.orthonormal.norm_eq_one i,one_mul]
      _ ≤ ‖F‖*‖b j‖ := F.le_opNorm _
      _ = ‖F‖ := by rw [b.orthonormal.norm_eq_one,mul_one]
  simpa only [Fintype.card_fin] using matrix_norm_det_le_factorial
    (F.toLinearMap.toMatrix b.toBasis d.toBasis) (norm_nonneg F) hA

lemma normDet_comp_three {U V W Z : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
    (R : U →L[ℝ] V) (A : V →L[ℝ] W) (S : W →L[ℝ] Z)
    (hUV : finrank ℝ U=finrank ℝ V) (hVW : finrank ℝ V=finrank ℝ W) :
    (S.comp (A.comp R)).toLinearMap.normDet=
      S.toLinearMap.normDet*A.toLinearMap.normDet*R.toLinearMap.normDet := by
  change (S.toLinearMap ∘ₗ (A.toLinearMap ∘ₗ R.toLinearMap)).normDet=_
  rw [LinearMap.normDet_comp_of_finrank_eq _ _ (hUV.trans hVW),
    LinearMap.normDet_comp_of_finrank_eq _ _ hUV,mul_assoc]

end WeakMTWTransport

end

end

end

end OAI
