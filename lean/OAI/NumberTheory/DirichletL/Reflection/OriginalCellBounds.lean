import OAI.NumberTheory.DirichletL.Reflection.RowReindex
import OAI.NumberTheory.DirichletL.Reflection.TupleDyads

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma original_residual_norm_bounds (rows : Finset (Ideal Eis)) (J Q : Ideal Eis)
    (hbad : ∀ P∈fixedBadPrimes,P∣Q) (U : ℝ)
    (hrows : ∀ I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) :
    ∀ K∈originalResidualRows rows J Q,
      1≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤
        U/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ)) := by
  intro K hK
  have hr := originalResidualRows_range rows J Q hbad U hrows K hK
  exact ⟨QuadraticMainBoundary.norm_one_le hr.1.1,hr.2⟩

theorem original_residual_cell_representative (rows : Finset (Ideal Eis)) (J Q : Ideal Eis)
    (hbad : ∀ P∈fixedBadPrimes,P∣Q) (U : ℝ)
    (hrows : ∀ I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U)
    (H : ℝ) (hH : H=U/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ)))
    (i : Fin (columnDyadicLength H+1))
    (hi : (divisorDyadicBin (originalResidualRows rows J Q) H i).Nonempty) :
    ∃ I∈rows,I≠0 ∧ rowPowerfulPart J=rowPowerfulPart I ∧ rowMaskPart J Q=rowMaskPart I Q ∧
      (Ideal.absNorm I:ℝ)≤U ∧
      divisorDyadicScale i.val≤(Ideal.absNorm (rowResidualPart I Q):ℝ) ∧
      (Ideal.absNorm (rowResidualPart I Q):ℝ)≤2*divisorDyadicScale i.val := by
  obtain ⟨K,hK⟩ := hi
  have hKT := (Finset.mem_filter.mp hK).1
  have hr := originalResidualRows_reconstruct rows J Q (fun I hI => (hrows I hI).1) K hKT
  obtain ⟨hI,hp,hm⟩ := Finset.mem_filter.mp hr.1
  refine ⟨reconstructFiberRow J Q K,hI,(hrows _ hI).1,hp.symm,hm.symm,(hrows _ hI).2,?_⟩
  rw [hr.2]
  apply divisorDyadicBin_bounds _ H _ i K hK
  intro D hD
  rw [hH]
  exact original_residual_norm_bounds rows J Q hbad U hrows D hD

lemma original_residual_cell_scale_cap (rows : Finset (Ideal Eis)) (J Q : Ideal Eis)
    (hbad : ∀ P∈fixedBadPrimes,P∣Q) (U H Z L : ℝ)
    (hrows : ∀ I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U)
    (hH : H=U/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ)))
    (hZ : 2≤Z) (hcap : H≤Z^L)
    (i : Fin (columnDyadicLength H+1))
    (hi : (divisorDyadicBin (originalResidualRows rows J Q) H i).Nonempty) :
    1≤2*divisorDyadicScale i.val ∧ 2*divisorDyadicScale i.val≤Z^(L+1) := by
  have hz : 0<Z := by linarith
  have hs := divisorDyadicScale_ge_one i.val
  have hh : divisorDyadicScale i.val≤H := by
    apply divisorDyadicBin_scale_le _ H _ i hi
    intro D hD
    rw [hH]
    exact original_residual_norm_bounds rows J Q hbad U hrows D hD
  refine ⟨by linarith,?_⟩
  calc
    _ ≤ Z*Z^L := mul_le_mul hZ (hh.trans hcap) (by linarith) hz.le
    _ = _ := by rw [Real.rpow_add hz,Real.rpow_one];ring

lemma dyadic_canonical_lower (Z QK : ℝ) (hZ : 1<Z) (hQK : 0<QK)
    (K : Ideal Eis) (hK : QK/2≤(Ideal.absNorm K:ℝ)) :
    Z^(Real.logb Z QK)/2≤(Ideal.absNorm K:ℝ) := by
  rw [Real.rpow_logb (lt_trans zero_lt_one hZ) (ne_of_gt hZ) hQK]
  exact hK

end
end SevenEighths.InverseReflectedPhase

end OAI
