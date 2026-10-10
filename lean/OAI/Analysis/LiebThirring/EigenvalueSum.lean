import OAI.Analysis.LiebThirring.Eigenspace

namespace OAI

universe u187 u188


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set
open scoped Topology ENNReal

lemma finite_family_le_moment {ι : Type u187} [Fintype ι] {γ : ℝ}
    {A : L2C →ₗ.[ℂ] L2C} (f : ι → L2C) (e : ι → ℝ)
    (hf : Orthonormal ℂ f)
    (he : ∀ i, e i < 0 ∧ IsOperatorEigenfunction A (e i) (f i)) :
    (∑ i, (ENNReal.ofReal |e i|)^γ) ≤ eigenvalueMoment γ A := by
  classical
  let q := (Fintype.equivFin ι).symm
  have h : (∑ i : Fin (Fintype.card ι), (ENNReal.ofReal |e (q i)|)^γ) ≤
      eigenvalueMoment γ A :=
    le_iSup_of_le _ (le_iSup_of_le (f ∘ q) (le_iSup_of_le (e ∘ q)
      (le_iSup_of_le (hf.comp q q.injective) (le_iSup_of_le (fun i ↦ he (q i)) le_rfl))))
  rw [Equiv.sum_comp q (fun i ↦ (ENNReal.ofReal |e i|)^γ)] at h
  exact h

lemma eigenvalueSum_le_moment (γ : ℝ) (A : L2C →ₗ.[ℂ] L2C) (hA : IsSelfAdjoint A) :
    eigenvalueSum γ A hA ≤ eigenvalueMoment γ A := by
  classical
  unfold eigenvalueSum
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le (fun s ↦ ?_)
  have h := finite_family_le_moment (γ:=γ)
    (fun i : s ↦ eigenBasisVector A hA i.1) (fun i : s ↦ i.1.1.1)
    ((eigenBasisVector_orthonormal A hA).comp Subtype.val Subtype.val_injective)
    (fun i ↦ ⟨i.1.1.2,eigenBasisVector_member A hA i.1⟩)
  rw [← Finset.sum_coe_sort s (fun i : EigenIndex A hA ↦ (ENNReal.ofReal |i.1.1|)^γ)]
  exact h

lemma eigenBasis_finite {γ : ℝ} {A : L2C →ₗ.[ℂ] L2C} (hA : IsSelfAdjoint A)
    (hfin : eigenvalueSum γ A hA ≠ ∞) (e : NegativeEnergy) :
    Finite (eigenBasisSet A hA e.1) := by
  classical
  by_contra h
  let : Infinite (eigenBasisSet A hA e.1) := not_finite_iff_infinite.mp h
  have hp : ENNReal.ofReal |e.1| ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (abs_pos.mpr (ne_of_lt e.2)))
  have hp' : (ENNReal.ofReal |e.1|)^γ ≠ 0 :=
    ne_of_gt (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hp) ENNReal.ofReal_ne_top)
  have hle := ENNReal.tsum_comp_le_tsum_of_injective
    (show Function.Injective (fun i : eigenBasisSet A hA e.1 ↦ (⟨e,i⟩ : EigenIndex A hA)) from
      fun i j h ↦ by cases h; rfl) (fun i : EigenIndex A hA ↦ (ENNReal.ofReal |i.1.1|)^γ)
  have ht : (∑' _ : eigenBasisSet A hA e.1, (ENNReal.ofReal |e.1|)^γ) = ∞ :=
    ENNReal.tsum_const_eq_top_of_ne_zero hp'
  rw [ht] at hle
  exact hfin (top_le_iff.mp hle)

lemma eigenSpace_finiteDimensional {γ : ℝ} {A : L2C →ₗ.[ℂ] L2C}
    (hA : IsSelfAdjoint A) (hfin : eigenvalueSum γ A hA ≠ ∞) (e : NegativeEnergy) :
    FiniteDimensional ℂ (eigenSpace A e.1) := by
  let := eigenBasis_finite hA hfin e
  let := Fintype.ofFinite (eigenBasisSet A hA e.1)
  exact Module.Finite.of_basis (eigenBasis A hA e.1).toOrthonormalBasis.toBasis


lemma finite_family_le_sum {ι : Type u188} [Fintype ι] {γ : ℝ}
    {A : L2C →ₗ.[ℂ] L2C} (hA : IsSelfAdjoint A)
    (hfin : eigenvalueSum γ A hA ≠ ∞)
    (f : ι → L2C) (e : ι → ℝ) (hf : Orthonormal ℂ f)
    (he : ∀ i, e i < 0 ∧ IsOperatorEigenfunction A (e i) (f i)) :
    (∑ i, (ENNReal.ofReal |e i|)^γ) ≤ eigenvalueSum γ A hA := by
  classical
  let E : ι → NegativeEnergy := fun i ↦ ⟨e i,(he i).1⟩
  have hlocal : ∀ t : NegativeEnergy,
      (∑' i : E ⁻¹' {t}, (ENNReal.ofReal |e i.1|)^γ) ≤
        ∑' _ : eigenBasisSet A hA t.1, (ENNReal.ofReal |t.1|)^γ := by
    intro t
    let := eigenBasis_finite hA hfin t
    let := Fintype.ofFinite (eigenBasisSet A hA t.1)
    let := eigenSpace_finiteDimensional hA hfin t
    have heq (i : E ⁻¹' {t}) : e i.1 = t.1 := congrArg Subtype.val i.2
    let v : (E ⁻¹' {t}) → eigenSpace A t.1 := fun i ↦
      ⟨f i.1,(mem_eigenSpace A t.1 _).mpr (by rw [← heq i]; exact (he i.1).2)⟩
    have hv : Orthonormal ℂ v := by
      apply orthonormal_iff_ite.mpr
      intro i j
      change inner ℂ (f i.1) (f j.1) = _
      simpa only [Subtype.val_inj] using orthonormal_iff_ite.mp hf i.1 j.1
    have hc := hv.linearIndependent.fintype_card_le_finrank
    rw [Module.finrank_eq_card_basis (eigenBasis A hA t.1).toOrthonormalBasis.toBasis] at hc
    calc
      _ = (Fintype.card (E ⁻¹' {t}) : ℝ≥0∞) * (ENNReal.ofReal |t.1|)^γ := by
        simp only [heq,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ ≤ (Fintype.card (eigenBasisSet A hA t.1) : ℝ≥0∞) * (ENNReal.ofReal |t.1|)^γ :=
        mul_le_mul_left (by exact_mod_cast hc) _
      _ = _ := by simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  calc
    _ = ∑' t : NegativeEnergy, ∑' i : E ⁻¹' {t}, (ENNReal.ofReal |e i.1|)^γ := by
      rw [ENNReal.tsum_fiberwise (fun i ↦ (ENNReal.ofReal |e i|)^γ) E,tsum_fintype]
    _ ≤ ∑' t : NegativeEnergy, ∑' _ : eigenBasisSet A hA t.1,
        (ENNReal.ofReal |t.1|)^γ := ENNReal.tsum_le_tsum hlocal
    _ = eigenvalueSum γ A hA := (ENNReal.tsum_sigma _).symm

lemma eigenvalueMoment_eq_sum {γ : ℝ} {A : L2C →ₗ.[ℂ] L2C} (hA : IsSelfAdjoint A)
    (hfin : eigenvalueSum γ A hA ≠ ∞) :
    eigenvalueMoment γ A = eigenvalueSum γ A hA := by
  apply le_antisymm
  · unfold eigenvalueMoment
    refine iSup_le (fun N ↦ iSup_le (fun f ↦ iSup_le (fun e ↦
      iSup_le (fun hf ↦ iSup_le (fun he ↦ ?_)))))
    exact finite_family_le_sum hA hfin f e hf he
  · exact eigenvalueSum_le_moment γ A hA

end SharpLiebThirring.OperatorProof

end

end OAI
