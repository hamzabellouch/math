import OAI.Analysis.LiebThirring.SpectralMain

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set
open scoped Topology ENNReal

lemma eigenBasis_nonempty {A : L2C →ₗ.[ℂ] L2C} (hA : IsSelfAdjoint A) {e : ℝ}
    {f : L2C} (hf : f ≠ 0) (he : IsOperatorEigenfunction A e f) :
    Nonempty (eigenBasisSet A hA e) := by
  classical
  by_contra h
  let : IsEmpty (eigenBasisSet A hA e) := ⟨fun i ↦ h ⟨i⟩⟩
  let u : eigenSpace A e := ⟨f,(mem_eigenSpace A e f).mpr he⟩
  have hz : (eigenBasis A hA e).repr u = 0 := by ext i; exact isEmptyElim i
  have hu : u = 0 := (eigenBasis A hA e).repr.injective (by simpa only [map_zero] using hz)
  exact hf (congrArg Subtype.val hu)

lemma oneEigenvalueMoment_eq_iSup (γ : ℝ) {A : L2C →ₗ.[ℂ] L2C} (hA : IsSelfAdjoint A) :
    oneEigenvalueMoment γ A = ⨆ i : EigenIndex A hA, (ENNReal.ofReal |i.1.1|)^γ := by
  classical
  apply le_antisymm
  · unfold oneEigenvalueMoment
    refine iSup_le (fun f ↦ iSup_le (fun e ↦ iSup_le (fun hf ↦ iSup_le (fun he ↦ ?_))))
    have hn : f ≠ 0 := by intro h; simp only [h,inner_zero_left,zero_ne_one] at hf
    obtain ⟨i⟩ := eigenBasis_nonempty hA hn he.2
    exact le_iSup_of_le (⟨⟨e,he.1⟩,i⟩ : EigenIndex A hA) le_rfl
  · refine iSup_le (fun i ↦ ?_)
    have hf : inner ℂ (eigenBasisVector A hA i) (eigenBasisVector A hA i) = 1 := by
      simpa using orthonormal_iff_ite.mp (eigenBasisVector_orthonormal A hA) i i
    exact le_iSup_of_le (eigenBasisVector A hA i) (le_iSup_of_le i.1.1
      (le_iSup_of_le hf (le_iSup_of_le ⟨i.1.2,eigenBasisVector_member A hA i⟩ le_rfl)))

lemma exists_max_weight {γ : ℝ} {A : L2C →ₗ.[ℂ] L2C} (hA : IsSelfAdjoint A)
    (hfin : eigenvalueSum γ A hA ≠ ∞) [Nonempty (EigenIndex A hA)] :
    ∃ i : EigenIndex A hA, ∀ j : EigenIndex A hA,
      (ENNReal.ofReal |j.1.1|)^γ ≤ (ENNReal.ofReal |i.1.1|)^γ := by
  classical
  let i₀ : EigenIndex A hA := Classical.choice inferInstance
  let w := fun i : EigenIndex A hA ↦ (ENNReal.ofReal |i.1.1|)^γ
  have hp : w i₀ ≠ 0 := ne_of_gt (ENNReal.rpow_pos
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr (ne_of_lt i₀.1.2))) ENNReal.ofReal_ne_top)
  have hs : {i : EigenIndex A hA | w i₀ ≤ w i}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top hfin hp
  obtain ⟨i,hi,hmax⟩ := Set.exists_max_image _ w hs ⟨i₀,show w i₀ ≤ w i₀ from le_rfl⟩
  refine ⟨i,fun j ↦ ?_⟩
  by_cases hj : w i₀ ≤ w j
  · exact hmax j hj
  · exact (le_of_lt (not_le.mp hj)).trans hi

/-- If there is a negative eigenvalue, retaining one state means precisely the
lowest negative eigenvalue, not an assumed minimizer or a finite spectral cutoff. -/
theorem one_state_is_lowest {γ : ℝ} (hγ : 0 < γ) {A : L2C →ₗ.[ℂ] L2C}
    (hA : IsSelfAdjoint A) (hfin : eigenvalueSum γ A hA ≠ ∞)
    (hex : ∃ (e : ℝ) (f : L2C), e < 0 ∧ f ≠ 0 ∧ IsOperatorEigenfunction A e f) :
    ∃ (e : ℝ) (f : L2C), e < 0 ∧ inner ℂ f f = 1 ∧
      IsOperatorEigenfunction A e f ∧
      oneEigenvalueMoment γ A = (ENNReal.ofReal |e|)^γ ∧
      ∀ (t : ℝ) (g : L2C), t < 0 → g ≠ 0 → IsOperatorEigenfunction A t g → e ≤ t := by
  classical
  obtain ⟨e₀,f₀,he₀,hf₀,ha₀⟩ := hex
  obtain ⟨i₀⟩ := eigenBasis_nonempty hA hf₀ ha₀
  let : Nonempty (EigenIndex A hA) := ⟨⟨⟨e₀,he₀⟩,i₀⟩⟩
  obtain ⟨i,hi⟩ := exists_max_weight hA hfin
  refine ⟨i.1.1,eigenBasisVector A hA i,i.1.2,?_,eigenBasisVector_member A hA i,?_,?_⟩
  · simpa using orthonormal_iff_ite.mp (eigenBasisVector_orthonormal A hA) i i
  · rw [oneEigenvalueMoment_eq_iSup γ hA]
    exact le_antisymm (iSup_le hi) (le_iSup (fun j : EigenIndex A hA ↦ (ENNReal.ofReal |j.1.1|)^γ) i)
  · intro t g ht hg ha
    obtain ⟨j⟩ := eigenBasis_nonempty hA hg ha
    have h := (ENNReal.rpow_le_rpow_iff hγ).mp (hi ⟨⟨t,ht⟩,j⟩)
    have hab : |t| ≤ |i.1.1| := (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).mp h
    rw [abs_of_neg ht,abs_of_neg i.1.2] at hab
    linarith

end SharpLiebThirring.OperatorProof

end

end OAI
