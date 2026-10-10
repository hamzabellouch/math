import Mathlib
import OAI.Probability.SKValue.GroundState.GaussianColumn

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set InnerProductSpace
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace
namespace SKValueG
variable {κ : Type*} [Fintype κ]

lemma unitOrZero_norm_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : E} (hv : v=0 ∨ ⟪v,v⟫=1) : ‖v‖≤1 := by
  rcases hv with rfl|hv
  · simp
  · rw [real_inner_self_eq_norm_sq] at hv
    nlinarith [norm_nonneg v]

lemma columnResidual_norm_le {v : EuclideanSpace ℝ κ}
    (hv : v=0 ∨ ⟪v,v⟫=1) (w : EuclideanSpace ℝ κ) :
    ‖columnResidual v w‖≤‖w‖ := by
  rcases hv with rfl|hv
  · simp [columnResidual]
  · have he := columnResidual_inner hv w w
    simp only [real_inner_self_eq_norm_sq] at he
    nlinarith [norm_nonneg w,norm_nonneg (columnResidual v w),sq_nonneg ⟪v,w⟫]

lemma columnVector_norm_le {v : EuclideanSpace ℝ κ}
    (hv : v=0 ∨ ⟪v,v⟫=1) (w : EuclideanSpace ℝ κ) :
    ‖columnVector v w‖≤‖w‖^2 := by
  have he := columnSplitCoeff_inner hv w w
  rw [Fintype.sum_sum_type] at he
  simp only [columnSplitCoeff,Sum.elim_inl,Sum.elim_inr] at he
  rw [←euclidean_inner_sum,quadraticCoeff_inner,quadraticCoeff_inner] at he
  simp only [real_inner_self_eq_norm_sq] at he
  have hn : 0≤‖columnVector v w‖ := norm_nonneg _
  have hp := sq_nonneg (‖columnResidual v w‖^2)
  have hw := sq_nonneg (‖w‖^2)
  exact (sq_le_sq₀ hn (sq_nonneg _)).mp (by nlinarith)

lemma columnLinear_bound {v : EuclideanSpace ℝ κ}
    (hv : v=0 ∨ ⟪v,v⟫=1) (w : EuclideanSpace ℝ κ) (z : κ → ℝ) :
    |(∑ k,columnVector v w k*z k)|≤‖w‖^2*‖WithLp.toLp 2 z‖ := by
  have he : (∑ k,columnVector v w k*z k)=⟪columnVector v w,WithLp.toLp 2 z⟫ :=
    (euclidean_inner_sum _ _).symm
  rw [he]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (columnVector_norm_le hv w) (norm_nonneg _))

lemma quadraticCoeff_coord_bound (w : EuclideanSpace ℝ κ) (k : κ×κ) :
    |quadraticCoeff w k|≤‖w‖^2 := by
  have h1 : |w k.1|≤‖w‖ := PiLp.norm_apply_le w k.1
  have h2 : |w k.2|≤‖w‖ := PiLp.norm_apply_le w k.2
  have hs : 1≤Real.sqrt 2 := by norm_num
  rw [quadraticCoeff,abs_div,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
  calc
    _ ≤ ‖w‖*‖w‖ := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    _ = ‖w‖^2 := by ring
    _ ≤ ‖w‖^2*Real.sqrt 2 := le_mul_of_one_le_right (sq_nonneg _) hs

lemma measurable_columnResidual {Ω : Type*} [MeasurableSpace Ω]
    {v w : Ω → EuclideanSpace ℝ κ} (hv : Measurable v) (hw : Measurable w) :
    Measurable (fun ω ↦ columnResidual (v ω) (w ω)) := by
  unfold columnResidual
  fun_prop

lemma measurable_columnVector {Ω : Type*} [MeasurableSpace Ω]
    {v w : Ω → EuclideanSpace ℝ κ} (hv : Measurable v) (hw : Measurable w) :
    Measurable (fun ω ↦ columnVector (v ω) (w ω)) := by
  unfold columnVector
  have hi : Measurable (fun ω ↦ (⟪v ω,w ω⟫ : ℝ)) := hv.inner hw
  exact (hi.smul (measurable_columnResidual hv hw)).add
    ((hi.pow_const 2 |>.div_const _).smul hv)

lemma gramSchmidt_eq_sub_sum_nat {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℕ → E) (j : ℕ) :
    gramSchmidt ℝ f j=f j-∑ i∈Finset.range j,
      (⟪gramSchmidt ℝ f i,f j⟫/‖gramSchmidt ℝ f i‖^2) • gramSchmidt ℝ f i := by
  have he := gramSchmidt_def'' ℝ f j
  simp only [Nat.Iio_eq_range] at he
  exact eq_sub_iff_add_eq.mpr he.symm

lemma measurable_gramSchmidt {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (f : Ω → ℕ → E) (hf : ∀ j,Measurable (fun ω ↦ f ω j))
    (j : ℕ) : Measurable (fun ω ↦ gramSchmidt ℝ (f ω) j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    simp_rw [show (fun ω ↦ gramSchmidt ℝ (f ω) j) =
      (fun ω ↦ f ω j-∑ i∈Finset.range j,
        (⟪gramSchmidt ℝ (f ω) i,f ω j⟫/‖gramSchmidt ℝ (f ω) i‖^2) •
          gramSchmidt ℝ (f ω) i) from funext (fun ω ↦ gramSchmidt_eq_sub_sum_nat (f ω) j)]
    apply (hf j).sub
    apply Finset.measurable_sum
    intro i hi
    have hg := ih i (Finset.mem_range.mp hi)
    exact ((hg.inner (hf j)).div (hg.norm.pow_const 2)).smul hg

lemma measurable_gramSchmidtNormed {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (f : Ω → ℕ → E) (hf : ∀ j,Measurable (fun ω ↦ f ω j))
    (j : ℕ) : Measurable (fun ω ↦ gramSchmidtNormed ℝ (f ω) j) := by
  have hg := measurable_gramSchmidt f hf j
  change Measurable (fun ω ↦ ‖gramSchmidt ℝ (f ω) j‖⁻¹ • gramSchmidt ℝ (f ω) j)
  exact hg.norm.inv.smul hg

lemma gramSchmidtNormed_unitOrZero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℕ → E) (j : ℕ) :
    gramSchmidtNormed ℝ f j=0 ∨ ⟪gramSchmidtNormed ℝ f j,gramSchmidtNormed ℝ f j⟫=1 := by
  by_cases h : gramSchmidtNormed ℝ f j=0
  · exact Or.inl h
  · right
    rw [real_inner_self_eq_norm_sq,gramSchmidtNormed_unit_length' h]
    norm_num

lemma gramSchmidtNormed_pairwise_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℕ → E) {i j : ℕ} (hij : i≠j) :
    ⟪gramSchmidtNormed ℝ f i,gramSchmidtNormed ℝ f j⟫=0 := by
  simp only [gramSchmidtNormed,real_inner_smul_left,real_inner_smul_right,
    gramSchmidt_orthogonal ℝ f hij,mul_zero]

end SKValueG

end

end OAI
