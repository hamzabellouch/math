import OAI.NumberTheory.CubicMoment.Estimates.IndependentMellin

namespace OAI

/-! The high-coordinate tail of the genuine product Mellin weight is bounded
by its explicit finite sum of coordinate moments. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mellinHeightBox (T : ℝ) : Set (ι → ℝ) := {τ | ∀ i, |τ i| ≤ T}

def mellinHeightPower (A : ℕ) (τ : ι → ℝ) : ℝ := ∑ i, |τ i|^A

omit [DecidableEq ι] in
lemma measurableSet_mellinHeightBox (T : ℝ) : MeasurableSet (mellinHeightBox (ι := ι) T) := by
  have he : mellinHeightBox (ι := ι) T = ⋂ i, {τ : ι → ℝ | |τ i| ≤ T} := by
    ext τ
    simp [mellinHeightBox]
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_le (measurable_pi_apply i).abs measurable_const)

omit [DecidableEq ι] in
lemma mellinHeightPower_nonneg (A : ℕ) (τ : ι → ℝ) : 0 ≤ mellinHeightPower A τ :=
  Finset.sum_nonneg (fun i _ => pow_nonneg (abs_nonneg (τ i)) A)

omit [DecidableEq ι] in
lemma mellinHeightPower_large {T : ℝ} (hT : 0 ≤ T) (A : ℕ) {τ : ι → ℝ}
    (hτ : τ ∈ (mellinHeightBox T)ᶜ) : T^A ≤ mellinHeightPower A τ := by
  have h : ∃ i, T < |τ i| := by
    simpa only [mellinHeightBox,mem_compl_iff,mem_ofPred_eq,not_forall,not_le] using hτ
  obtain ⟨i,hi⟩ := h
  exact (pow_le_pow_left₀ hT hi.le A).trans
    (Finset.single_le_sum (fun j _ => pow_nonneg (abs_nonneg (τ j)) A) (Finset.mem_univ i))

omit [DecidableEq ι] in
theorem multivariate_weighted_tail (w : (ι → ℝ) → ℂ) (hw : Integrable w)
    (A : ℕ) (hA : Integrable (fun τ => mellinHeightPower A τ*‖w τ‖))
    {T : ℝ} (hT : 0 < T) :
    (∫ τ in (mellinHeightBox T)ᶜ, ‖w τ‖) ≤
      (∫ τ : ι → ℝ, mellinHeightPower A τ*‖w τ‖)/T^A := by
  apply (le_div_iff₀ (pow_pos hT A)).mpr
  rw [mul_comm,← integral_const_mul]
  apply (integral_mono_ae (hw.norm.restrict.const_mul _) hA.restrict ?_).trans
    (setIntegral_le_integral hA (Filter.Eventually.of_forall
      (fun τ => mul_nonneg (mellinHeightPower_nonneg A τ) (_root_.norm_nonneg _))))
  filter_upwards [ae_restrict_mem (measurableSet_mellinHeightBox T).compl] with τ hτ
  exact mul_le_mul_of_nonneg_right (mellinHeightPower_large hT.le A hτ) (_root_.norm_nonneg _)

lemma prod_one_coordinate (f : ι → ℝ) (i : ι) (c : ℝ) :
    (∏ j, if j=i then c*f j else f j) = c*∏ j, f j := by
  classical
  have he (j : ι) : (if j=i then c*f j else f j) = (if j=i then c else 1)*f j := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp

lemma independentMellinWeight_coordinate_moment_integrable
    (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ) (i : ι) :
    Integrable (fun τ : ι → ℝ => |τ i|^A*‖independentMellinWeight W X τ‖) := by
  have hh (j : ι) : Integrable (fun t : ℝ =>
      if j=i then |t|^A*‖zeroLineMellinWeight (W j) (X j) t‖ else
        ‖zeroLineMellinWeight (W j) (X j) t‖) := by
    by_cases hj : j=i
    · simp only [hj,ite_true]
      exact zeroLineMellinWeight_moment_integrable (W i) (hW i) (hpos i) (hsm i) (hX i) A
    · simp only [hj,ite_false]
      exact (zeroLineMellinWeight_integrable (W j) (hW j) (hpos j) (hsm j) (hX j)).norm
  have hp := Integrable.fintype_prod hh
  convert hp using 1
  funext τ
  rw [independentMellinWeight,norm_prod]
  symm
  convert prod_one_coordinate (fun j => ‖zeroLineMellinWeight (W j) (X j) (τ j)‖) i (|τ i|^A) using 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j=i <;> simp [hj]

lemma independentMellinWeight_moment_integrable
    (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ) :
    Integrable (fun τ : ι → ℝ => mellinHeightPower A τ*‖independentMellinWeight W X τ‖) := by
  simp only [mellinHeightPower,Finset.sum_mul]
  exact integrable_finsetSum _ (fun i _ =>
    independentMellinWeight_coordinate_moment_integrable W X hW hpos hsm hX A i)

omit [DecidableEq ι] in
lemma independentMellinWeight_norm_scale (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (τ : ι → ℝ) :
    ‖independentMellinWeight W X τ‖ = ‖independentMellinWeight W (fun _ => 1) τ‖ := by
  simp only [independentMellinWeight,norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [zeroLineMellinWeight_norm (W i) (hX i),
    zeroLineMellinWeight_norm (W i) (by norm_num)]

def independentMellinMoment (W : ι → ℝ → ℂ) (A : ℕ) : ℝ :=
  ∫ τ : ι → ℝ, mellinHeightPower A τ*‖independentMellinWeight W (fun _ => 1) τ‖

omit [DecidableEq ι] in
lemma independentMellinMoment_nonneg (W : ι → ℝ → ℂ) (A : ℕ) :
    0 ≤ independentMellinMoment W A :=
  integral_nonneg (fun τ => mul_nonneg (mellinHeightPower_nonneg A τ) (_root_.norm_nonneg _))

omit [DecidableEq ι] in
lemma independentMellinWeight_moment (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (A : ℕ) :
    (∫ τ : ι → ℝ, mellinHeightPower A τ*‖independentMellinWeight W X τ‖) =
      independentMellinMoment W A := by
  simp_rw [independentMellinWeight_norm_scale W X hX]
  rfl

theorem independentMellinWeight_tail (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hW : ∀ i, HasCompactSupport (W i)) (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (W i)) (hX : ∀ i, 0 < X i) (A : ℕ)
    {T : ℝ} (hT : 0 < T) :
    (∫ τ in (mellinHeightBox T)ᶜ, ‖independentMellinWeight W X τ‖) ≤
      independentMellinMoment W A/T^A := by
  have h := multivariate_weighted_tail (independentMellinWeight W X)
    (independentMellinWeight_integrable W X hW hpos hsm hX) A
    (independentMellinWeight_moment_integrable W X hW hpos hsm hX A) hT
  rwa [independentMellinWeight_moment W X hX A] at h

end CubicFirstMoment

end

end OAI
