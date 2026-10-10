import OAI.Probability.DilutedSpin.CountedSteps
import OAI.Probability.DilutedSpin.GeneralRootArrayLaw
import OAI.Probability.DilutedSpin.PhysicalAverages

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw

@[simp] theorem pi_uniform {ι : Type} [Fintype ι] [DecidableEq ι]
    {B : ι → Type} [∀ i, Fintype (B i)] [∀ i, Nonempty (B i)] :
    pi (fun i => (uniform : FiniteLaw (B i))) = (uniform : FiniteLaw ((i : ι) → B i)) := by
  ext x
  simp [pi,uniform,Fintype.card_pi,Finset.prod_inv_distrib]

lemma expect_uniform {B : Type} [Fintype B] [Nonempty B] (f : B → ℝ) :
    (uniform : FiniteLaw B).expect f = (∑ x, f x)/(Fintype.card B) := by
  simp only [expect,uniform,← Finset.mul_sum,div_eq_mul_inv]
  ring

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.SizeCoupling
open MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped BigOperators NNReal

/-- Exact entropy normalization, not merely an asymptotic comparison. -/
theorem spinMean_one {N p k l r : ℕ} [NeZero N] {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, m j ≠ 0) (hend : m (Fin.last r) = 1)
    (theta : Fin k → InteractionSample p) (h : Fin N → ℝ) :
    spinMean Q m theta h (fun _ _ _ => 1) = indexAverage theta h-N*Real.log 2 := by
  unfold spinMean spinRoot
  simp only [root_one,backwardLog_physical theta h _ r m hm hend,
    FiniteLaw.expect_const,FiniteLaw.expect_sub]
  rw [FiniteLaw.pi_uniform,FiniteLaw.pi_uniform,FiniteLaw.expect_uniform]
  rfl

theorem spinMean_base_distance {N p k l r : ℕ} [NeZero N] {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hend : m (Fin.last r) = 1)
    (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    {D : ℝ} (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    |spinMean Q m theta h ψ-(indexAverage theta h-N*Real.log 2)| ≤ D*l := by
  rw [← spinMean_one Q m (fun j => ne_of_gt (hm j)) hend theta h]
  apply FiniteLaw.abs_expect_sub_le
  intro indices
  apply FiniteLaw.abs_expect_sub_le
  intro sites
  have ht := root_factor_stability
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform r) Q m hm
    (fun x => logWeight theta h indices (KernelTower.terminalState r x)) id
    (fun i x a => ψ i (KernelTower.terminalState r x (sites i)) a) (fun _ _ _ => 1)
    (fun _ => D) (fun i x a => by simpa only [Real.log_one,sub_zero] using hψ i _ a)
  simpa only [spinRoot,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using ht

lemma integrate_close {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    {f g : Z → ℝ} {C : ℝ} (hf : Measurable f) (hg : Integrable g μ)
    (h : ∀ z, |f z-g z| ≤ C) :
    Integrable f μ ∧ |(∫ z, f z ∂μ)-(∫ z, g z ∂μ)| ≤ C := by
  have hi : Integrable f μ := integrable_of_norm_sub_le hf.aestronglyMeasurable hg
    (integrable_const C) (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,abs_sub_comm] using h z))
  exact ⟨hi,abs_integral_sub_le_const μ hi hg h⟩

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
