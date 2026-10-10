import OAI.MathematicalPhysics.CriticalSK.Main
import OAI.Probability.SKGap.Main

namespace OAI

noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter

namespace CriticalSK

lemma disorderLaw_temperature_map (n : ℕ) (β : ℝ) :
    (disorderLaw n).map (fun W => β • W) = SKGap.disorderLaw β n := by
  unfold disorderLaw SKGap.disorderLaw
  change (Measure.pi (fun _ : Edge n => gaussianReal 0 (n : ℝ≥0)⁻¹)).map
      (fun W e => β * W e) = _
  rw [Measure.pi_map_pi (f := fun _ : Edge n => fun a : ℝ => β * a)
    (fun _ => (measurable_const.mul measurable_id).aemeasurable)]
  congr 1
  funext e
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_inv, NNReal.coe_natCast]
  rw [Real.coe_toNNReal _ (div_nonneg (sq_nonneg β) (Nat.cast_nonneg n))]
  exact (div_eq_mul_inv _ _).symm

lemma companion_hamiltonian {n : ℕ} (W : Disorder n) (x : Spin n) :
    SKGap.hamiltonian W 0 x = hamiltonian W x := by
  unfold SKGap.hamiltonian
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  rw [symmetric_sum_upper _ (by
    intro i j
    rw [SKGap.coupling_symm W i j]
    ring)]
  have hd : (∑ i : Fin n, SKGap.spinValue (x i) * SKGap.coupling W i i *
      SKGap.spinValue (x i)) = 0 := by simp [SKGap.coupling_diag]
  rw [hd, zero_add]
  have he : (∑ e : Edge n, SKGap.spinValue (x e.val.1) *
      SKGap.coupling W e.val.1 e.val.2 * SKGap.spinValue (x e.val.2)) = hamiltonian W x := by
    unfold hamiltonian
    apply Finset.sum_congr rfl
    intro e _
    simp only [SKGap.coupling, dite_eq_left e.property]
    change spinValue (x e.val.1) * W e * spinValue (x e.val.2) = _
    ring
  rw [he]
  ring

lemma companion_partition {n : ℕ} (W : Disorder n) : SKGap.partition W 0 = partition W := by
  simp only [SKGap.partition, SKGap.weight, companion_hamiltonian, partition]

lemma companion_mass {n : ℕ} (W : Disorder n) (x : Spin n) :
    SKGap.mass W 0 x = gibbs W x := by
  rw [SKGap.mass, SKGap.weight, companion_hamiltonian, companion_partition]
  rfl

lemma companion_expectation {n : ℕ} (W : Disorder n) (f : Spin n → ℝ) :
    SKGap.expectation W 0 f = mean W f := by
  simp only [SKGap.expectation, companion_mass, mean]

lemma companion_variance {n : ℕ} (W : Disorder n) (f : Spin n → ℝ) :
    SKGap.variance W 0 f = variance W f := by
  simp only [SKGap.variance, companion_expectation, variance]

lemma companion_conditionalExpectation {n : ℕ} (W : Disorder n) (i : Fin n)
    (f : Spin n → ℝ) (x : Spin n) :
    SKGap.conditionalExpectation W 0 i f x = ∑ y, siteKernel W i x y * f y := by
  rw [← siteAverage_eq, siteAverage_two]
  rw [← companion_mass W x, show flipSite i x = SKGap.flip i x from rfl,
    ← companion_mass W (SKGap.flip i x)]
  simp only [SKGap.conditionalExpectation, SKGap.mass, div_mul_eq_mul_div, ← add_div,
    div_div_div_cancel_right₀ (ne_of_gt (SKGap.partition_pos W 0))]

lemma companion_dirichlet {n : ℕ} (W : Disorder n) (f : Spin n → ℝ) :
    SKGap.dirichlet W 0 f = dirichlet W f := by
  simp only [SKGap.dirichlet, companion_expectation, companion_conditionalExpectation, dirichlet]

lemma companion_poincare_preimage (n : ℕ) (β C : ℝ) :
    (fun W : Disorder n => β • W) ⁻¹' SKGap.poincareEvent n C = poincareEvent n β C := by
  ext W
  simp only [Set.mem_preimage, SKGap.poincareEvent, poincareEvent, Set.mem_ofPred_eq,
    companion_variance, companion_dirichlet]

lemma companion_poincare_measurable (n : ℕ) (C : ℝ) :
    MeasurableSet (SKGap.poincareEvent n C) := by
  have he : SKGap.poincareEvent n C = poincareEvent n 1 C := by
    simpa only [one_smul, Set.preimage_id'] using companion_poincare_preimage n 1 C
  rw [he]
  exact (poincareEvent_closed n 1 C).measurableSet

lemma companion_poincare_probability (n : ℕ) (β C : ℝ) :
    SKGap.disorderLaw β n (SKGap.poincareEvent n C) = disorderLaw n (poincareEvent n β C) := by
  rw [← disorderLaw_temperature_map,
    Measure.map_apply (continuous_const_smul β).measurable (companion_poincare_measurable n C),
    companion_poincare_preimage]

theorem fixed_temperature_poincare (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ Tendsto (fun n : ℕ =>
      (disorderLaw n).real (poincareEvent n β C)) atTop (𝓝 1) := by
  obtain ⟨C, hC, hP, _⟩ := SKGap.sk_main β hβ0 hβ1
  have hp : Tendsto (fun n : ℕ => (disorderLaw n).real (poincareEvent n β C))
      atTop (𝓝 1) := by
    simp_rw [companion_poincare_probability] at hP
    simpa only [Measure.real, ENNReal.toReal_one, Function.comp_def] using
      (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp hP
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hp tendsto_const_nhds
  · intro n
    refine measureReal_mono ?_
    intro W hW f
    exact (hW f).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (dirichlet_nonneg (β • W) f))
  · intro n
    exact measureReal_le_one

end CriticalSK
end

end OAI
