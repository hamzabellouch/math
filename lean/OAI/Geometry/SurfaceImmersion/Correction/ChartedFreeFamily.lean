import OAI.Geometry.SurfaceImmersion.Correction.ChartedUniformFree
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanFamily
import OAI.Geometry.SurfaceImmersion.Correction.CoordinateLinearizedCalculus

namespace OAI

/-! The actual finite free oscillation and its original-coordinate linear
residual. The constants precede the immersion and scales. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean
variable {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
    {K : ι → Compacts Base} {s : ℝ≥0}
    {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

def chartedFreeSum (d : ∀ i, ChartedMeanData (c i) r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) : RField 4 :=
  QuadraticMean.sumDisplacement τ (fun i => coordinatePhase (φ i))
    (fun i => coordinateAmplitude ((d i).freeAmplitude hρ δ q A))

lemma chartedFreeSum_eq (d : ∀ i, ChartedMeanData (c i) r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) :
    chartedFreeSum d hρ δ q A = fun x => ∑ i, (d i).displacement hρ δ q A x := rfl

lemma chartedFreeSum_smooth_support (d : ∀ i, ChartedMeanData (c i) r ρ R reference)
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) :
    ContDiff ℝ ∞ (chartedFreeSum d hρ δ q A) ∧
      tsupport (chartedFreeSum d hρ δ q A) ⊆ ⋃ i, (modeSupport (K i) : Set SmallModes.Base) := by
  rw [chartedFreeSum_eq]
  refine ⟨ContDiff.sum (fun i _ => ((d i).displacement_smooth_support hρ δ q A).1),?_⟩
  apply closure_minimal _ (isClosed_iUnion_of_finite fun i => (modeSupport (K i)).isCompact.isClosed)
  intro x hx
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro i _
  exact image_eq_zero_of_notMem_tsupport (fun hz => hn (Set.mem_iUnion.mpr
    ⟨i,((d i).displacement_smooth_support hρ δ q A).2 hz⟩))

theorem uniform_charted_free_family (p : ι → ChartedMeanProfile P)
    (hρ : 0 < ρ) (q m : ℕ) (C : ℝ) :
    ∃ B E : ℝ, 1 ≤ B ∧ 1 ≤ E ∧ ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : ι → Base → ℝ} {K : ι → Compacts Base} {ε τ : ℝ} {s : ℝ≥0}
      {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
      (d : ∀ i, ChartedMeanData (c i) r ρ R reference), (∀ i, (p i).Fits (d i)) →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 → ∀ δ : ℝ, 0 ≤ δ →
      ∀ A : SmallModes.Base → Tensor, 0 ≤ C → ContDiff ℝ ∞ A → InTrialBall Set.univ reference r A →
      WeightedBound Set.univ s (PolynomialSolveData.inputOrder (P := P) q m) C A →
      WeightedBound Set.univ τ m (B * (δ * τ)) (chartedFreeSum d hρ δ q A) ∧
      WeightedBound Set.univ τ m (E * (δ * τ) * (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1))
        (coordinateFullLinearized P ε G (chartedFreeSum d hρ δ q A)) := by
  classical
  choose B E hB hE he using fun i => uniform_charted_free_bounds (R := R) (p i) hρ q m C
  refine ⟨1 + ∑ i, B i,1 + ∑ i, E i,?_,?_,?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => zero_le_one.trans (hB i))
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => zero_le_one.trans (hE i))
  intro G hG φ K ε τ s c d hd hτ hs hτs hs1 hε hsmall δ hδ A hC hA hball hbA
  have hm (i : ι) := he i (d i) (hd i) hτ hs hτs hs1 hε hsmall δ hδ A hC hA hball hbA
  rw [chartedFreeSum_eq]
  constructor
  · have hh := WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ
      (fun i => B i * (δ * τ)) (fun i => (d i).displacement hρ δ q A)
      (fun i _ => ((d i).displacement_smooth_support hρ δ q A).1.contDiffOn)
      (fun i _ => (hm i).1)
    apply hh.mono_const
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (mul_nonneg hδ hτ.le)
  · rw [coordinateFullLinearized_sum P ε G Finset.univ _
      (fun i => ((d i).displacement_smooth_support hρ δ q A).1)]
    have hh := WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ
      (fun i => E i * (δ * τ) * (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1))
      (fun i => coordinateFullLinearized P ε G ((d i).displacement hρ δ q A))
      (fun i _ => (coordinateFullLinearized_smooth (c i).openO (c i).openU P (c i).smoothP hG
        (c i).mapsG (K i) (c i).supportU ((d i).displacement_smooth_support hρ δ q A).1
        ((d i).displacement_smooth_support hρ δ q A).2 ε).contDiffOn)
      (fun i _ => (hm i).2)
    apply hh.mono_const
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (mul_nonneg hδ hτ.le))
      (pow_nonneg (add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))) _)

theorem uniform_charted_free_family_all_inputs (p : ι → ChartedMeanProfile P)
    (hρ : 0 < ρ) (q m : ℕ) (C : ℝ) :
    ∃ B E : ℝ, 1 ≤ B ∧ 1 ≤ E ∧ ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : ι → Base → ℝ} {K : ι → Compacts Base} {ε τ : ℝ} {s : ℝ≥0}
      {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
      {r : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ∀ i, ChartedMeanData (c i) r ρ R reference), (∀ i, (p i).Fits (d i)) →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 → ∀ δ : ℝ, 0 ≤ δ →
      ∀ A : SmallModes.Base → Tensor, 0 ≤ C → ContDiff ℝ ∞ A → InTrialBall Set.univ reference r A →
      WeightedBound Set.univ s (PolynomialSolveData.inputOrder (P := P) q m) C A →
      WeightedBound Set.univ τ m (B * (δ * τ)) (chartedFreeSum d hρ δ q A) ∧
      WeightedBound Set.univ τ m (E * (δ * τ) * (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1))
        (coordinateFullLinearized P ε G (chartedFreeSum d hρ δ q A)) := by
  classical
  choose B E hB hE he using fun i => uniform_charted_free_bounds (R := R) (p i) hρ q m C
  refine ⟨1 + ∑ i, B i,1 + ∑ i, E i,?_,?_,?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => zero_le_one.trans (hB i))
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => zero_le_one.trans (hE i))
  intro G hG φ K ε τ s c r reference d hd hτ hs hτs hs1 hε hsmall δ hδ A hC hA hball hbA
  have hm (i : ι) := he i (d i) (hd i) hτ hs hτs hs1 hε hsmall δ hδ A hC hA hball hbA
  rw [chartedFreeSum_eq]
  constructor
  · have hh := WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ
      (fun i => B i * (δ * τ)) (fun i => (d i).displacement hρ δ q A)
      (fun i _ => ((d i).displacement_smooth_support hρ δ q A).1.contDiffOn)
      (fun i _ => (hm i).1)
    apply hh.mono_const
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (mul_nonneg hδ hτ.le)
  · rw [coordinateFullLinearized_sum P ε G Finset.univ _
      (fun i => ((d i).displacement_smooth_support hρ δ q A).1)]
    have hh := WeightedBound.finset_sum isOpen_univ.uniqueDiffOn hτ.le Finset.univ
      (fun i => E i * (δ * τ) * (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1))
      (fun i => coordinateFullLinearized P ε G ((d i).displacement hρ δ q A))
      (fun i _ => (coordinateFullLinearized_smooth (c i).openO (c i).openU P (c i).smoothP hG
        (c i).mapsG (K i) (c i).supportU ((d i).displacement_smooth_support hρ δ q A).1
        ((d i).displacement_smooth_support hρ δ q A).2 ε).contDiffOn)
      (fun i _ => (hm i).2)
    apply hh.mono_const
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (mul_nonneg hδ hτ.le))
      (pow_nonneg (add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))) _)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
