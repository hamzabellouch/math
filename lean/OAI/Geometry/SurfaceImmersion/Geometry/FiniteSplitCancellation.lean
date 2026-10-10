import OAI.Geometry.SurfaceImmersion.Correction.PolynomialInputNorm
import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedSolverScale
import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedSolverFacts
import OAI.Geometry.SurfaceImmersion.Correction.FinitePolynomialCancellation
import OAI.Geometry.SurfaceImmersion.Geometry.DisplacementSum

namespace OAI

/-!
Cancellation by a fixed finite family of unperturbed phase solvers.  The
partition, local solvers, inverse-chart bounds and splitting bounds are all
fixed before choosing the target or scales.  Thus the resulting constants
depend only on that geometric data and the finite iteration order.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal

namespace ClosedSurfaceR4.PhaseGeometry

open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

/-- Uniform cancellation of targets split among finitely many fixed phase
charts.  Neither the constants nor the input derivative order depend on the
target, wavelength or slow scale. -/
theorem finite_split_cancellation {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin 3 → Fin n → Expression)
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (φ : JetPolynomial.Base → ℝ) (K : Compacts SmallModes.Base)
    (L : ι → Compacts JetPolynomial.Base)
    (T : (i : ι) → SupportedField (F := ComplexTensor) K →ₗ[ℝ]
      SupportedField (F := ComplexTensor) (modeSupport (L i)))
    (c₀ : (i : ι) → PolynomialSolveData P 0 G hG φ (L i) 1 1)
    (hLK : ∀ i, (modeSupport (L i) : Set SmallModes.Base) ⊆ K)
    (I : ι → ℕ → ℝ) (hI : ∀ i m, 1 ≤ I i m)
    (hi : ∀ i m j, 1 ≤ j → j ≤ m → ∀ x ∈ (c₀ i).e.target,
      ‖iteratedFDerivWithin ℝ j (c₀ i).e.symm (c₀ i).e.target x‖ ≤ I i m)
    (S : ℕ → ℝ) (hS : ∀ m, 1 ≤ S m)
    (hT : ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 → ∀ m i A,
      supportedWeightedSeminorm (modeSupport (L i)) s m (T i A) ≤
        S m * supportedWeightedSeminorm K s m A)
    (hsum : ∀ A x, ∑ i, T i A x = A x) (q : ℕ) :
    ∃ C D : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ (∀ m, 0 ≤ D m) ∧
      ∀ (A : SupportedField (F := ComplexTensor) K) (τ : ℝ) (s : ℝ≥0),
        0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m
          (C m * supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := P) q m) A) X) ∧
        (∀ m, WeightedBound univ τ m
          ((τ / s) ^ (q + 1) * D m * supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := P) q m) A)
          (RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
            QuadraticMean.displacement τ (coordinatePhase φ) A)) := by
  classical
  let b : ι → ℕ → ℝ := fun i m =>
    tensorChartBudget m (I i m) (I i (m + 1)) * S m
  have hbn (i : ι) (m : ℕ) : 0 ≤ b i m :=
    mul_nonneg (tensorChartBudget_nonneg m (zero_le_one.trans (hI i m))
      (zero_le_one.trans (hI i (m + 1)))) (zero_le_one.trans (hS m))
  let cbase := fun i => (c₀ i).atUnperturbedScale 1 1 le_rfl
  let C := fun m => ∑ i, (cbase i).sizeFactor q m *
    b i (PolynomialSolveData.inputOrder (P := P) q m)
  let D := fun m => ∑ i, (cbase i).residualFactor q m *
    b i (PolynomialSolveData.inputOrder (P := P) q m)
  refine ⟨C, D, ?_, ?_, ?_⟩
  · intro m
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg ((cbase i).sizeFactor_nonneg q m) (hbn i _))
  · intro m
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg ((cbase i).residualFactor_nonneg q m) (hbn i _))
  · intro A τ s hτ hs hτs hs1
    let c := fun i => (c₀ i).atUnperturbedScale τ s hs1
    have hsmall : τ / s + (0 : ℝ) / τ ^ tensorLoss P ≤ 1 := by
      simpa only [zero_div, add_zero] using (div_le_one₀ hs).mpr hτs
    obtain ⟨X, hX, hsp, hb, hr⟩ := finite_polynomial_cancellation P 0 hG
      (fun _ : ι => φ) L c hτ hs hτs hs1 le_rfl hsmall (fun i => T i A) q
    have hn (i : ι) (m : ℕ) : (c i).norm (T i A) m ≤
        b i m * supportedWeightedSeminorm K s m A := by
      have hbound := (c i).norm_le_of_weightedBound hs hs1 (I i) (hI i) (hi i) m
        (mul_nonneg (zero_le_one.trans (hS m)) (apply_nonneg _ _)) (T i A)
        ((weightedBound_of_supportedSeminorm s m (T i A)).mono_const
          (hT s hs hs1 m i A))
      simpa only [b, mul_assoc] using hbound
    have hsz (i : ι) (m : ℕ) : (c i).size (T i A) q m ≤
        ((cbase i).sizeFactor q m * b i (PolynomialSolveData.inputOrder (P := P) q m)) *
          supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A := by
      rw [(c i).size_eq_factor]
      exact (mul_le_mul_of_nonneg_left (hn i _) ((cbase i).sizeFactor_nonneg q m)).trans_eq
        (mul_assoc _ _ _).symm
    have hres (i : ι) (m : ℕ) : (c i).residual (T i A) q m ≤
        (τ / s) ^ (q + 1) *
          ((cbase i).residualFactor q m * b i (PolynomialSolveData.inputOrder (P := P) q m)) *
          supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A := by
      rw [(c i).residual_eq_factor]
      simp only [zero_div, add_zero]
      calc
        _ ≤ ((τ / s) ^ (q + 1) * (cbase i).residualFactor q m) *
            (b i (PolynomialSolveData.inputOrder (P := P) q m) *
              supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A) :=
          mul_le_mul_of_nonneg_left (hn i _)
            (mul_nonneg (pow_nonneg (div_nonneg hτ.le hs.le) _)
              ((cbase i).residualFactor_nonneg q m))
        _ = _ := by ring
    have hdisp (x : SmallModes.Base) :
        ∑ i, QuadraticMean.displacement τ (coordinatePhase φ) (T i A) x =
          QuadraticMean.displacement τ (coordinatePhase φ) A x := by
      simp only [QuadraticMean.displacement]
      rw [← QuadraticMean.realMode_sum, hsum A x]
    refine ⟨X, hX, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hsp hx)
      exact hLK i hi
    · intro m
      apply (hb m).mono_const
      calc
        _ ≤ ∑ i, ((cbase i).sizeFactor q m *
            b i (PolynomialSolveData.inputOrder (P := P) q m)) *
              supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A :=
          Finset.sum_le_sum (fun i _ => hsz i m)
        _ = _ := (Finset.sum_mul _ _ _).symm
    · intro m
      have hbound : (∑ i, (c i).residual (T i A) q m) ≤
          (τ / s) ^ (q + 1) * D m *
            supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A := by
        calc
          _ ≤ ∑ i, (τ / s) ^ (q + 1) *
              ((cbase i).residualFactor q m * b i (PolynomialSolveData.inputOrder (P := P) q m)) *
              supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A :=
            Finset.sum_le_sum (fun i _ => hres i m)
          _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
      simpa only [coordinateFullLinearized_unperturbed, hdisp, Pi.add_def] using
        (hr m).mono_const hbound

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
