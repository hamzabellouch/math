import OAI.Geometry.SurfaceImmersion.Correction.PolynomialProfileTransfer
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteSplitCancellation

namespace OAI

/-!
Uniform finite cancellation from actual-scale solver records with fixed
numeric profiles.  No reference solver at unit scale is used.  All constants
are selected before the map, phase, target and both scales.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal

namespace ClosedSurfaceR4.PhaseGeometry

open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

theorem profiled_split_cancellation {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin 3 → Fin n → Expression) (K : Compacts SmallModes.Base)
    (L : ι → Compacts JetPolynomial.Base)
    (T : (i : ι) → SupportedField (F := ComplexTensor) K →ₗ[ℝ]
      SupportedField (F := ComplexTensor) (modeSupport (L i)))
    (hLK : ∀ i, (modeSupport (L i) : Set SmallModes.Base) ⊆ K)
    (C J I : ι → ℕ → ℝ) (hC : ∀ i m, 0 ≤ C i m)
    (hJ : ∀ i m, 1 ≤ J i m) (hI : ∀ i m, 1 ≤ I i m)
    (S : ℕ → ℝ) (hS : ∀ m, 1 ≤ S m)
    (hT : ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 → ∀ m i A,
      supportedWeightedSeminorm (modeSupport (L i)) s m (T i A) ≤
        S m * supportedWeightedSeminorm K s m A)
    (hsum : ∀ A x, ∑ i, T i A x = A x) (q : ℕ) :
    ∃ Cv Ct : ℕ → ℝ, (∀ m, 0 ≤ Cv m) ∧ (∀ m, 0 ≤ Ct m) ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (φ : JetPolynomial.Base → ℝ) (τ : ℝ) (s : ℝ≥0),
        0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ (c : (i : ι) → PolynomialSolveData P 0 G hG φ (L i) τ s),
        (∀ i, (c i).C = C i) → (∀ i, (c i).D = 0) → (∀ i, (c i).J = J i) →
        (∀ i m j, 1 ≤ j → j ≤ m → ∀ x ∈ (c i).e.target,
          ‖iteratedFDerivWithin ℝ j (c i).e.symm (c i).e.target x‖ ≤ I i m) →
      ∀ A : SupportedField (F := ComplexTensor) K,
      ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m
          (Cv m * supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := P) q m) A) X) ∧
        (∀ m, WeightedBound univ τ m
          ((τ / s) ^ (q + 1) * Ct m * supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := P) q m) A)
          (RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
            QuadraticMean.displacement τ (coordinatePhase φ) A)) := by
  classical
  let b : ι → ℕ → ℝ := fun i m =>
    tensorChartBudget m (I i m) (I i (m + 1)) * S m
  have hbn (i : ι) (m : ℕ) : 0 ≤ b i m :=
    mul_nonneg (tensorChartBudget_nonneg m (zero_le_one.trans (hI i m))
      (zero_le_one.trans (hI i (m + 1)))) (zero_le_one.trans (hS m))
  let V : ι → ℕ → ℝ := fun i m =>
    PolynomialSolveData.sizeProfile P (C i) 0 (J i) q m
  let R : ι → ℕ → ℝ := fun i m =>
    PolynomialSolveData.residualProfile P (C i) 0 (J i) q m
  have hV (i : ι) (m : ℕ) : 0 ≤ V i m :=
    PolynomialSolveData.sizeProfile_nonneg P (C i) 0 (J i) (hC i)
      (fun m => zero_le_one.trans (hJ i m)) q m
  have hR (i : ι) (m : ℕ) : 0 ≤ R i m :=
    PolynomialSolveData.residualProfile_nonneg P (C i) 0 (J i) (hC i)
      (fun m => zero_le_one.trans (hJ i m)) q m
  let Cv := fun m => ∑ i, V i m * b i (PolynomialSolveData.inputOrder (P := P) q m)
  let Ct := fun m => ∑ i, R i m * b i (PolynomialSolveData.inputOrder (P := P) q m)
  refine ⟨Cv, Ct, ?_, ?_, ?_⟩
  · intro m
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hV i m) (hbn i _))
  · intro m
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hR i m) (hbn i _))
  · intro G hG φ τ s hτ hs hτs hs1 c hc hd hj hi A
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
        (V i m * b i (PolynomialSolveData.inputOrder (P := P) q m)) *
          supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A := by
      rw [(c i).size_eq_factor, (c i).sizeFactor_eq_sizeProfile (hc i) (hd i) (hj i)]
      exact (mul_le_mul_of_nonneg_left (hn i _) (hV i m)).trans_eq (mul_assoc _ _ _).symm
    have hres (i : ι) (m : ℕ) : (c i).residual (T i A) q m ≤
        (τ / s) ^ (q + 1) * (R i m * b i (PolynomialSolveData.inputOrder (P := P) q m)) *
          supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A := by
      rw [(c i).residual_eq_factor, (c i).residualFactor_eq_residualProfile (hc i) (hd i) (hj i)]
      simp only [zero_div, add_zero]
      calc
        _ ≤ ((τ / s) ^ (q + 1) * R i m) *
            (b i (PolynomialSolveData.inputOrder (P := P) q m) *
              supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A) :=
          mul_le_mul_of_nonneg_left (hn i _)
            (mul_nonneg (pow_nonneg (div_nonneg hτ.le hs.le) _) (hR i m))
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
        _ ≤ ∑ i, (V i m * b i (PolynomialSolveData.inputOrder (P := P) q m)) *
              supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A :=
          Finset.sum_le_sum (fun i _ => hsz i m)
        _ = _ := (Finset.sum_mul _ _ _).symm
    · intro m
      have hbound : (∑ i, (c i).residual (T i A) q m) ≤
          (τ / s) ^ (q + 1) * Ct m *
            supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A := by
        calc
          _ ≤ ∑ i, (τ / s) ^ (q + 1) *
              (R i m * b i (PolynomialSolveData.inputOrder (P := P) q m)) *
              supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder (P := P) q m) A :=
            Finset.sum_le_sum (fun i _ => hres i m)
          _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
      simpa only [coordinateFullLinearized_unperturbed, hdisp, Pi.add_def] using
        (hr m).mono_const hbound

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
