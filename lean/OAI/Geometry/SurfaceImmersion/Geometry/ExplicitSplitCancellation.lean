import OAI.Geometry.SurfaceImmersion.Geometry.FiniteSplitCancellation
import OAI.Geometry.SurfaceImmersion.Geometry.MetricForcedFactorBudgets

namespace OAI

/-! The finite-chart correction retains explicit coordinate, splitting and
cardinality factors. These factors can be bounded before a fast scale is chosen. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

 def splitInputBudget (q m : ℕ) (I S : ℕ → ℝ) : ℝ :=
  let k := PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m
  tensorChartBudget k (I k) (I (k+1))*S k

 def splitSizeBudget (q m : ℕ) (C J I S : ℕ → ℝ) : ℝ :=
  max 1 (metricForcedSizeBudget C J (fun _ => 1) q m)*splitInputBudget q m I S

 def splitResidualBudget (q m : ℕ) (C J I S : ℕ → ℝ) : ℝ :=
  max 1 (metricForcedResidualBudget C J (fun _ => 1) q m)*splitInputBudget q m I S

 theorem explicit_finite_split_cancellation {ι : Type*} [Fintype ι]
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (φ : JetPolynomial.Base → ℝ) (K : Compacts SmallModes.Base)
    (L : ι → Compacts JetPolynomial.Base)
    (T : (i : ι) → SupportedField (F := ComplexTensor) K →ₗ[ℝ]
      SupportedField (F := ComplexTensor) (modeSupport (L i)))
    {τ : ℝ} {s : ℝ≥0}
    (c : (i : ι) → PolynomialSolveData emptyMetricPolynomial 0 G hG φ (L i) τ s)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hLK : ∀ i, (modeSupport (L i) : Set SmallModes.Base) ⊆ K)
    (C J I S : ℕ → ℝ) (hI : ∀ m, 1 ≤ I m) (hS : ∀ m, 1 ≤ S m)
    (hc : ∀ i, (c i).C = C ∧ (c i).D = (fun _ => 0) ∧ (c i).J = J)
    (hi : ∀ i m j, 1 ≤ j → j ≤ m → ∀ x ∈ (c i).e.target,
      ‖iteratedFDerivWithin ℝ j (c i).e.symm (c i).e.target x‖ ≤ I m)
    (hT : ∀ m i A, supportedWeightedSeminorm (modeSupport (L i)) s m (T i A) ≤
      S m * supportedWeightedSeminorm K s m A)
    (hsum : ∀ A x, ∑ i, T i A x = A x) (q : ℕ)
    (A : SupportedField (F := ComplexTensor) K) :
    ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
      (∀ m, WeightedBound univ τ m
        ((Fintype.card ι : ℝ)*splitSizeBudget q m C J I S *
          supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder
            (P := emptyMetricPolynomial) q m) A) X) ∧
      (∀ m, WeightedBound univ τ m
        ((τ/s)^(q+1)*(Fintype.card ι : ℝ)*splitResidualBudget q m C J I S *
          supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder
            (P := emptyMetricPolynomial) q m) A)
        (RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
          QuadraticMean.displacement τ (coordinatePhase φ) A)) := by
  classical
  have hsmall : τ/s+(0:ℝ)/τ^tensorLoss emptyMetricPolynomial ≤ 1 := by
    simpa only [zero_div,add_zero] using (div_le_one₀ hs).mpr hτs
  obtain ⟨X,hX,hsp,hb,hr⟩ := finite_polynomial_cancellation emptyMetricPolynomial 0 hG
    (fun _ : ι => φ) L c hτ hs hτs hs1 le_rfl hsmall (fun i => T i A) q
  have hn (i : ι) (m : ℕ) : (c i).norm (T i A) m ≤
      (tensorChartBudget m (I m) (I (m+1))*S m)*supportedWeightedSeminorm K s m A := by
    have hh := (c i).norm_le_of_weightedBound hs hs1 I hI (hi i) m
      (mul_nonneg (zero_le_one.trans (hS m)) (apply_nonneg _ _)) (T i A)
      ((weightedBound_of_supportedSeminorm s m (T i A)).mono_const (hT m i A))
    simpa only [mul_assoc] using hh
  have hsize (i : ι) (m : ℕ) : (c i).size (T i A) q m ≤
      splitSizeBudget q m C J I S * supportedWeightedSeminorm K s
        (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A := by
    rw [(c i).size_eq_factor]
    calc
      _ ≤ (c i).sizeFactor q m * (splitInputBudget q m I S *
          supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A) :=
        mul_le_mul_of_nonneg_left (hn i _) ((c i).sizeFactor_nonneg q m)
      _ ≤ max 1 (metricForcedSizeBudget C J (fun _ => 1) q m) *
          (splitInputBudget q m I S * supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A) := by
        have hf : (c i).sizeFactor q m ≤
            max 1 (metricForcedSizeBudget C J (fun _ => 1) q m) := by
          rw [(c i).metric_sizeFactor_eq (fun r => congrFun (hc i).2.1 r),
            (hc i).1,(hc i).2.2]
          exact le_max_right _ _
        apply mul_le_mul_of_nonneg_right hf
        exact mul_nonneg (mul_nonneg (tensorChartBudget_nonneg _
          (zero_le_one.trans (hI _)) (zero_le_one.trans (hI _)))
            (zero_le_one.trans (hS _))) (apply_nonneg _ _)
      _ = _ := by unfold splitSizeBudget; ring
  have hres (i : ι) (m : ℕ) : (c i).residual (T i A) q m ≤
      (τ/s)^(q+1)*splitResidualBudget q m C J I S * supportedWeightedSeminorm K s
        (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A := by
    rw [(c i).residual_eq_factor]
    simp only [zero_div,add_zero]
    calc
      _ ≤ (τ/s)^(q+1)*(c i).residualFactor q m * (splitInputBudget q m I S *
          supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A) :=
        mul_le_mul_of_nonneg_left (hn i _) (mul_nonneg
          (pow_nonneg (div_nonneg hτ.le hs.le) _) ((c i).residualFactor_nonneg q m))
      _ ≤ (τ/s)^(q+1)*max 1 (metricForcedResidualBudget C J (fun _ => 1) q m) *
          (splitInputBudget q m I S * supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_left _ (pow_nonneg (div_nonneg hτ.le hs.le) _)
          rw [(c i).metric_residualFactor_eq (fun r => congrFun (hc i).2.1 r),
            (hc i).1,(hc i).2.2]
          exact le_max_right _ _
        · exact mul_nonneg (mul_nonneg (tensorChartBudget_nonneg _
            (zero_le_one.trans (hI _)) (zero_le_one.trans (hI _)))
              (zero_le_one.trans (hS _))) (apply_nonneg _ _)
      _ = _ := by unfold splitResidualBudget; ring
  have hdisp (x : SmallModes.Base) :
      ∑ i, QuadraticMean.displacement τ (coordinatePhase φ) (T i A) x =
        QuadraticMean.displacement τ (coordinatePhase φ) A x := by
    simp only [QuadraticMean.displacement]
    rw [← QuadraticMean.realMode_sum,hsum A x]
  refine ⟨X,hX,?_,?_,?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hsp hx)
    exact hLK i hi
  · intro m
    apply (hb m).mono_const
    calc
      _ ≤ ∑ _i : ι, splitSizeBudget q m C J I S * supportedWeightedSeminorm K s
          (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) A :=
        Finset.sum_le_sum (fun i _ => hsize i m)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  · intro m
    have hsumres : (∑ i, (c i).residual (T i A) q m) ≤
        (τ/s)^(q+1)*(Fintype.card ι : ℝ)*splitResidualBudget q m C J I S *
          supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder
            (P := emptyMetricPolynomial) q m) A := by
      calc
        _ ≤ ∑ _i : ι, (τ/s)^(q+1)*splitResidualBudget q m C J I S *
            supportedWeightedSeminorm K s (PolynomialSolveData.inputOrder
              (P := emptyMetricPolynomial) q m) A :=
          Finset.sum_le_sum (fun i _ => hres i m)
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
    simpa only [coordinateFullLinearized_unperturbed,hdisp,Pi.add_def] using
      (hr m).mono_const hsumres

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
