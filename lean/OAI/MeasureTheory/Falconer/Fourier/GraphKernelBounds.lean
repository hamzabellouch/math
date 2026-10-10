import OAI.MeasureTheory.Falconer.Fourier.GraphFourPointKernel

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem inheritedCircleSymbol_norm_le {ι : Type*} (S : Finset ι)
    (b : ι → PolicyDescriptor) (k : ι → ℕ) (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (h : Plane → ℂ) (K : ℕ) (hK : ∑ a ∈ S, k a ≤ K)
    (x : Plane) (hx : ‖h x‖ ≤ 1) (ω : UnitCircle) :
    ‖inheritedCircleSymbol S b k Q ρ m N lam sig J i h x ω‖ ≤
      symbolDerivativeConstant K^K := by
  classical
  simp only [inheritedCircleSymbol, norm_mul, Complex.norm_real]
  exact (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans
    (by simpa using (inheritedMaskProduct_zero_bound S b k Q hQ ρ m N lam sig J i
      (fun _ => x) K hK (sourceAngle ω)))

theorem graphBinWeight_bounds (n j k : ℕ) (p : UnitCircle × UnitCircle) :
    0 ≤ graphBinWeight n j k p ∧ graphBinWeight n j k p ≤ 1 := by
  have hu := circleAngularBin_bounds n j p.1
  have hv := circleAngularBin_bounds n k p.2
  exact ⟨mul_nonneg hu.1 hv.1, by simpa [graphBinWeight] using mul_le_mul hu.2 hv.2 hv.1 zero_le_one⟩

theorem graphDistanceWeight_norm_le (axis : ℝ) (n j k : ℕ) (p : UnitCircle × UnitCircle) :
    ‖graphDistanceWeight axis n j k p‖ ≤ 1 := by
  have hb := graphBinWeight_bounds n j k p
  simp only [graphDistanceWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb.1, Complex.norm_conj]
  exact (mul_le_mul (mul_le_mul hb.2 (sourceConeCircle_norm_le axis p.1)
    (norm_nonneg _) zero_le_one) (sourceConeCircle_norm_le axis p.2)
      (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem graphProductWeight_norm_le (plus : Bool) (n j k : ℕ) (p : UnitCircle × UnitCircle) :
    ‖graphProductWeight plus n j k p‖ ≤ 1 := by
  have hb := graphBinWeight_bounds n j k p
  have hs := graphSignPartition_bounds (p.1,p.2)
  cases plus <;> simp only [graphProductWeight, Bool.false_eq_true, ↓reduceIte,
    Complex.norm_real, Real.norm_eq_abs, circleGraphSignPlus, circleGraphSignMinus]
  · rw [abs_of_nonneg (mul_nonneg hb.1 hs.2.2.1)]
    exact (mul_le_mul hb.2 hs.2.2.2.1 hs.2.2.1 zero_le_one).trans_eq (by ring)
  · rw [abs_of_nonneg (mul_nonneg hb.1 hs.1)]
    exact (mul_le_mul hb.2 hs.2.1 hs.1 zero_le_one).trans_eq (by ring)

theorem graphFourKernel_norm_le (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ) (B : Fin 4 → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hb : ∀ i x ω, ‖b i x ω‖ ≤ B i)
    (hW : ∀ p, ‖W p‖ ≤ 1) (x : Fin 4 → Plane) (r : ℝ) (u v : UnitCircle) :
    ‖graphFourKernel b W x r u v‖ ≤ (B 0*B 1)*(B 2*B 3) := by
  simp only [graphFourKernel, graphFourAmplitude, norm_mul, sourcePlaneWave_norm,
    one_mul, Complex.norm_conj]
  exact (mul_le_mul
    (mul_le_mul (hW (u,v))
      (mul_le_mul (hb 0 _ _) (hb 1 _ _) (norm_nonneg _) (hB 0))
      (by positivity) zero_le_one)
    (mul_le_mul (hb 2 _ _) (hb 3 _ _) (norm_nonneg _) (hB 2))
    (by positivity) (mul_nonneg zero_le_one (mul_nonneg (hB 0) (hB 1)))).trans_eq (by ring)

theorem graphFourKernel_measurable (b : Fin 4 → Plane → UnitCircle → ℂ)
    (W : UnitCircle × UnitCircle → ℂ)
    (hb : ∀ i, Measurable (fun p : Plane × UnitCircle => b i p.1 p.2))
    (hW : Measurable W) :
    Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      graphFourKernel b W p.2 p.1.1 p.1.2.1 p.1.2.2) := by
  unfold graphFourKernel graphFourAmplitude sourcePlaneWave
  have h0 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 0 (p.2 0) p.1.2.1) := (hb 0).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 0, p.1.2.1)) from by fun_prop)
  have h1 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 1 (p.2 1) p.1.2.1) := (hb 1).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 1, p.1.2.1)) from by fun_prop)
  have h2 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 2 (p.2 2) p.1.2.2) := (hb 2).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 2, p.1.2.2)) from by fun_prop)
  have h3 : Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
      b 3 (p.2 3) p.1.2.2) := (hb 3).comp
        (show Measurable (fun p : (ℝ × (UnitCircle × UnitCircle)) × (Fin 4 → Plane) =>
          (p.2 3, p.1.2.2)) from by fun_prop)
  apply Measurable.mul
  · fun_prop
  · exact (((hW.comp (measurable_snd.comp measurable_fst)).mul
      (h0.mul (Complex.continuous_conj.measurable.comp h1))).mul
      (h2.mul (Complex.continuous_conj.measurable.comp h3)))

end PlanarFalconer

end OAI
