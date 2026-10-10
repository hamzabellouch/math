import OAI.Geometry.SurfaceImmersion.Correction.PolynomialFixedCancellation

namespace OAI

/-! One polynomial bound for all phases in a fixed finite catalog.
The target supports may vary with the immersion and the scale. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates RealModes

lemma coordinatePhase_lift (φ : SmallModes.Base → ℝ) :
    coordinatePhase (φ ∘ planeCoordinateIsometry) = φ := by
  funext x
  simp only [coordinatePhase,Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]

theorem finite_catalog_polynomial_cancellation
    (Γ : Finset (SmallModes.Base → ℝ)) (hΓ : ∀ φ ∈ Γ, ContDiff ℝ ∞ φ)
    (K₀ : Compacts SmallModes.Base) {ε b D : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hD : 1 ≤ D) (hDB : (ε*b)⁻¹ ≤ D)
    (B : ℕ → ℝ → ℝ) (hB : ∀ m, HasPolynomialBound (B m))
    (hB1 : ∀ m x, 1 ≤ x → 1 ≤ B m x) (q : ℕ) :
    ∃ (d : ℕ → ℕ) (E : ℕ → ℝ), (∀ m, 1 ≤ E m) ∧
      ∀ x : ℝ, 1 ≤ x → ∀ φ ∈ Γ,
      ∀ {G : JetPolynomial.Base → JetPolynomial.Space} (_hG : ContDiff ℝ ∞ G)
        (K : Compacts SmallModes.Base), (K : Set SmallModes.Base) ⊆ K₀ →
      (∀ y ∈ (K : Set SmallModes.Base),
        Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) y)) →
      (∀ y ∈ (K : Set SmallModes.Base), b ≤ ‖realSecondTensor (G ∘ planeCoordinateIsometry.symm) y‖) →
      (∀ y ∈ (K : Set SmallModes.Base),
        ε*‖realSecondTensor (G ∘ planeCoordinateIsometry.symm) y‖ ≤
          ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) y)
            (-(phaseDerivative φ y).2,(phaseDerivative φ y).1)‖) →
      (∀ y ∈ (K : Set SmallModes.Base),
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) y)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) y))⁻¹‖ ≤ D) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m j, j ≤ m+3 → WeightedBound univ 1 j
        (B m x/(s : ℝ)^(j-2)) (G ∘ planeCoordinateIsometry.symm)) →
      ∀ f : SupportedField (F := ComplexTensor) K,
      ∃ X : RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m
          (E m*x^(d m)*supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f) X) ∧
        (∀ m, WeightedBound univ τ m
          ((τ/s)^(q+1)*(E m*x^(d m))*supportedWeightedSeminorm K s
            (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f)
          (realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
            QuadraticMean.displacement τ φ f)) := by
  classical
  have hsmooth (φ : Γ) : ContDiff ℝ ∞ (φ.val ∘ planeCoordinateIsometry) :=
    (hΓ φ.val φ.property).comp planeCoordinateIsometry.contDiff
  choose N J S p A hJ hS hA hc using fun φ : Γ =>
    relative_phase_polynomial_cancellation (hsmooth φ) K₀ hε hb
  let C := fun (φ : Γ) m x => (N φ : ℝ)*splitSizeBudget q m
    (fun r => A φ r*(fixedChartSolverBudget (J φ) (fun j => B j x) D r)^(p φ r))
    (fixedChartSolverBudget (J φ) (fun j => B j x) D) (J φ) (S φ)
  let R := fun (φ : Γ) m x => (N φ : ℝ)*splitResidualBudget q m
    (fun r => A φ r*(fixedChartSolverBudget (J φ) (fun j => B j x) D r)^(p φ r))
    (fixedChartSolverBudget (J φ) (fun j => B j x) D) (J φ) (S φ)
  have hpoly (φ : Γ) (m : ℕ) : HasPolynomialBound (C φ m) ∧ HasPolynomialBound (R φ m) :=
    fixed_cancellation_budgets_polynomial (N φ) q m (J φ) (S φ) (A φ) (p φ) B
      (hJ φ) (hS φ) (hA φ) hD hB hB1
  let H := fun m x => ∑ φ : Γ, (C φ m x+R φ m x)
  have hH (m : ℕ) : HasPolynomialBound (H m) :=
    HasPolynomialBound.sum Finset.univ (fun φ : Γ => fun x => C φ m x+R φ m x)
      (fun φ _ => (hpoly φ m).1.add (hpoly φ m).2)
  choose d E hE hbound using hH
  have hnonneg (φ : Γ) (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : 0 ≤ C φ m x ∧ 0 ≤ R φ m x := by
    obtain ⟨_,_,_,h⟩ := (hpoly φ m).1
    obtain ⟨_,_,_,h'⟩ := (hpoly φ m).2
    exact ⟨(h x hx).1,(h' x hx).1⟩
  have hmajor (φ : Γ) (m : ℕ) (x : ℝ) (hx : 1 ≤ x) :
      C φ m x ≤ E m*x^(d m) ∧ R φ m x ≤ E m*x^(d m) := by
    have hh : C φ m x+R φ m x ≤ H m x :=
      Finset.single_le_sum (fun ψ _ => add_nonneg (hnonneg ψ m x hx).1 (hnonneg ψ m x hx).2)
        (Finset.mem_univ φ)
    exact ⟨((le_add_of_nonneg_right (hnonneg φ m x hx).2).trans hh).trans (hbound m x hx).2,
      ((le_add_of_nonneg_left (hnonneg φ m x hx).1).trans hh).trans (hbound m x hx).2⟩
  refine ⟨d,E,hE,?_⟩
  intro x hx φ hφ G hG K hK hImm hBnorm hrel hgram τ s hτ hs hτs hs1 hFj f
  let γ : Γ := ⟨φ,hφ⟩
  have hrel' : ∀ y ∈ (K : Set SmallModes.Base),
      ε*‖realSecondTensor (G ∘ planeCoordinateIsometry.symm) y‖ ≤
        ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) y)
          (-(phaseDerivative (coordinatePhase (γ.val ∘ planeCoordinateIsometry)) y).2,
            (phaseDerivative (coordinatePhase (γ.val ∘ planeCoordinateIsometry)) y).1)‖ := by
    simpa only [coordinatePhase_lift] using hrel
  obtain ⟨X,hX,hsp,hv,hr⟩ := hc γ hG K hK D hD hDB hImm hBnorm hrel' hgram
    τ s hτ hs hτs hs1 (fun j => B j x) (fun j => hB1 j x hx) hFj q f
  refine ⟨X,hX,hsp,?_,?_⟩
  · intro m
    exact (hv m).mono_const (mul_le_mul_of_nonneg_right (hmajor γ m x hx).1 (apply_nonneg _ _))
  · intro m
    have hh := hr m
    simp only [coordinatePhase_lift] at hh
    apply hh.mono_const
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hmajor γ m x hx).2
        (pow_nonneg (div_nonneg hτ.le hs.le) (q+1)))
      (show 0 ≤ supportedWeightedSeminorm K s
        (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) f from apply_nonneg _ _)
    simpa only [R,mul_assoc] using hm

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
