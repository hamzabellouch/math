import OAI.Geometry.SurfaceImmersion.Atlas.CompactPhaseSolvers
import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedScaleNorm
import OAI.Geometry.SurfaceImmersion.Correction.FinitePolynomialCancellation
import OAI.Geometry.SurfaceImmersion.Geometry.DisplacementSum

namespace OAI

/-! Cancellation on an arbitrary compact support from actual good-phase geometry. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

/-- A single good phase on a compact support needs only finitely many local
phase charts. Their actual corrections cancel the original target at every
smaller wavelength, with one set of constants for that target. -/
theorem compact_good_phase_cancellation
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    {φ : JetPolynomial.Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K : Compacts SmallModes.Base)
    (hImm : ∀ p ∈ (K : Set SmallModes.Base),
      Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) p))
    (hgood : ∀ p ∈ (K : Set SmallModes.Base),
      Good (RealModes.realSecondTensor (G ∘ planeCoordinateIsometry.symm) p)
        (phaseDerivative (coordinatePhase φ) p))
    (A : SupportedField (F := ComplexTensor) K) (q : ℕ) :
    ∃ C D : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ (∀ m, 0 ≤ D m) ∧
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ K ∧
        (∀ m, WeightedBound univ τ m (C m) X) ∧
        (∀ m, WeightedBound univ τ m ((τ/s)^(q+1) * D m)
          (RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X +
            QuadraticMean.displacement τ (coordinatePhase φ) A)) := by
  classical
  obtain ⟨t,L,B,c,hLK,_,hsum⟩ := compact_phase_solvers hG hφ K hImm hgood A
  let cbase := fun i : t => (c i).atUnperturbedScale 1 1 le_rfl
  let C := fun m => ∑ i : t, (cbase i).sizeFactor q m *
    (c i).norm (B i) (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m)
  let D := fun m => ∑ i : t, (cbase i).residualFactor q m *
    (c i).norm (B i) (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m)
  have hn (i : t) (m : ℕ) : 0 ≤ (c i).norm (B i) m := apply_nonneg _ _
  refine ⟨C,D,?_,?_,?_⟩
  · intro m
    exact Finset.sum_nonneg (fun i _ => mul_nonneg ((cbase i).sizeFactor_nonneg q m) (hn i _))
  · intro m
    exact Finset.sum_nonneg (fun i _ => mul_nonneg ((cbase i).residualFactor_nonneg q m) (hn i _))
  · intro τ s hτ hs hτs hs1
    let d := fun i : t => (c i).atUnperturbedScale τ s hs1
    have hsmall : τ/s + (0:ℝ)/τ^tensorLoss emptyMetricPolynomial ≤ 1 := by
      simpa only [zero_div,add_zero] using (div_le_one₀ hs).mpr hτs
    obtain ⟨X,hX,hsp,hb,hr⟩ := finite_polynomial_cancellation emptyMetricPolynomial 0 hG
      (fun _ : t => φ) L d hτ hs hτs hs1 le_rfl hsmall B q
    have hnorm (i : t) (m : ℕ) : (d i).norm (B i) m ≤ (c i).norm (B i) m :=
      (c i).norm_atUnperturbedScale_le τ s hs hs1 (B i) m
    have hsz (i : t) (m : ℕ) : (d i).size (B i) q m ≤ (cbase i).sizeFactor q m *
        (c i).norm (B i) (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) := by
      rw [(d i).size_eq_factor]
      exact mul_le_mul_of_nonneg_left (hnorm i _) ((cbase i).sizeFactor_nonneg q m)
    have hres (i : t) (m : ℕ) : (d i).residual (B i) q m ≤ (τ/s)^(q+1) *
        ((cbase i).residualFactor q m *
          (c i).norm (B i) (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m)) := by
      rw [(d i).residual_eq_factor]
      simp only [zero_div,add_zero]
      calc
        _ ≤ (τ/s)^(q+1) * (cbase i).residualFactor q m *
            (c i).norm (B i) (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m) :=
          mul_le_mul_of_nonneg_left (hnorm i _)
            (mul_nonneg (pow_nonneg (div_nonneg hτ.le hs.le) _) ((cbase i).residualFactor_nonneg q m))
        _ = _ := mul_assoc _ _ _
    have hdisp (x : SmallModes.Base) :
        ∑ i : t, QuadraticMean.displacement τ (coordinatePhase φ) (B i) x =
          QuadraticMean.displacement τ (coordinatePhase φ) A x := by
      simp only [QuadraticMean.displacement]
      rw [← QuadraticMean.realMode_sum,hsum]
    refine ⟨X,hX,?_,?_,?_⟩
    · intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hsp hx)
      exact hLK i hi
    · intro m
      exact (hb m).mono_const (Finset.sum_le_sum (fun i _ => hsz i m))
    · intro m
      have hbound : (∑ i : t, (d i).residual (B i) q m) ≤ (τ/s)^(q+1) * D m := by
        calc
          _ ≤ ∑ i : t, (τ/s)^(q+1) * ((cbase i).residualFactor q m *
              (c i).norm (B i) (PolynomialSolveData.inputOrder (P := emptyMetricPolynomial) q m)) :=
            Finset.sum_le_sum (fun i _ => hres i m)
          _ = _ := (Finset.mul_sum _ _ _).symm
      simpa only [coordinateFullLinearized_unperturbed,hdisp,Pi.add_def] using (hr m).mono_const hbound

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
