import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace Invariant233.FieldTraceFaithfulness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem apply_eq_zero_of_re_inner_eq_zero {T : E →L[ℂ] E}
    (hT : T.IsPositive) {x : E} (hx : (inner ℂ (T x) x).re = 0) : T x = 0 := by
  let R := CFC.sqrt T
  have hR : R.IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)
  have hRR : R * R = T := CFC.sqrt_mul_sqrt_self T
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT)
  have hnorm : ‖R x‖ ^ 2 = 0 := by
    rw [R.apply_norm_sq_eq_inner_adjoint_left, (ContinuousLinearMap.isSelfAdjoint_iff'.mp hR.isSelfAdjoint)]
    change (inner ℂ ((R * R) x) x).re = 0
    rw [hRR]
    exact hx
  have hRx : R x = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  rw [← hRR]
  change R (R x) = 0
  simp [hRx]

theorem eq_zero_of_re_diagonal_eq_zero {ι : Type*} (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive)
    (hdiag : ∀ i, (inner ℂ (T (b i)) (b i)).re = 0) : T = 0 := by
  have hb : ∀ i, T (b i) = 0 := fun i =>
    apply_eq_zero_of_re_inner_eq_zero hT (hdiag i)
  ext x
  have hsum := T.hasSum (b.hasSum_repr x)
  simp only [map_smul, hb, smul_zero] at hsum
  exact hsum.unique hasSum_zero

theorem ae_eq_zero_of_integral_diagonal_eq_zero
    {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (b : HilbertBasis ι ℂ E) (i₀ : ι)
    (H : X → E →L[ℂ] E) (σ : ι → X → X)
    (hσ : ∀ i, MeasurePreserving (σ i) μ μ)
    (hpos : ∀ᵐ x ∂μ, (H x).IsPositive)
    (hcov : ∀ i, ∀ᵐ x ∂μ,
      (inner ℂ (H x (b i)) (b i)).re =
        (inner ℂ (H (σ i x) (b i₀)) (b i₀)).re)
    (hint : Integrable (fun x => (inner ℂ (H x (b i₀)) (b i₀)).re) μ)
    (htrace : ∫ x, (inner ℂ (H x (b i₀)) (b i₀)).re ∂μ = 0) :
    H =ᵐ[μ] 0 := by
  have hnonneg : 0 ≤ᵐ[μ] fun x => (inner ℂ (H x (b i₀)) (b i₀)).re := by
    filter_upwards [hpos] with x hx
    exact hx.re_inner_nonneg_left _
  have hzero : ∀ᵐ x ∂μ, (inner ℂ (H x (b i₀)) (b i₀)).re = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp htrace
  have hall : ∀ i, ∀ᵐ x ∂μ, (inner ℂ (H x (b i)) (b i)).re = 0 := by
    intro i
    filter_upwards [hcov i, (hσ i).quasiMeasurePreserving.ae hzero] with x hcovx hzerox
    exact hcovx.trans hzerox
  filter_upwards [hpos, ae_all_iff.mpr hall] with x hposx hdiagx
  exact eq_zero_of_re_diagonal_eq_zero b hposx hdiagx

end Invariant233.FieldTraceFaithfulness

end

end OAI
