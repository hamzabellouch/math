import OAI.Geometry.SurfaceImmersion.Geometry.TransverseFinitePatching
import OAI.Geometry.SurfaceImmersion.Geometry.SupportedScalarQuotient

namespace OAI

/-! Prescribe a transverse derivative using actual defining functions and smooth cutoffs. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.TransverseSmallFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

theorem exists_prescribed_transverse_derivative
    {f χ : ι → E → ℝ} {T : E → ℝ} {K : Set E} (v : E)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hχc : ∀ i, HasCompactSupport (χ i)) (hT : ContDiff ℝ ∞ T)
    (hden : ∀ i x, x ∈ tsupport (χ i) → fderiv ℝ (f i) x v ≠ 0)
    (hzero : ∀ i x, x ∈ K → x ∈ tsupport (χ i) → f i x = 0)
    (hpartition : ∀ x ∈ K, T x ≠ 0 → (∑ i, χ i x) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H : E → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ ⋃ i, tsupport (χ i) ∧ (∀ x, |H x| < ε) ∧
      ∀ x ∈ K, fderiv ℝ H x v = T x := by
  let d : ι → E → ℝ := fun i x => fderiv ℝ (f i) x v
  let g : ι → E → ℝ := fun i x => (χ i x * T x) / d i x
  have hd (i : ι) : ContDiff ℝ ∞ (d i) :=
    ((hf i).fderiv_right (by simp)).clm_apply contDiff_const
  have hsupp (i : ι) : tsupport (g i) ⊆ tsupport (χ i) := by
    exact (supported_quotient_support (fun x => χ i x * T x) (d i)).trans
      tsupport_mul_subset_left
  have hg (i : ι) : ContDiff ℝ ∞ (g i) := by
    apply supported_quotient_smooth ((hχ i).mul hT) (hd i)
    intro x hx
    exact hden i x (tsupport_mul_subset_left hx)
  have hgc (i : ι) : HasCompactSupport (g i) :=
    supported_quotient_compact (hχc i |>.mul_right)
  have hcoef (i : ι) (x : E) : g i x * d i x = χ i x * T x := by
    exact supported_quotient_cancel (χ := fun y => χ i y * T y) (d := d i)
      (fun y hy => hden i y (tsupport_mul_subset_left hy)) x
  obtain ⟨H, hH, hHc, hHs, hHsmall, hHd⟩ := finite_small_correction hf hg hgc
    (fun i x hx hs => hzero i x hx (hsupp i hs)) hε
  refine ⟨H, hH, hHc, hHs.trans (iUnion_mono hsupp), hHsmall, ?_⟩
  intro x hx
  rw [hHd x hx]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  change (∑ i, g i x * d i x) = T x
  simp_rw [hcoef]
  rw [← Finset.sum_mul]
  by_cases hTx : T x = 0
  · simp [hTx]
  · rw [hpartition x hx hTx, one_mul]

end ClosedSurfaceR4.TransverseSmallFunction

end

end OAI
