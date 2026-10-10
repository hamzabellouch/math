import OAI.Geometry.SurfaceImmersion.Atlas.GridPhaseCutoffs
import OAI.Geometry.SurfaceImmersion.Atlas.ChartedPartitionLeading

namespace OAI

/-! The leading tensor of all cell phases is exactly the original chart
weight squared times the input tensor. No cardinality-dependent loss occurs. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.PhaseGrid
open JetPolynomial

lemma supportedCellCutoff_square_sum {K : Compacts Base}
    (f : SupportedField (F := ℝ) K) {a : Finset Index} {h : ℝ}
    (hh : 0 < h) (hK : (K : Set Base) ⊆ coverRegion a h) (x : Base) :
    (∑ k : a, (supportedCellCutoff f hh hK k.val x)^2) = (f x)^2 := by
  classical
  by_cases hf : f x = 0
  · simp [supportedCellCutoff_apply,hf]
  have hxK : x ∈ (K : Set Base) := by
    by_contra hx
    exact hf (by simpa only [Pi.zero_apply] using f.zero_on_compl hx)
  have hsum := normalizedCutoff_squares
    (zero_lt_one.trans_le (squareSum_ge_one hh (coverRegion_covers a h (hK hxK))))
  have hco : (∑ k : a, (normalizedCutoff a h k.val x)^2) =
      ∑ k ∈ a, (normalizedCutoff a h k x)^2 :=
    Finset.sum_coe_sort a (fun k => (normalizedCutoff a h k x)^2)
  simp only [supportedCellCutoff_apply,mul_pow]
  rw [← Finset.mul_sum,hco,hsum,mul_one]

end ClosedSurfaceR4.PhaseGrid

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean PhaseGeometry RealModes FiniteMean PhaseGrid

theorem charted_grid_partition_leading {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {ε τ : ℝ} {G : Base → Space} {hG : ContDiff ℝ ∞ G}
    {a : Finset Index} {h : ℝ} {K₀ : Compacts SmallModes.Base}
    (χ : SupportedField (F := ℝ) K₀) (hh : 0 < h)
    (hK₀ : (K₀ : Set SmallModes.Base) ⊆ coverRegion a h)
    {φ : a → Fin 3 → Base → ℝ} {K : a → Fin 3 → Compacts Base} {s : ℝ≥0}
    {c : ∀ k j, PolynomialSolveData P ε G hG (φ k j) (K k j) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ∀ k j, ChartedMeanData (c k j) r ρ R reference) (hρ : 0 < ρ)
    (Q : a → PhaseBasis) (w : a → Fin 3 → ℝ)
    (hw : ∀ k j, w k j ≠ 0)
    (hphase : ∀ k j, coordinatePhase (φ k j) = phaseLinear (w k j • (Q k).ξ j))
    (hcutoff : ∀ k j x, x ∈ (c k j).e.source →
      (d k j).cutoff ((c k j).e x) = supportedCellCutoff χ hh hK₀ k.val x / w k j)
    (hform : ∀ k j x, x ∈ (c k j).e.source → (d k j).form ((c k j).e x) = (Q k).Q j)
    (hsupport : ∀ k j, tsupport (supportedCellCutoff χ hh hK₀ k.val) ⊆ (c k j).e.source)
    {A : SmallModes.Base → Tensor} (hA : ContDiff ℝ ∞ A)
    (hball : InTrialBall univ reference r A) :
    chartedFamilyLeading (fun t : a × Fin 3 => d t.1 t.2) hρ A =
      fun x => (χ x)^2 • A x := by
  classical
  have hcell (k : a) := charted_partition_leading (d k) hρ
    (supportedCellCutoff χ hh hK₀ k.val) (Q k) (w k) (hw k) (hphase k)
    (hcutoff k) (hform k) (hsupport k) hA hball
  funext x
  change (∑ t : a × Fin 3, (d t.1 t.2).leading hρ A x) = _
  rw [Fintype.sum_prod_type]
  simp_rw [show ∀ k : a, (∑ j : Fin 3, (d k j).leading hρ A x) =
    (supportedCellCutoff χ hh hK₀ k.val x)^2 • A x from fun k => congrFun (hcell k) x]
  rw [← Finset.sum_smul,supportedCellCutoff_square_sum]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
