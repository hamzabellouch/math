import OAI.Analysis.IrrationalRotation.Rotation.DiagonalGauge
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Invariant233.DiagonalGauge

theorem fiberOperator_single (t : Circle) (k : ℤ) (c : ℂ) :
    fiberOperator t (lp.single 2 k c) = fourier k t • (lp.single 2 k c : Fiber) := by
  apply lp.ext
  funext j
  change fourier j t * (lp.single 2 k c : Fiber) j =
    fourier k t * (lp.single 2 k c : Fiber) j
  by_cases hj : j = k
  · subst j; rfl
  · simp [lp.single_apply, hj]

theorem fiberOperator_default_basis (t : Circle) (k : ℤ) :
    fiberOperator t ((default : HilbertBasis ℤ ℂ Fiber) k) =
      fourier k t • ((default : HilbertBasis ℤ ℂ Fiber) k) := by
  have hb : (default : HilbertBasis ℤ ℂ Fiber) k =
      (lp.single 2 k (1 : ℂ) : Fiber) :=
    (HilbertBasis.repr_symm_single (default : HilbertBasis ℤ ℂ Fiber) k).symm
  rw [hb]
  exact fiberOperator_single t k 1

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem fieldOperator_indicator (t : Circle) (s : Set X)
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (v : Fiber) :
    fieldOperator μ t (indicatorConstLp 2 hs hμs v) =
      indicatorConstLp 2 hs hμs (fiberOperator t v) := by
  apply Lp.ext
  filter_upwards [fieldOperator_ae μ t (indicatorConstLp 2 hs hμs v),
    (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := v)),
    (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs)
      (c := fiberOperator t v))] with x hf hx hy
  rw [hf, hx, hy]
  by_cases hxs : x ∈ s <;> simp [hxs]

theorem fieldOperator_indicator_single (t : Circle) (s : Set X)
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (k : ℤ) (c : ℂ) :
    fieldOperator μ t (indicatorConstLp 2 hs hμs (lp.single 2 k c : Fiber)) =
      fourier k t • indicatorConstLp 2 hs hμs (lp.single 2 k c : Fiber) := by
  rw [fieldOperator_indicator, fiberOperator_single]
  apply Lp.ext
  filter_upwards
    [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs)
      (c := fourier k t • (lp.single 2 k c : Fiber)),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs)
      (c := (lp.single 2 k c : Fiber)),
    Lp.coeFn_smul (fourier k t) (indicatorConstLp 2 hs hμs (lp.single 2 k c : Fiber))]
    with x hleft hbase hright
  rw [hleft, hright]
  change s.indicator (fun _ => fourier k t • (lp.single 2 k c : Fiber)) x =
    fourier k t • indicatorConstLp 2 hs hμs (lp.single 2 k c : Fiber) x
  rw [hbase]
  by_cases hxs : x ∈ s <;> simp [hxs]

theorem fieldOperator_indicator_basis (t : Circle) (s : Set X)
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (k : ℤ) :
    fieldOperator μ t (indicatorConstLp 2 hs hμs ((default : HilbertBasis ℤ ℂ Fiber) k)) =
      fourier k t • indicatorConstLp 2 hs hμs ((default : HilbertBasis ℤ ℂ Fiber) k) := by
  have hb : (default : HilbertBasis ℤ ℂ Fiber) k =
      (lp.single 2 k (1 : ℂ) : Fiber) :=
    (HilbertBasis.repr_symm_single (default : HilbertBasis ℤ ℂ Fiber) k).symm
  rw [hb]
  exact fieldOperator_indicator_single μ t s hs hμs k 1

theorem fourier_neg_parameter (k : ℤ) (t : Circle) :
    fourier k (-t) = star (fourier k t) := by
  simp only [fourier_apply, smul_neg, fourier_neg', Complex.star_def]

theorem inner_conjugate_of_eigenvectors
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (v w : Lp Fiber 2 μ)
    (j k : ℤ)
    (hv : ∀ t : Circle, fieldOperator μ t v = fourier j t • v)
    (hw : ∀ t : Circle, fieldOperator μ t w = fourier k t • w)
    (t : Circle) :
    inner ℂ w (conjugate μ A t v) = fourier (k-j) t * inner ℂ w (A v) := by
  change inner ℂ w (fieldOperator μ t (A (fieldOperator μ (-t) v))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left, fieldOperator_adjoint,
    hw, hv, map_smul, inner_smul_left, inner_smul_right]
  have hchar : star (fourier k (-t)) * fourier j (-t) = fourier (k-j) t := by
    rw [fourier_neg_parameter, star_star, fourier_neg_parameter]
    rw [sub_eq_add_neg, fourier_add, fourier_neg]
    rfl
  change star (fourier k (-t)) * (fourier j (-t) * inner ℂ w (A v)) = _
  rw [← mul_assoc, hchar]

theorem inner_conjugate_indicator_basis
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ)
    (s u : Set X) (hs : MeasurableSet s) (hu : MeasurableSet u)
    (hμs : μ s ≠ ∞) (hμu : μ u ≠ ∞) (j k : ℤ) (t : Circle) :
    inner ℂ (indicatorConstLp 2 hu hμu ((default : HilbertBasis ℤ ℂ Fiber) k))
      (conjugate μ A t (indicatorConstLp 2 hs hμs ((default : HilbertBasis ℤ ℂ Fiber) j))) =
      fourier (k-j) t * inner ℂ
        (indicatorConstLp 2 hu hμu ((default : HilbertBasis ℤ ℂ Fiber) k))
        (A (indicatorConstLp 2 hs hμs ((default : HilbertBasis ℤ ℂ Fiber) j))) :=
  inner_conjugate_of_eigenvectors μ A _ _ j k
    (fun t => fieldOperator_indicator_basis μ t s hs hμs j)
    (fun t => fieldOperator_indicator_basis μ t u hu hμu k) t

end Invariant233.DiagonalGauge

end

end OAI
