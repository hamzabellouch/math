import OAI.Analysis.LipschitzHilbert.Trees.FourGridBandErrors

namespace OAI

/-! Summing the actual annular packet errors without a scale-count loss. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

def fullBandSum {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (x : ℝ) : ℂ := ∑ j, f j x

def partialBandSum {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (i : ℕ) (x : ℝ) : ℂ :=
  ∑ j, if j.val < i then f j x else 0

namespace FiniteLineGrid

theorem scalarAverage_memLp (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℂ)
    (hf : MemLp f 2 μ) (i : ℕ) : MemLp (g.scalarAverage μ f i) 2 μ := by
  apply memLp_re_im_iff.mp
  constructor
  · convert g.average_memLp μ (fun x => (f x).re) hf.re i using 1
    ext x
    exact scalarAverage_re g μ f i x
  · convert g.average_memLp μ (fun x => (f x).im) hf.im i using 1
    ext x
    exact scalarAverage_im g μ f i x

theorem scalarAverage_fullBandSum {N : ℕ} (g : FiniteLineGrid)
    (f : Fin N → SchwartzMap ℝ ℂ) (i : ℕ) :
    g.scalarAverage g.lineMeasure (fullBandSum f) i =ᵐ[g.lineMeasure]
      fun x => ∑ j, g.scalarAverage g.lineMeasure (f j) i x := by
  have hr : (fun x => (fullBandSum f x).re) = ∑ j, (fun x => (f j x).re) := by
    funext x
    simp only [fullBandSum, Complex.re_sum, Finset.sum_apply]
  have hi : (fun x => (fullBandSum f x).im) = ∑ j, (fun x => (f j x).im) := by
    funext x
    simp only [fullBandSum, Complex.im_sum, Finset.sum_apply]
  have hR := condExp_finsetSum (μ := g.lineMeasure) (s := Finset.univ)
    (fun j _ => (show MemLp (fun x => (f j x).re) 2 g.lineMeasure from
      (schwartz_re_memLp (f j)).restrict g.root).integrable (by norm_num))
    (g.filtration i)
  have hI := condExp_finsetSum (μ := g.lineMeasure) (s := Finset.univ)
    (fun j _ => (show MemLp (fun x => (f j x).im) 2 g.lineMeasure from
      (schwartz_im_memLp (f j)).restrict g.root).integrable (by norm_num))
    (g.filtration i)
  filter_upwards [hR,hI] with x hxR hxI
  apply Complex.ext
  · simp only [Complex.re_sum, scalarAverage_re, average, hr]
    simpa only [Finset.sum_apply] using hxR
  · simp only [Complex.im_sum, scalarAverage_im, average, hi]
    simpa only [Finset.sum_apply] using hxI

end FiniteLineGrid

theorem bandErrorAt_memLp (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ) (level i j : ℕ) :
    MemLp (bandErrorAt g f level i j) 2 g.lineMeasure := by
  have hf : MemLp (f : ℝ → ℂ) 2 g.lineMeasure := (f.memLp 2 volume).restrict g.root
  have hav := g.scalarAverage_memLp g.lineMeasure f hf level
  by_cases hji : j < i
  · convert hf.sub hav using 1
    ext x
    simp only [bandErrorAt, ite_eq_left hji, Pi.sub_apply]
  · convert hav.neg using 1
    ext x
    simp only [bandErrorAt, ite_eq_right hji, zero_sub, Pi.neg_apply]

theorem bandError_memLp (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ) (i j : ℕ) :
    MemLp (bandError g f i j) 2 g.lineMeasure := bandErrorAt_memLp g f i i j

theorem bandErrorAt_sum {N : ℕ} (g : FiniteLineGrid)
    (f : Fin N → SchwartzMap ℝ ℂ) (level i : ℕ) :
    (fun x => ∑ j, bandErrorAt g (f j) level i j.val x) =ᵐ[g.lineMeasure]
      fun x => partialBandSum f i x - g.scalarAverage g.lineMeasure (fullBandSum f) level x := by
  filter_upwards [g.scalarAverage_fullBandSum f level] with x hx
  simp only [bandErrorAt, Finset.sum_sub_distrib, partialBandSum, hx]

theorem bandError_sum {N : ℕ} (g : FiniteLineGrid)
    (f : Fin N → SchwartzMap ℝ ℂ) (i : ℕ) :
    (fun x => ∑ j, bandError g (f j) i j.val x) =ᵐ[g.lineMeasure]
      fun x => partialBandSum f i x - g.scalarAverage g.lineMeasure (fullBandSum f) i x :=
  bandErrorAt_sum g f i i

theorem geometric_square_comparison {N : ℕ} (g : FiniteLineGrid) (offset : ℕ)
    (f : Fin N → SchwartzMap ℝ ℂ)
    (hlow : ∀ j ξ, |ξ| < bandInner j.val → 𝓕 (f j) ξ = 0)
    (hhigh : ∀ j ξ, bandOuter j.val < |ξ| → 𝓕 (f j) ξ = 0)
    (hdepth : offset + N ≤ g.depth)
    (hmesh : ∀ i, g.meshWidth (offset + i) = ((4 : ℝ) ^ i)⁻¹) :
    (∑ i : Fin (N + 1), ∫ x,
      ‖partialBandSum f i.val x -
        g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i.val) x‖ ^ 2
        ∂g.lineMeasure) ≤
      256 * ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
  have h := finite_energy_schur g.lineMeasure
    (fun (i : Fin (N + 1)) (j : Fin N) => bandErrorAt g (f j) (offset + i.val) i.val j.val)
    (fun i j => bandErrorAt_memLp g (f j) (offset + i.val) i.val j.val)
    (fun i j => scaleWeight i.val j.val) (fun i j => scaleWeight_pos i.val j.val)
    (fun j => ∫ x, ‖f j x‖ ^ 2) (fun j => integral_nonneg (fun _ => sq_nonneg _))
    (R := 16) (C := 16) (by norm_num)
    (fun i => scaleWeight_sum N i.val) (fun j => scaleWeight_sum_column (N + 1) j.val)
    (fun i j => geometric_band_error g (f j) j.val (hlow j) (hhigh j)
      (by have := i.isLt; omega) (hmesh i.val))
  have heq : (∑ i : Fin (N + 1), ∫ x,
      ‖∑ j, bandErrorAt g (f j) (offset + i.val) i.val j.val x‖ ^ 2 ∂g.lineMeasure) =
      ∑ i : Fin (N + 1), ∫ x,
      ‖partialBandSum f i.val x - g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i.val) x‖ ^ 2
        ∂g.lineMeasure := by
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [bandErrorAt_sum g f (offset + i.val) i.val] with x hx
    rw [hx]
  rw [heq] at h
  norm_num only [show (16 : ℝ) * 16 = 256 by norm_num] at h
  exact h


theorem fourGrid_square_comparison {N : ℕ} (origin : ℝ)
    (f : Fin N → SchwartzMap ℝ ℂ)
    (hlow : ∀ j ξ, |ξ| < bandInner j.val → 𝓕 (f j) ξ = 0)
    (hhigh : ∀ j ξ, bandOuter j.val < |ξ| → 𝓕 (f j) ξ = 0) :
    (∑ i : Fin (N + 1), ∫ x,
      ‖partialBandSum f i.val x -
        (fourGrid origin N).scalarAverage (fourGrid origin N).lineMeasure (fullBandSum f) i.val x‖ ^ 2
        ∂(fourGrid origin N).lineMeasure) ≤
      256 * ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
  simpa only [Nat.zero_add] using geometric_square_comparison (fourGrid origin N) 0 f hlow hhigh
    (by simp [fourGrid]) (fun i => by simpa only [Nat.zero_add] using fourGrid_mesh origin N i)

end LipschitzHilbert

end

end OAI
