import Mathlib
import OAI.Analysis.CoulombIonization.Variational.RootCoulomb

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
namespace CoulombAtom
section SliceLp
variable {E F : Type*} [MeasureSpace E] [MeasureSpace F]
  [SFinite (volume : Measure E)] [SFinite (volume : Measure F)]

lemma memLp_slice_left {f : E × F → ℂ} (hf : MemLp f 2) :
    ∀ᵐ y, MemLp (fun x => f (x, y)) 2 := by
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  filter_upwards [hf.aestronglyMeasurable.prodMk_right, hi.prod_left_ae] with y hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hi

end SliceLp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]
  [MeasureSpace F] [SFinite (volume : Measure F)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [IsLocallyFiniteMeasure (volume : Measure E)] in
lemma integral_pair_norm_sq {f : E → ℂ} (hf : MemLp f 2)
    (φ : E → ℝ) (hφ : MemLp (fun x => (φ x : ℂ)) 2) :
    ‖∫ x, f x * (φ x : ℂ)‖ ^ 2 ≤
      ‖hφ.toLp (fun x => (φ x : ℂ))‖ ^ 2 * ∫ x, ‖f x‖ ^ 2 := by
  have he : (∫ x, f x * (φ x : ℂ)) = l2Test φ hφ (hf.toLp f) := by
    rw [l2Test_apply]
    exact integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by rw [hx]) |>.symm
  rw [he]
  have h := norm_inner_le_norm (𝕜 := ℂ) (hφ.toLp (fun x => (φ x : ℂ))) (hf.toLp f)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow, lp_norm_sq (hf.toLp f)] at hs
  have hi : (∫ x, ‖hf.toLp f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 :=
    integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by simp only [hx])
  rw [hi] at hs
  exact hs

omit [BorelSpace E] in
lemma partial_pairing_memLp {f : E × F → ℂ} (hf : MemLp f 2)
    (φ : E → ℝ) (hφ : MemLp (fun x => (φ x : ℂ)) 2) :
    MemLp (fun y => ∫ x, f (x, y) * (φ x : ℂ)) 2 := by
  have hm : AEStronglyMeasurable (fun y => ∫ x, f (x, y) * (φ x : ℂ)) := by
    exact (hf.aestronglyMeasurable.mul (hφ.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst)
      )).prod_swap.integral_prod_right'
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  apply (hi.integral_prod_right.const_mul
    (‖hφ.toLp (fun x => (φ x : ℂ))‖ ^ 2)).mono'
      (hm.norm.pow 2)
  filter_upwards [memLp_slice_left hf] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact integral_pair_norm_sq hy φ hφ

end CoulombAtom

end

end OAI
