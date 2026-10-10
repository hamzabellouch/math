import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.Cubature
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Tensorizing the one-dimensional Gauss error without differentiating a
parameter integral. This is used for the transported nuclear cubature. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem gaussTwoPoint_sub (f g : ℝ → ℝ) :
    gaussTwoPoint (fun x => f x-g x) = gaussTwoPoint f-gaussTwoPoint g := by
  unfold gaussTwoPoint
  ring

theorem gaussTwoPoint_comm (f : ℝ → ℝ → ℝ) :
    gaussTwoPoint (fun x => gaussTwoPoint (f x)) =
      gaussTwoPoint (fun y => gaussTwoPoint (fun x => f x y)) := by
  unfold gaussTwoPoint
  ring

theorem gaussTwoPoint_abs_bound (f : ℝ → ℝ) {E : ℝ}
    (h : ∀ x ∈ Set.Icc (-1) 1, |f x| ≤ E) : |gaussTwoPoint f| ≤ 2*E := by
  have hg : gaussAbscissa ≤ 1 := by nlinarith only [gaussAbscissa_sq,gaussAbscissa_pos]
  have hp := gaussAbscissa_pos.le
  have h₁ := h (-gaussAbscissa) ⟨by linarith,by linarith⟩
  have h₂ := h gaussAbscissa ⟨by linarith,hg⟩
  exact (abs_add_le _ _).trans (by linarith)

theorem gaussTwoPoint_integral_comm (f : ℝ → ℝ → ℝ)
    (hf : Continuous f.uncurry) :
    gaussTwoPoint (fun x => ∫ y : ℝ in (-1)..1, f x y) =
      ∫ y : ℝ in (-1)..1, gaussTwoPoint (fun x => f x y) := by
  have hc (x : ℝ) : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
  exact (intervalIntegral.integral_add (hc (-gaussAbscissa) |>.intervalIntegrable _ _)
    (hc gaussAbscissa |>.intervalIntegrable _ _)).symm

theorem gaussTwoPoint_integral_continuous {X : Type*} [TopologicalSpace X] (f : X → ℝ → ℝ)
    (hf : Continuous f.uncurry) :
    Continuous (fun x => ∫ y : ℝ in (-1)..1, f x y) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf _ _

theorem gaussTwoPoint_function_continuous {X : Type*} [TopologicalSpace X] (f : X → ℝ → ℝ)
    (hf : Continuous f.uncurry) : Continuous (fun x => gaussTwoPoint (f x)) :=
  (hf.comp (continuous_id.prodMk continuous_const)).add
    (hf.comp (continuous_id.prodMk continuous_const))

theorem interval_abs_bound {E : ℝ} (f : ℝ → ℝ)
    (h : ∀ x ∈ Set.Icc (-1) 1, |f x| ≤ E) :
    |∫ x : ℝ in (-1)..1, f x| ≤ 2*E := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := f) (a := (-1:ℝ)) (b := 1) (C := E) (fun x hx => by
      have hx' : -1 < x ∧ x ≤ 1 := by
        simpa only [Set.uIoc_of_le (by norm_num : (-1:ℝ) ≤ 1),Set.mem_Ioc] using hx
      simpa only [Real.norm_eq_abs] using h x ⟨hx'.1.le,hx'.2⟩)
  norm_num [Real.norm_eq_abs] at hi
  simpa only [mul_comm] using hi

theorem gaussTensor2_error (f : ℝ → ℝ → ℝ) (hf : Continuous f.uncurry) {E : ℝ}
    (hx : ∀ y ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun x => f x y)-(∫ x : ℝ in (-1)..1, f x y)| ≤ E)
    (hy : ∀ x ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (f x)-(∫ y : ℝ in (-1)..1, f x y)| ≤ E) :
    |gaussTwoPoint (fun x => gaussTwoPoint (f x))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, f x y)| ≤ 4*E := by
  let A := gaussTwoPoint (fun x => gaussTwoPoint (f x))
  let B := ∫ x : ℝ in (-1)..1, gaussTwoPoint (f x)
  let C := ∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, f x y
  have h₁ : |A-B| ≤ 2*E := by
    have hid : A-B = gaussTwoPoint (fun y => gaussTwoPoint (fun x => f x y)-
        (∫ x : ℝ in (-1)..1, f x y)) := by
      rw [gaussTwoPoint_sub,gaussTwoPoint_comm]
      dsimp only [A,B]
      rw [gaussTwoPoint_integral_comm (fun y x => f x y)
        (hf.comp continuous_swap)]
    rw [hid]
    exact gaussTwoPoint_abs_bound _ hx
  have h₂ : |B-C| ≤ 2*E := by
    rw [show B-C = ∫ x : ℝ in (-1)..1,
      gaussTwoPoint (f x)-(∫ y : ℝ in (-1)..1, f x y) from
      (intervalIntegral.integral_sub
        ((gaussTwoPoint_function_continuous f hf).intervalIntegrable _ _)
        ((gaussTwoPoint_integral_continuous f hf).intervalIntegrable _ _)).symm]
    exact interval_abs_bound _ hy
  exact (abs_sub_le A B C).trans (by linarith only [h₁,h₂])

theorem gaussTensor3_first_comm (f : ℝ → ℝ → ℝ → ℝ) :
    gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y))) =
      gaussTwoPoint (fun y => gaussTwoPoint (fun z => gaussTwoPoint (fun x => f x y z))) := by
  unfold gaussTwoPoint
  ring

theorem gaussTensor2_integral_comm (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) :
    gaussTwoPoint (fun y => gaussTwoPoint (fun z => ∫ x : ℝ in (-1)..1, f x y z)) =
      ∫ x : ℝ in (-1)..1, gaussTwoPoint (fun y => gaussTwoPoint (f x y)) := by
  have hz (y : ℝ) : Continuous (fun p : ℝ × ℝ => f p.2 y p.1) :=
    hf.comp (show Continuous (fun p : ℝ × ℝ => (p.2,y,p.1)) by fun_prop)
  have hg : Continuous (fun p : ℝ × ℝ => gaussTwoPoint (f p.2 p.1)) := by
    unfold gaussTwoPoint
    exact (hf.comp (show Continuous (fun p : ℝ × ℝ => (p.2,p.1,-gaussAbscissa)) by fun_prop)).add
      (hf.comp (show Continuous (fun p : ℝ × ℝ => (p.2,p.1,gaussAbscissa)) by fun_prop))
  calc
    _ = gaussTwoPoint (fun y => ∫ x : ℝ in (-1)..1, gaussTwoPoint (f x y)) := by
      congr 1
      funext y
      exact gaussTwoPoint_integral_comm _ (hz y)
    _ = _ := gaussTwoPoint_integral_comm _ hg

theorem gaussTensor3_error (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) {E : ℝ}
    (hx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun x => f x y z)-(∫ x : ℝ in (-1)..1, f x y z)| ≤ E)
    (hy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (fun y => f x y z)-(∫ y : ℝ in (-1)..1, f x y z)| ≤ E)
    (hz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      |gaussTwoPoint (f x y)-(∫ z : ℝ in (-1)..1, f x y z)| ≤ E) :
    |gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y)))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z)| ≤ 12*E := by
  let A := gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y)))
  let B := ∫ x : ℝ in (-1)..1, gaussTwoPoint (fun y => gaussTwoPoint (f x y))
  let C := ∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z
  have h₁ : |A-B| ≤ 4*E := by
    have hid : A-B = gaussTwoPoint (fun y => gaussTwoPoint (fun z =>
        gaussTwoPoint (fun x => f x y z)-(∫ x : ℝ in (-1)..1, f x y z))) := by
      simp_rw [gaussTwoPoint_sub]
      rw [gaussTensor2_integral_comm f hf,← gaussTensor3_first_comm]
    rw [hid]
    have h := gaussTwoPoint_abs_bound _ (fun y hy' => gaussTwoPoint_abs_bound _ (hx y hy'))
    convert h using 1
    ring
  have hg : Continuous (fun p : ℝ × ℝ => gaussTwoPoint (f p.1 p.2)) := by
    unfold gaussTwoPoint
    exact (hf.comp (show Continuous (fun p : ℝ × ℝ => (p.1,p.2,-gaussAbscissa)) by fun_prop)).add
      (hf.comp (show Continuous (fun p : ℝ × ℝ => (p.1,p.2,gaussAbscissa)) by fun_prop))
  have hI : Continuous (fun p : ℝ × ℝ => ∫ z : ℝ in (-1)..1, f p.1 p.2 z) :=
    gaussTwoPoint_integral_continuous (fun (p : ℝ × ℝ) z => f p.1 p.2 z)
      (hf.comp (show Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1,p.1.2,p.2)) by fun_prop))
  have h₂ : |B-C| ≤ 8*E := by
    have hb := gaussTwoPoint_function_continuous (fun x y => gaussTwoPoint (f x y)) hg
    have hc := gaussTwoPoint_integral_continuous
      (fun x y => ∫ z : ℝ in (-1)..1, f x y z) hI
    rw [show B-C = ∫ x : ℝ in (-1)..1,
      gaussTwoPoint (fun y => gaussTwoPoint (f x y))-
        (∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z) from
      (intervalIntegral.integral_sub (hb.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm]
    have h := interval_abs_bound _ (fun x hx' =>
      gaussTensor2_error (f x)
        (hf.comp (show Continuous (fun p : ℝ × ℝ => (x,p.1,p.2)) by fun_prop)) (hy x hx') (hz x hx'))
    convert h using 1
    ring
  exact (abs_sub_le A B C).trans (by linarith only [h₁,h₂])

theorem gaussTensor3_C4_error (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) {C : ℝ} (hC : 0 ≤ C)
    (hfx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      ContDiffOn ℝ 4 (fun x => f x y z) (Set.Icc (-1) 1))
    (hfy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      ContDiffOn ℝ 4 (fun y => f x y z) (Set.Icc (-1) 1))
    (hfz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      ContDiffOn ℝ 4 (f x y) (Set.Icc (-1) 1))
    (hCx : ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1, ∀ x ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 (fun x => f x y z) (Set.Icc (-1) 1) x‖ ≤ C)
    (hCy : ∀ x ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 (fun y => f x y z) (Set.Icc (-1) 1) y‖ ≤ C)
    (hCz : ∀ x ∈ Set.Icc (-1) 1, ∀ y ∈ Set.Icc (-1) 1, ∀ z ∈ Set.Icc (-1) 1,
      ‖iteratedDerivWithin 4 (f x y) (Set.Icc (-1) 1) z‖ ≤ C) :
    |gaussTwoPoint (fun x => gaussTwoPoint (fun y => gaussTwoPoint (f x y)))-
      (∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1, f x y z)| ≤ 128*C := by
  have h := gaussTensor3_error f hf
    (fun y hy z hz => gaussTwoPoint_C4_error _ hC (hfx y hy z hz) (hCx y hy z hz))
    (fun x hx z hz => gaussTwoPoint_C4_error _ hC (hfy x hx z hz) (hCy x hx z hz))
    (fun x hx y hy => gaussTwoPoint_C4_error _ hC (hfz x hx y hy) (hCz x hx y hy))
  convert h using 1
  ring

end ContinuumCoulomb

end

end OAI
