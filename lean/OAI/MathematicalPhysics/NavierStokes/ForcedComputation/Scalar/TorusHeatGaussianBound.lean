import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatLattice
import Mathlib.Analysis.SumIntegralComparisons

namespace OAI

/-! Elementary lattice estimates for the two-dimensional torus heat kernel. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory
open scoped BigOperators

theorem gaussian_nat_tsum_le {b : ℝ} (hb : 0 < b) :
    (∑' n : ℕ, Real.exp (-b * (n : ℝ) ^ 2)) ≤ 1 + Real.sqrt (Real.pi / b) := by
  have ha : AntitoneOn (fun x : ℝ => Real.exp (-b * x ^ 2)) (Ici 0) := by
    intro x hx y hy hxy
    apply Real.exp_le_exp.mpr
    have hs := (sq_le_sq₀ hx hy).mpr hxy
    nlinarith
  have hi := integrable_exp_neg_mul_sq hb
  have hh := ha.tsum_le_integral hi.integrableOn (fun x _ => (Real.exp_pos _).le)
  rw [integral_gaussian_Ioi] at hh
  simp only [zero_pow two_ne_zero, mul_zero, Real.exp_zero] at hh
  have hs : 0 ≤ Real.sqrt (Real.pi / b) := Real.sqrt_nonneg _
  linarith

theorem gaussianLattice_add_int (t x : ℝ) (m : ℤ) :
    gaussianLattice t (x + m) = gaussianLattice t x := by
  unfold gaussianLattice
  have h := (Equiv.addRight m).tsum_eq
    (fun n : ℤ => Real.exp (-((x + (n : ℝ)) ^ 2) / (4 * t)))
  convert h using 1
  apply tsum_congr
  intro n
  simp only [Equiv.coe_addRight, Int.cast_add]
  congr 2
  ring

theorem gaussianLattice_neg (t x : ℝ) : gaussianLattice t (-x) = gaussianLattice t x := by
  unfold gaussianLattice
  have h := (Equiv.neg ℤ).tsum_eq
    (fun n : ℤ => Real.exp (-((x + (n : ℝ)) ^ 2) / (4 * t)))
  convert h using 1
  apply tsum_congr
  intro n
  simp only [Equiv.neg_apply, Int.cast_neg]
  congr 2
  ring

theorem gaussianLattice_abs (t x : ℝ) : gaussianLattice t |x| = gaussianLattice t x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, gaussianLattice_neg]

theorem gaussian_nat_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => Real.exp (-((n : ℝ) ^ 2) / (4 * t))) := by
  have h := (gaussianLattice_summable ht 0).comp_injective
    (show Function.Injective (fun n : ℕ => (n : ℤ)) from Int.ofNat_injective)
  simpa only [Function.comp_def, zero_add, Int.cast_natCast] using h

theorem gaussian_nat_scaled_le {t : ℝ} (ht : 0 < t) :
    (∑' n : ℕ, Real.exp (-((n : ℝ) ^ 2) / (4 * t))) ≤
      1 + Real.sqrt (4 * Real.pi * t) := by
  have h := gaussian_nat_tsum_le (b := (4 * t)⁻¹) (by positivity)
  have he (x : ℝ) : -(4 * t)⁻¹ * x ^ 2 = -(x ^ 2) / (4 * t) := by ring
  have hs : Real.pi / (4 * t)⁻¹ = 4 * Real.pi * t := by rw [div_inv_eq_mul]; ring
  simpa only [he, hs] using h

theorem gaussianLattice_centered_le {t r : ℝ} (ht : 0 < t)
    (hr : 0 ≤ r) (hr' : r ≤ 1 / 2) :
    gaussianLattice t r ≤ 2 * (1 + Real.sqrt (4 * Real.pi * t)) *
      Real.exp (-(r ^ 2) / (4 * t)) := by
  let fp := fun n : ℕ => Real.exp (-((r + (n : ℝ)) ^ 2) / (4 * t))
  let fm := fun n : ℕ => Real.exp (-((r - ((n : ℝ) + 1)) ^ 2) / (4 * t))
  let u := fun n : ℕ => Real.exp (-(r ^ 2) / (4 * t)) *
    Real.exp (-((n : ℝ) ^ 2) / (4 * t))
  have hu : Summable u := (gaussian_nat_summable ht).mul_left _
  have hbound (s : ℝ) (n : ℕ) (hs : r ^ 2 + (n : ℝ) ^ 2 ≤ s ^ 2) :
      Real.exp (-(s ^ 2) / (4 * t)) ≤ u n := by
    dsimp only [u]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ (-(r ^ 2) - (n : ℝ) ^ 2) / (4 * t) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  have hfp (n : ℕ) : fp n ≤ u n := by
    apply hbound
    nlinarith [mul_nonneg hr (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hfm (n : ℕ) : fm n ≤ u n := by
    apply hbound
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hnr : 0 ≤ (n : ℝ) * (1 - r) := mul_nonneg hn (by linarith)
    nlinarith
  have hp : Summable fp := hu.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hfp
  have hm : Summable fm := hu.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hfm
  have he : gaussianLattice t r = (∑' n, fp n) + ∑' n, fm n := by
    calc
      gaussianLattice t r = ∑' n : ℤ, Int.rec fp fm n := by
        apply tsum_congr
        intro n
        cases n with
        | ofNat n => simp only [fp, Int.ofNat_eq_natCast, Int.cast_natCast]
        | negSucc n =>
          simp only [fm, Int.cast_negSucc]
          push_cast
          congr 2
      _ = _ := (hp.hasSum.int_rec hm.hasSum).tsum_eq
  rw [he]
  calc
    _ ≤ (∑' n, u n) + ∑' n, u n :=
      add_le_add (hp.tsum_le_tsum hfp hu) (hm.tsum_le_tsum hfm hu)
    _ = 2 * Real.exp (-(r ^ 2) / (4 * t)) *
        (∑' n : ℕ, Real.exp (-((n : ℝ) ^ 2) / (4 * t))) := by
      dsimp only [u]
      rw [tsum_mul_left]
      ring
    _ ≤ 2 * Real.exp (-(r ^ 2) / (4 * t)) *
        (1 + Real.sqrt (4 * Real.pi * t)) :=
      mul_le_mul_of_nonneg_left (gaussian_nat_scaled_le ht) (by positivity)
    _ = _ := by ring

theorem gaussianLattice_nearest_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    gaussianLattice t x ≤ 2 * (1 + Real.sqrt (4 * Real.pi * t)) *
      Real.exp (-((x - (⌊x + 1 / 2⌋ : ℤ)) ^ 2) / (4 * t)) := by
  let m : ℤ := ⌊x + 1 / 2⌋
  let r : ℝ := x - (m : ℝ)
  have hrl : -(1 / 2 : ℝ) ≤ r := by
    have h := Int.floor_le (x + 1 / 2)
    dsimp only [r, m]
    linarith
  have hru : r ≤ (1 / 2 : ℝ) := by
    have h := Int.lt_floor_add_one (x + 1 / 2)
    dsimp only [r, m]
    linarith
  have he := gaussianLattice_add_int t r m
  have hx : r + (m : ℝ) = x := by dsimp only [r]; ring
  rw [hx] at he
  rw [he, ← gaussianLattice_abs t r]
  simpa only [sq_abs] using gaussianLattice_centered_le ht (abs_nonneg r)
    (abs_le.mpr ⟨hrl, hru⟩)

theorem gaussianLattice_nonneg (t x : ℝ) : 0 ≤ gaussianLattice t x :=
  tsum_nonneg (fun _ => (Real.exp_pos _).le)

theorem torusHeatKernel_gaussian {t : ℝ} (ht : 0 < t) (x : Plane) :
    torusHeatKernel t x ≤
      4 * (1 + Real.sqrt (1 / (4 * Real.pi * t))) ^ 2 *
        Real.exp (-(torusDistanceSq x) / (4 * t)) := by
  let A := 4 * Real.pi * t
  let S := Real.sqrt A
  let E := fun j : Fin 2 => Real.exp (-((x j - (⌊x j + 1 / 2⌋ : ℤ)) ^ 2) / (4 * t))
  have hA : 0 < A := by dsimp only [A]; positivity
  have hS : 0 < S := Real.sqrt_pos.mpr hA
  have hS2 : S ^ 2 = A := Real.sq_sqrt hA.le
  have hAi : A⁻¹ = S⁻¹ ^ 2 := by rw [← hS2, inv_pow]
  have hSi : Real.sqrt (1 / A) = S⁻¹ := by
    simp only [one_div, Real.sqrt_inv, S]
  have hcoeff : A⁻¹ * (2 * (1 + S)) ^ 2 = 4 * (1 + Real.sqrt (1 / A)) ^ 2 := by
    rw [hAi, hSi]
    field_simp [hS.ne']
    ring
  have hE : E 0 * E 1 = Real.exp (-(torusDistanceSq x) / (4 * t)) := by
    dsimp only [E]
    rw [← Real.exp_add]
    congr 1
    simp only [torusDistanceSq, Fin.sum_univ_two]
    ring
  rw [torusHeatKernel_factor ht]
  change A⁻¹ * (gaussianLattice t (x 0) * gaussianLattice t (x 1)) ≤ _
  calc
    _ ≤ A⁻¹ * ((2 * (1 + S) * E 0) * (2 * (1 + S) * E 1)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hA.le)
      exact mul_le_mul (gaussianLattice_nearest_le ht (x 0))
        (gaussianLattice_nearest_le ht (x 1)) (gaussianLattice_nonneg t (x 1))
        (by dsimp only [S, E]; positivity)
    _ = (A⁻¹ * (2 * (1 + S)) ^ 2) * (E 0 * E 1) := by ring
    _ = _ := by rw [hcoeff, hE]

end ForcedComputation.VelocityDetector

end

end OAI
