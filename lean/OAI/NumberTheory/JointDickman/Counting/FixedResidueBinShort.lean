import OAI.NumberTheory.JointDickman.Counting.FixedResidueEnergy
import OAI.NumberTheory.JointDickman.Counting.PrescribedCenterShort

namespace OAI

/-! # Bin short averages in a residue class with a prescribed fixed divisor -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem fixed_residue_finitePrime_short_with_center
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (μ : ℂ)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    (P : ℕ → Finset ℕ) (hP : ∀ B p, p ∈ P B → p.Prime)
    (t : ℕ → ℕ → ℝ) (ht : ∀ B p, p ∈ P B → 0 ≤ t B p ∧ t B p ≤ 1)
    {d e : ℕ} (hd : 0 < d) [NeZero e] (a : ℕ) (ha : a.Coprime e)
    (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖residueBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (finitePrimeWeight (P B) (t B)) ((d*a : ℕ) : ZMod (d*e)) (H B) z‖^2) < ε := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hH' : Tendsto (fun B => H B/(d : ℝ)) atTop atTop := by
    simpa only [div_eq_mul_inv,mul_comm] using hH.const_mul_atTop (inv_pos.mpr hdR)
  have hu := unit_progressions_short_with_center hMR hMRT hKMT hM hJ ζ μ hmean P hP
    (fun B p => if p ∣ d then 1 else t B p) (fun B => fixedDivisorWeight_bounds (ht B) d)
    (q := e) (fun B => A B/d) scale (fun B => H B/d)
    (fun B => div_pos (hA B) hdR) hscale hH'
  have hbin := hscale.eventually (binLabel_eventually_mul_invariant J hJ
    (fun i : Fin (J-1) => i.val+1) (fun _ => by omega) ζ hd.ne')
  intro ε hε
  filter_upwards [hu ε hε,hH.eventually_gt_atTop 0] with B hB hHB
  have hX := hscale.const_mul_atTop (hA B)
  filter_upwards [hB,hbin,hX.eventually_gt_atTop 0] with n hn hbn hXn
  have he := residueBinAverage_fixed_energy_le
    (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
    (hP B) (t B) (ht B) hd e a hbn hHB hXn
  have hh := hn (ZMod.unitOfCoprime a ha)
  have hxd : A B*scale n/(d : ℝ) = (A B/d)*scale n := by ring
  simp only [hxd] at he
  have hu' : (1/((A B/d)*scale n))*(∫ z in ((A B/d)*scale n)..2*((A B/d)*scale n),
      ‖residueBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
        (finitePrimeWeight (P B) (fun p => if p ∣ d then 1 else t B p)) (a : ZMod e) (H B/d) z‖^2) < ε := by
    simpa only [← residueBinAverage_unit,ZMod.coe_unitOfCoprime] using hh
  exact he.trans_lt hu'

end JointDickman

end OAI
