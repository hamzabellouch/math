import OAI.NumberTheory.JointDickman.Counting.CoarseBinShort
import OAI.NumberTheory.JointDickman.Counting.FixedResidueEnergy
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeFeatureInvariance
import OAI.NumberTheory.JointDickman.Arithmetic.ResidueDivisorRepresentation

namespace OAI

/-! # Coarse-feature cancellation in every residue class -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem fixed_residue_coarse_short_with_center
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) (b : Fin m)
    {d e : ℕ} (hd : 0 < d) [NeZero e] (a : ℕ) (ha : a.Coprime e)
    (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖residueBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b))
          ((d*a : ℕ) : ZMod (d*e)) (H B) z‖^2) < ε := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hH' : Tendsto (fun B => H B/(d : ℝ)) atTop atTop := by
    simpa only [div_eq_mul_inv,mul_comm] using hH.const_mul_atTop (inv_pos.mpr hdR)
  have hu := unit_coarse_short_with_center hMR hMRT hKMT hM hSD hSW hMP hJ ζ hζ μ hμ hmean hm b
    (q := e) (fun B => A B/d) scale (fun B => H B/d)
    (fun B => div_pos (hA B) hdR) hscale hH'
  have hbin := hscale.eventually (binLabel_eventually_mul_invariant J hJ
    (fun i : Fin (J-1) => i.val+1) (fun _ => by omega) ζ hd.ne')
  have hw := auxiliaryPrimeFeature_eventually_mul_fixed hd.ne' (fun B => primeCoarseFeature m B b)
  intro ε hε
  filter_upwards [hu ε hε,hH.eventually_gt_atTop 0,hw] with B hB hHB hwB
  have hX := hscale.const_mul_atTop (hA B)
  filter_upwards [hB,hbin,hX.eventually_gt_atTop 0] with n hn hbn hXn
  have he := residueBinAverage_dilate_energy_le
    (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
    (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b))
    (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b)) 1 hd e a
    ⟨by norm_num,by exact_mod_cast hd⟩ (fun k => by simpa only [one_mul] using hwB k) hbn hHB hXn
  have hh := hn (ZMod.unitOfCoprime a ha)
  have hxd : A B*scale n/(d : ℝ) = (A B/d)*scale n := by ring
  simp only [hxd] at he
  have hu' : (1/((A B/d)*scale n))*(∫ z in ((A B/d)*scale n)..2*((A B/d)*scale n),
      ‖residueBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
        (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b))
        (a : ZMod e) (H B/d) z‖^2) < ε := by
    simpa only [← residueBinAverage_unit,ZMod.coe_unitOfCoprime] using hh
  exact he.trans_lt hu'

theorem all_residues_coarse_short_with_center
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) (b : Fin m)
    {q : ℕ} [NeZero q] (A scale H : ℕ → ℝ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hH : Tendsto H atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop, ∀ r : ZMod q,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖residueBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b)) r (H B) z‖^2) < ε := by
  intro ε hε
  have hr (r : ZMod q) : ∀ᶠ B in atTop, ∀ᶠ n in atTop,
      (1/(A B*scale n))*(∫ z in (A B*scale n)..2*(A B*scale n),
        ‖residueBinAverage (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ μ
          (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b)) r (H B) z‖^2) < ε := by
    obtain ⟨d,e,a,hd,he,hq,hr,ha⟩ := residue_fixed_divisor_representation r
    subst q
    let : NeZero e := ⟨he.ne'⟩
    rw [hr]
    exact fixed_residue_coarse_short_with_center hMR hMRT hKMT hM hSD hSW hMP hJ ζ hζ μ hμ hmean
      hm b hd a ha A scale H hA hscale hH ε hε
  filter_upwards [eventually_all.mpr hr] with B hB
  exact eventually_all.mpr hB

end JointDickman

end OAI
