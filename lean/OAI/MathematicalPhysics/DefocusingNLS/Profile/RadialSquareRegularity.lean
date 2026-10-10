import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexAverage
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! The squared-radius profile has a regular first derivative at the origin. -/

open Set Filter Topology
namespace DefocusingNLS

noncomputable def radialSquareProfile (Q : ℝ → ℂ) (x : ℝ) : ℂ := Q (Real.sqrt x)

noncomputable def radialSquareSlope (k : ℕ) (a b : ℝ) (Q : ℝ → ℂ) (x : ℝ) : ℂ :=
  radialComplexAverage k a b Q (Real.sqrt x)/2

theorem radialSquareSlope_continuous (k : ℕ) (a b : ℝ) (Q : ℝ → ℂ)
    (hQ : Continuous Q) : Continuous (radialSquareSlope k a b Q) :=
  ((radialComplexAverage_continuous k a b Q hQ).comp Real.continuous_sqrt).div_const 2

theorem radialSquareProfile_hasDerivAt (k : ℕ) (a b R : ℝ) (hR : 0 < R)
    (Q : ℝ → ℂ) (hQ : Differentiable ℝ Q)
    (hd : ∀ r ∈ Ioc 0 R, deriv Q r=(r : ℂ)*radialComplexAverage k a b Q r)
    (x : ℝ) (hx : x ∈ Ioc 0 (R^2)) :
    HasDerivAt (radialSquareProfile Q) (radialSquareSlope k a b Q x) x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx.1
  have hsC : (Real.sqrt x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hsR : Real.sqrt x ≤ R := (Real.sqrt_le_left hR.le).2 hx.2
  have hh := ((hQ (Real.sqrt x)).hasDerivAt).scomp x (Real.hasDerivAt_sqrt hx.1.ne')
  rw [hd _ ⟨hs,hsR⟩] at hh
  apply hh.congr_deriv
  change (1/(2*Real.sqrt x) : ℝ) •
    ((Real.sqrt x : ℂ)*radialComplexAverage k a b Q (Real.sqrt x))=
      radialComplexAverage k a b Q (Real.sqrt x)/2
  rw [Complex.real_smul]
  push_cast
  field_simp [hsC]

theorem radialSquareProfile_hasDerivWithinAt_zero (k : ℕ) (a b R : ℝ) (hR : 0 < R)
    (Q : ℝ → ℂ) (hQ : Differentiable ℝ Q)
    (hd : ∀ r ∈ Ioc 0 R, deriv Q r=(r : ℂ)*radialComplexAverage k a b Q r) :
    HasDerivWithinAt (radialSquareProfile Q) (radialComplexSource k a b (Q 0)/24)
      (Ici 0) 0 := by
  have h0 : 0 < R^2 := sq_pos_of_pos hR
  have hc : Continuous (radialSquareProfile Q) := hQ.continuous.comp Real.continuous_sqrt
  have hs := radialSquareSlope_continuous k a b Q hQ.continuous
  have hlim : Tendsto (deriv (radialSquareProfile Q)) (nhdsWithin 0 (Ioi 0))
      (nhds (radialSquareSlope k a b Q 0)) := by
    apply hs.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
    filter_upwards [Ioo_mem_nhdsGT h0] with x hx
    exact (radialSquareProfile_hasDerivAt k a b R hR Q hQ hd x ⟨hx.1,hx.2.le⟩).deriv.symm
  have hh := hasDerivWithinAt_Ici_of_tendsto_deriv
    (s := Ioo 0 (R^2))
    (fun x hx => (radialSquareProfile_hasDerivAt k a b R hR Q hQ hd x
      ⟨hx.1,hx.2.le⟩).differentiableAt.differentiableWithinAt)
    hc.continuousAt.continuousWithinAt (Ioo_mem_nhdsGT h0) hlim
  convert hh using 1
  simp only [radialSquareSlope,Real.sqrt_zero,radialComplexAverage_zero]
  ring

theorem radialSquareProfile_contDiffOn_one (k : ℕ) (a b R : ℝ) (hR : 0 < R)
    (Q : ℝ → ℂ) (hQ : Differentiable ℝ Q)
    (hd : ∀ r ∈ Ioc 0 R, deriv Q r=(r : ℂ)*radialComplexAverage k a b Q r) :
    ContDiffOn ℝ 1 (radialSquareProfile Q) (Icc 0 (R^2)) := by
  have hu := uniqueDiffOn_Icc (sq_pos_of_pos hR)
  have hder (x : ℝ) (hx : x ∈ Icc 0 (R^2)) :
      HasDerivWithinAt (radialSquareProfile Q) (radialSquareSlope k a b Q x)
        (Icc 0 (R^2)) x := by
    rcases hx.1.eq_or_lt with rfl | hx0
    · have hh := (radialSquareProfile_hasDerivWithinAt_zero k a b R hR Q hQ hd).mono
        (s := Icc 0 (R^2))
        Icc_subset_Ici_self
      convert hh using 1
      simp only [radialSquareSlope,Real.sqrt_zero,radialComplexAverage_zero]
      ring
    · exact (radialSquareProfile_hasDerivAt k a b R hR Q hQ hd x ⟨hx0,hx.2⟩).hasDerivWithinAt
  apply (contDiffOn_one_iff_derivWithin hu).2
  refine ⟨fun x hx => (hder x hx).differentiableWithinAt,?_⟩
  apply (radialSquareSlope_continuous k a b Q hQ.continuous).continuousOn.congr
  intro x hx
  exact (hder x hx).derivWithin (hu x hx)

end DefocusingNLS

end OAI
