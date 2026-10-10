import OAI.Geometry.EinsteinFour.Potential
import OAI.Geometry.EinsteinFour.Coupling

namespace OAI

/-! Exact triangle certificates and the full zeroth-order coupling bound. -/

namespace PositiveEinsteinFour.Boundary

open Potential

noncomputable section

def spectralCoefficient (v b : ℝ) : ℝ :=
  17 * (2 - v - b) * v - kappa v b

def correctedPotential (v b : ℝ) : ℝ :=
  potential v b + 12 * couplingCoefficient v b * (2 - v - b) ^ 2 * spectralCoefficient b v

private theorem spectral_coefficient_triangle {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) :
    0 ≤ spectralCoefficient (z + 2 * w) z := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcert : 36 * spectralCoefficient (z + 2 * w) z =
      1597 * (1 - z - w) ^ 6 +
      202 * w * (1 - z - w) ^ 5 +
      1895 * w ^ 2 * (1 - z - w) ^ 4 +
      16404 * w ^ 3 * (1 - z - w) ^ 3 +
      21811 * w ^ 4 * (1 - z - w) ^ 2 +
      10562 * w ^ 5 * (1 - z - w) +
      1865 * w ^ 6 +
      8899 * z * (1 - z - w) ^ 5 +
      14289 * z * w * (1 - z - w) ^ 4 +
      45098 * z * w ^ 2 * (1 - z - w) ^ 3 +
      81382 * z * w ^ 3 * (1 - z - w) ^ 2 +
      51939 * z * w ^ 4 * (1 - z - w) +
      10265 * z * w ^ 5 +
      16125 * z ^ 2 * (1 - z - w) ^ 4 +
      36612 * z ^ 2 * w * (1 - z - w) ^ 3 +
      91530 * z ^ 2 * w ^ 2 * (1 - z - w) ^ 2 +
      86676 * z ^ 2 * w ^ 3 * (1 - z - w) +
      21537 * z ^ 2 * w ^ 4 +
      13165 * z ^ 3 * (1 - z - w) ^ 3 +
      37489 * z ^ 3 * w * (1 - z - w) ^ 2 +
      60935 * z ^ 3 * w ^ 2 * (1 - z - w) +
      21635 * z ^ 3 * w ^ 3 +
      5566 * z ^ 4 * (1 - z - w) ^ 2 +
      16860 * z ^ 4 * w * (1 - z - w) +
      10394 * z ^ 4 * w ^ 2 +
      1224 * z ^ 5 * (1 - z - w) +
      1896 * z ^ 5 * w := by
    unfold spectralCoefficient kappa
    ring
  have hp : 0 ≤ 36 * spectralCoefficient (z + 2 * w) z := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem corrected_potential_left {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) :
    0 ≤ correctedPotential (z + w) w := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcert : 61440 * correctedPotential (z + w) w =
      52330496 * (1 - z - w) ^ 9 +
      357015552 * w * (1 - z - w) ^ 8 +
      815244288 * w ^ 2 * (1 - z - w) ^ 7 +
      810256384 * w ^ 3 * (1 - z - w) ^ 6 +
      394554624 * w ^ 4 * (1 - z - w) ^ 5 +
      107510016 * w ^ 5 * (1 - z - w) ^ 4 +
      12652544 * w ^ 6 * (1 - z - w) ^ 3 +
      556486656 * z * (1 - z - w) ^ 8 +
      2680071168 * z * w * (1 - z - w) ^ 7 +
      4303378944 * z * w ^ 2 * (1 - z - w) ^ 6 +
      2903831040 * z * w ^ 3 * (1 - z - w) ^ 5 +
      908160768 * z * w ^ 4 * (1 - z - w) ^ 4 +
      154624512 * z * w ^ 5 * (1 - z - w) ^ 3 +
      11212800 * z * w ^ 6 * (1 - z - w) ^ 2 +
      2195206400 * z ^ 2 * (1 - z - w) ^ 7 +
      7890980864 * z ^ 2 * w * (1 - z - w) ^ 6 +
      9038312320 * z ^ 2 * w ^ 2 * (1 - z - w) ^ 5 +
      3989635200 * z ^ 2 * w ^ 3 * (1 - z - w) ^ 4 +
      717011840 * z ^ 2 * w ^ 4 * (1 - z - w) ^ 3 +
      82824064 * z ^ 2 * w ^ 5 * (1 - z - w) ^ 2 +
      4427776 * z ^ 2 * w ^ 6 * (1 - z - w) +
      4629191296 * z ^ 3 * (1 - z - w) ^ 6 +
      12449319040 * z ^ 3 * w * (1 - z - w) ^ 5 +
      9970116736 * z ^ 3 * w ^ 2 * (1 - z - w) ^ 4 +
      2689352704 * z ^ 3 * w ^ 3 * (1 - z - w) ^ 3 +
      261153280 * z ^ 3 * w ^ 4 * (1 - z - w) ^ 2 +
      28723840 * z ^ 3 * w ^ 5 * (1 - z - w) +
      992256 * z ^ 3 * w ^ 6 +
      5937790992 * z ^ 4 * (1 - z - w) ^ 5 +
      11767844624 * z ^ 4 * w * (1 - z - w) ^ 4 +
      6335324928 * z ^ 4 * w ^ 2 * (1 - z - w) ^ 3 +
      957916992 * z ^ 4 * w ^ 3 * (1 - z - w) ^ 2 +
      65841872 * z ^ 4 * w ^ 4 * (1 - z - w) +
      6269328 * z ^ 4 * w ^ 5 +
      4893653872 * z ^ 5 * (1 - z - w) ^ 4 +
      6929290400 * z ^ 5 * w * (1 - z - w) ^ 3 +
      2344739296 * z ^ 5 * w ^ 2 * (1 - z - w) ^ 2 +
      190004832 * z ^ 5 * w ^ 3 * (1 - z - w) +
      12840720 * z ^ 5 * w ^ 4 +
      2625756488 * z ^ 6 * (1 - z - w) ^ 3 +
      2499901720 * z ^ 6 * w * (1 - z - w) ^ 2 +
      476640184 * z ^ 6 * w ^ 2 * (1 - z - w) +
      20443560 * z ^ 6 * w ^ 3 +
      890265000 * z ^ 7 * (1 - z - w) ^ 2 +
      506723984 * z ^ 7 * w * (1 - z - w) +
      42511368 * z ^ 7 * w ^ 2 +
      173232449 * z ^ 8 * (1 - z - w) +
      44351457 * z ^ 8 * w +
      14720001 * z ^ 9 := by
    unfold correctedPotential potential zeroOrder theta spectralCoefficient couplingCoefficient kappa
    ring
  have hp : 0 ≤ 61440 * correctedPotential (z + w) w := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem corrected_potential_right {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) :
    0 ≤ correctedPotential (1 + w) z := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcert : 61440 * correctedPotential (1 + w) z =
      14720001 * (1 - z - w) ^ 9 +
      91727569 * w * (1 - z - w) ^ 8 +
      238225960 * w ^ 2 * (1 - z - w) ^ 7 +
      327759896 * w ^ 3 * (1 - z - w) ^ 6 +
      234220880 * w ^ 4 * (1 - z - w) ^ 5 +
      58259600 * w ^ 5 * (1 - z - w) ^ 4 +
      2556928 * w ^ 6 * (1 - z - w) ^ 3 +
      39006208 * w ^ 7 * (1 - z - w) ^ 2 +
      27283456 * w ^ 8 * (1 - z - w) +
      253952 * w ^ 9 +
      44351457 * z * (1 - z - w) ^ 8 +
      202899328 * z * w * (1 - z - w) ^ 7 +
      373129128 * z * w ^ 2 * (1 - z - w) ^ 6 +
      374168320 * z * w ^ 3 * (1 - z - w) ^ 5 +
      259960144 * z * w ^ 4 * (1 - z - w) ^ 4 +
      218477056 * z * w ^ 5 * (1 - z - w) ^ 3 +
      215812096 * z * w ^ 6 * (1 - z - w) ^ 2 +
      104497152 * z * w ^ 7 * (1 - z - w) +
      1478656 * z * w ^ 8 +
      42511368 * z ^ 2 * (1 - z - w) ^ 7 +
      118518968 * z ^ 2 * w * (1 - z - w) ^ 6 +
      196012000 * z ^ 2 * w ^ 2 * (1 - z - w) ^ 5 +
      416840032 * z ^ 2 * w ^ 3 * (1 - z - w) ^ 4 +
      621025792 * z ^ 2 * w ^ 4 * (1 - z - w) ^ 3 +
      487728640 * z ^ 2 * w ^ 5 * (1 - z - w) ^ 2 +
      170454016 * z ^ 2 * w ^ 6 * (1 - z - w) +
      2140160 * z ^ 2 * w ^ 7 +
      20443560 * z ^ 3 * (1 - z - w) ^ 6 +
      55317888 * z ^ 3 * w * (1 - z - w) ^ 5 +
      284482272 * z ^ 3 * w ^ 2 * (1 - z - w) ^ 4 +
      644759552 * z ^ 3 * w ^ 3 * (1 - z - w) ^ 3 +
      549594624 * z ^ 3 * w ^ 4 * (1 - z - w) ^ 2 +
      160598016 * z ^ 3 * w ^ 5 * (1 - z - w) +
      1218560 * z ^ 3 * w ^ 6 +
      12840720 * z ^ 4 * (1 - z - w) ^ 5 +
      62565328 * z ^ 4 * w * (1 - z - w) ^ 4 +
      248047104 * z ^ 4 * w ^ 2 * (1 - z - w) ^ 3 +
      296960512 * z ^ 4 * w ^ 3 * (1 - z - w) ^ 2 +
      94270464 * z ^ 4 * w ^ 4 * (1 - z - w) +
      378880 * z ^ 4 * w ^ 5 +
      6269328 * z ^ 5 * (1 - z - w) ^ 4 +
      21430784 * z ^ 5 * w * (1 - z - w) ^ 3 +
      60944896 * z ^ 5 * w ^ 2 * (1 - z - w) ^ 2 +
      32604160 * z ^ 5 * w ^ 3 * (1 - z - w) +
      75776 * z ^ 5 * w ^ 4 +
      992256 * z ^ 6 * (1 - z - w) ^ 3 +
      1525760 * z ^ 6 * w * (1 - z - w) ^ 2 +
      5408768 * z ^ 6 * w ^ 2 * (1 - z - w) := by
    unfold correctedPotential potential zeroOrder theta spectralCoefficient couplingCoefficient kappa
    ring
  have hp : 0 ≤ 61440 * correctedPotential (1 + w) z := by
    rw [hcert]
    positivity
  nlinarith only [hp]

/-- The first boundary certificate in equation (23), including the vertex
where its value is zero. -/
theorem spectralCoefficient_nonneg {v b : ℝ}
    (hb : 0 ≤ b) (horder : b ≤ v) (hsum : v + b ≤ 2) :
    0 ≤ spectralCoefficient v b := by
  have h := spectral_coefficient_triangle (z := b) (w := (v - b) / 2)
    hb (by linarith) (by linarith)
  simpa only [show b + 2 * ((v - b) / 2) = v by ring] using h

/-- The last boundary certificate in equation (23). The two triangle proofs
meet along `v = 1`, so no strict-domain hypothesis is required. -/
theorem correctedPotential_nonneg {v b : ℝ}
    (hb : 0 ≤ b) (horder : b ≤ v) (hsum : v + b ≤ 2) :
    0 ≤ correctedPotential v b := by
  by_cases hv1 : v ≤ 1
  · have h := corrected_potential_left (z := v - b) (w := b)
      (by linarith) hb (by linarith)
    simpa only [sub_add_cancel] using h
  · have h := corrected_potential_right (z := b) (w := v - 1)
      hb (by linarith) (by linarith)
    simpa only [show 1 + (v - 1) = v by ring] using h

/-- The cubic eigenvalue parametrization controls the potential defect using
only the minimum-eigenvalue defect and the closed spectral domain. -/
theorem spectral_potential_defect_bound {v r σ δ : ℝ}
    (hv : 0 ≤ v) (hr : 1 ≤ r) (hr2 : r ≤ 2)
    (hδ : 0 ≤ δ) (hdefect : v * (r - 1) ≤ δ)
    (hσ : σ = (3 * r - r ^ 3) / 2) :
    v ^ 2 * (1 - σ) ≤ 2 * δ ^ 2 := by
  have hd : 0 ≤ v * (r - 1) := mul_nonneg hv (by linarith)
  have hsq : (v * (r - 1)) ^ 2 ≤ δ ^ 2 := by nlinarith
  have hfac : 1 - σ = (r - 1) ^ 2 * (r + 2) / 2 := by rw [hσ]; ring
  have hmul := mul_le_mul_of_nonneg_right (show (r + 2) / 2 ≤ 2 by linarith)
    (sq_nonneg (v * (r - 1)))
  rw [hfac]
  nlinarith

/-- The derivative-free part of the manuscript's combined integrand. -/
def zeroOrderIntegrand (v b σ τ : ℝ) : ℝ :=
  -zeroOrder v b - 6 * v ^ 2 * (1 - σ) * spectralCoefficient v b -
    6 * b ^ 2 * (1 - τ) * spectralCoefficient b v

private theorem ordered_zeroOrder_bound {v b σ τ : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (horder : b ≤ v) (hsum : v + b ≤ 2)
    (hσ : σ ≤ 1) (hτ : τ ≤ 1)
    (hdefect : b ^ 2 * (1 - τ) ≤ 2 * (2 - v - b) ^ 2) :
    zeroOrderIntegrand v b σ τ ≤ -theta v b ^ 2 / couplingCoefficient v b := by
  have hc : 0 < couplingCoefficient v b :=
    lt_of_lt_of_le (by norm_num) (couplingCoefficient_lower hsum hv hb)
  have hcform : couplingCoefficient v b = 2 / 5 - 3 * v * b / 10 := by
    unfold couplingCoefficient
    ring
  have hlv := spectralCoefficient_nonneg hb horder hsum
  have hplus : 0 ≤ 6 * v ^ 2 * (1 - σ) * spectralCoefficient v b := by positivity
  by_cases hlb : 0 ≤ spectralCoefficient b v
  · have hminus : 0 ≤ 6 * b ^ 2 * (1 - τ) * spectralCoefficient b v := by positivity
    have hI : zeroOrderIntegrand v b σ τ ≤ -zeroOrder v b := by
      unfold zeroOrderIntegrand
      linarith
    apply hI.trans
    apply (le_div_iff₀ hc).2
    have hF := potential_nonneg hv hb hsum
    unfold potential at hF
    rw [← hcform] at hF
    nlinarith
  · have hprod := mul_le_mul_of_nonpos_right hdefect
      (show 6 * spectralCoefficient b v ≤ 0 by linarith)
    have hI : zeroOrderIntegrand v b σ τ ≤
        -zeroOrder v b - 12 * (2 - v - b) ^ 2 * spectralCoefficient b v := by
      unfold zeroOrderIntegrand
      nlinarith only [hplus, hprod]
    apply hI.trans
    apply (le_div_iff₀ hc).2
    have hF := correctedPotential_nonneg hb horder hsum
    unfold correctedPotential potential at hF
    rw [← hcform] at hF
    nlinarith

theorem zeroOrderIntegrand_swap (v b σ τ : ℝ) :
    zeroOrderIntegrand b v τ σ = zeroOrderIntegrand v b σ τ := by
  unfold zeroOrderIntegrand zeroOrder
  ring

theorem theta_swap (v b : ℝ) : theta b v = theta v b := by
  unfold theta
  ring

/-- The full potential estimate `I₀ ≤ -Θ²/c`, on the closed spectral triangle
and for either ordering of the blocks. All polynomial certificates required
by equation (23) are proved in this development. -/
theorem zeroOrder_bound {v b σ τ : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2)
    (hσ : σ ≤ 1) (hτ : τ ≤ 1)
    (hvdefect : v ^ 2 * (1 - σ) ≤ 2 * (2 - v - b) ^ 2)
    (hbdefect : b ^ 2 * (1 - τ) ≤ 2 * (2 - v - b) ^ 2) :
    zeroOrderIntegrand v b σ τ ≤ -theta v b ^ 2 / couplingCoefficient v b := by
  rcases le_total b v with horder | horder
  · exact ordered_zeroOrder_bound hv hb horder hsum hσ hτ hbdefect
  · have h := ordered_zeroOrder_bound hb hv horder (by linarith) hτ hσ
      (by convert hvdefect using 1; ring)
    rw [zeroOrderIntegrand_swap, theta_swap] at h
    have hc : couplingCoefficient b v = couplingCoefficient v b := by
      unfold couplingCoefficient
      ring
    rwa [hc] at h

end

end PositiveEinsteinFour.Boundary

end OAI
