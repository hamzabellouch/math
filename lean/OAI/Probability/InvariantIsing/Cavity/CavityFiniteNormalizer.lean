import OAI.Probability.InvariantIsing.Cavity.CavityFiniteLogDet
import OAI.Probability.InvariantIsing.Cavity.CavityNormalizerIntegral

namespace OAI

/-! Evaluation of the quadratic root/gap/residual normalizer on a finite
trial overlap path. No quadratic marking or limiting formula is assumed. -/

noncomputable section
open MeasureTheory Set
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology

namespace InvariantIsing

def cavityFiniteQuadraticMean {d l : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (H : Fin (l + 1) → Matrix (Fin d) (Fin d) ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (cut : Fin (l + 2) → ℝ) : ℝ :=
  Matrix.trace (S₀ * cavityBackwardQuadratic K (H 0)) / 2 -
    (∑ i : Fin l, Real.log ((1 - H i.castSucc * K).det / (1 - H i.succ * K).det) /
      (2 * cut i.castSucc.succ)) - Real.log (1 - H (Fin.last l) * K).det / 2

private lemma cavity_finite_normalizer_algebra {m d l : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (p : OverlapPath) (cut : Fin (l + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (l + 1)) = 1)
    (q : Fin (l + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j r, r ∈ Ioo (cut j.castSucc) (cut j.succ) → p r = q j)
    (htop : q (Fin.last l) < 1)
    (K : Matrix (Fin d) (Fin d) ℝ) (H : Fin (l + 1) → Matrix (Fin d) (Fin d) ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (size : ℝ)
    (hdet : ∀ i, (1 - H i * K).det ≠ 0)
    (hlog : ∀ i, Real.log (1 - H i * K).det =
      size * cavityLogDetPotential rho lam hrho hsum (deficit p (q i)))
    (hroot : Matrix.trace (S₀ * cavityBackwardQuadratic K (H 0)) =
      -size * (q 0 * deficit p (q 0) * cavityRDerivative rho lam hrho hsum (deficit p (q 0)))) :
    cavityFiniteQuadraticMean K H S₀ cut =
      -(size / 2) * ∫ r in 0..1, cavityNormalizerDensity rho lam hrho hsum p r := by
  rw [finite_overlap_normalizer_integral rho lam hrho hsum p cut hcut hfirst hlast q hq hp htop]
  unfold cavityFiniteQuadraticMean
  rw [hroot, hlog]
  simp_rw [Real.log_div (hdet _) (hdet _), hlog]
  have he (i : Fin l) :
      (size * cavityLogDetPotential rho lam hrho hsum (deficit p (q i.castSucc)) -
        size * cavityLogDetPotential rho lam hrho hsum (deficit p (q i.succ))) /
          (2 * cut i.castSucc.succ) =
      size / 2 * ((cavityLogDetPotential rho lam hrho hsum (deficit p (q i.castSucc)) -
        cavityLogDetPotential rho lam hrho hsum (deficit p (q i.succ))) / cut i.castSucc.succ) := by
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  ring

/-- The finite-multiplicity quadratic normalizer, including the ordinary
last Gaussian integration, is exactly the required path integral. -/
theorem cavity_finite_quadratic_mean {m d N l : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (s : Fin m → ℕ) (hs : ∀ a, s a ≤ N)
    (hcounts : ∀ a, (Finset.univ.filter (fun i => g i = a)).card = N - s a)
    (hsrho : ∀ a, (s a : ℝ) = (N : ℝ) * rho a)
    (p : OverlapPath) (cut : Fin (l + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (l + 1)) = 1)
    (q : Fin (l + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j r, r ∈ Ioo (cut j.castSucc) (cut j.succ) → p r = q j)
    (htop : q (Fin.last l) < 1) :
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B - A₀
    let H := fun j => (finiteInverse rho lam hrho hsum (deficit p (q j)) •
      (1 : Matrix (Fin d) (Fin d) ℝ) - A₀)⁻¹
    let S₀ := q 0 • ((1 / finiteSecondResolvent rho lam
      (finiteInverse rho lam hrho hsum (deficit p (q 0)))) • (H 0 * H 0))
    cavityFiniteQuadraticMean K H S₀ cut =
      -((N : ℝ) / 2) * ∫ r in 0..1, cavityNormalizerDensity rho lam hrho hsum p r := by
  let A₀ := Matrix.diagonal (fun i => lam (g i))
  let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B - A₀
  let H := fun j => (finiteInverse rho lam hrho hsum (deficit p (q j)) •
    (1 : Matrix (Fin d) (Fin d) ℝ) - A₀)⁻¹
  let S₀ := q 0 • ((1 / finiteSecondResolvent rho lam
    (finiteInverse rho lam hrho hsum (deficit p (q 0)))) • (H 0 * H 0))
  have hx (j : Fin (l + 1)) : 0 < deficit p (q j) :=
    finite_overlap_deficit_pos p cut hfirst hlast q hq.monotone hp htop (hq.monotone (Fin.le_last j))
  have hdet (j : Fin (l + 1)) : (1 - H j * K).det ≠ 0 := by
    rw [show (1 - H j * K).det = (deficit p (q j)) ^ N *
        ∏ a, (finiteInverse rho lam hrho hsum (deficit p (q j)) - lam a) ^ s a from
      cavity_finite_tilt_determinant rho lam hrho hsum B hB hBE hcomplete g s hs hcounts _ (hx j)]
    exact mul_ne_zero (pow_ne_zero N (hx j).ne') (Finset.prod_ne_zero_iff.mpr
      (fun a _ => pow_ne_zero _ (sub_pos.mpr
        ((finiteInverse_spec rho lam hrho hsum (hx j)).1 a)).ne'))
  have hlog (j : Fin (l + 1)) : Real.log (1 - H j * K).det =
      (N : ℝ) * cavityLogDetPotential rho lam hrho hsum (deficit p (q j)) := by
    rw [cavityLogDetPotential_eq rho lam hrho hsum (hx j)]
    exact cavity_finite_tilt_logdet rho lam hrho hsum B hB hBE hcomplete
      g s hs hcounts hsrho _ (hx j)
  have hroot : Matrix.trace (S₀ * cavityBackwardQuadratic K (H 0)) =
      -(N : ℝ) * (q 0 * deficit p (q 0) *
        cavityRDerivative rho lam hrho hsum (deficit p (q 0))) := by
    have he := cavity_finite_root_trace rho lam hrho hsum B hB hBE hcomplete
      g s hs hcounts hsrho _ (hx 0)
    change Matrix.trace (((1 / finiteSecondResolvent rho lam
      (finiteInverse rho lam hrho hsum (deficit p (q 0)))) • (H 0 * H 0)) *
        cavityBackwardQuadratic K (H 0)) = _ at he
    dsimp only [S₀]
    rw [Matrix.smul_mul, Matrix.trace_smul, he,
      ← cavityRDerivative_eq_deriv rho lam hrho hsum (hx 0)]
    ring
  exact cavity_finite_normalizer_algebra rho lam hrho hsum p cut hcut hfirst hlast
    q hq hp htop K H S₀ N hdet hlog hroot

end InvariantIsing

end

end OAI
