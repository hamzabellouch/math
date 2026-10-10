import OAI.MeasureTheory.Falconer.Angular.FourPointCaps
import OAI.MeasureTheory.Falconer.Estimates.RotatedNonstationary
import OAI.MeasureTheory.Falconer.Angular.InverseStationaryCutoff
import OAI.MeasureTheory.Falconer.Angular.StationaryOppositePhase

namespace OAI

/-!
# Derivatives of the actual cap-weighted endpoint pair

Scalar product and conjugation rules control the amplitudes and their
rotated spherical chart in arbitrary ambient dimension at least three.
-/

namespace Falconer
open Set
open scoped ContDiff ComplexConjugate

theorem capPairAmplitude_chart_smooth {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (η : Sphere (n+2) → ℝ)
    (b b' : Space (n+2) → Sphere (n+2) → ℂ)
    (x : Space (n+2) × Space (n+2)) (y : Space n)
    (hη : ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => (η w : ℂ)) y))
    (hb : ContDiff ℝ ∞ (rotatedChartAmplitude e (b x.1) y))
    (hb' : ContDiff ℝ ∞ (rotatedChartAmplitude e (b' x.2) y)) :
    ContDiff ℝ ∞ (rotatedChartAmplitude e (capPairAmplitude η b b' x) y) :=
  hη.mul (hb.mul (Complex.conjCLE.contDiff.comp hb'))

theorem capPairAmplitude_chart_derivatives {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (η : Sphere (n+2) → ℝ)
    (b b' : Space (n+2) → Sphere (n+2) → ℂ)
    (x : Space (n+2) × Space (n+2)) (y : Space n) (m : ℕ)
    (hη : ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => (η w : ℂ)) y))
    (hb : ContDiff ℝ ∞ (rotatedChartAmplitude e (b x.1) y))
    (hb' : ContDiff ℝ ∞ (rotatedChartAmplitude e (b' x.2) y))
    {H B B' D : ℝ} (hH : 0 ≤ H) (hB : 0 ≤ B) (hB' : 0 ≤ B') (hD : 0 ≤ D)
    (u : ℝ)
    (hηbound : ∀ k ≤ m,
      ‖iteratedDeriv k (rotatedChartAmplitude e (fun w => (η w : ℂ)) y) u‖ ≤ H*D^k)
    (hbbound : ∀ k ≤ m,
      ‖iteratedDeriv k (rotatedChartAmplitude e (b x.1) y) u‖ ≤ B*D^k)
    (hb'bound : ∀ k ≤ m,
      ‖iteratedDeriv k (rotatedChartAmplitude e (b' x.2) y) u‖ ≤ B'*D^k) :
    ∀ k ≤ m, ‖iteratedDeriv k
      (rotatedChartAmplitude e (capPairAmplitude η b b' x) y) u‖ ≤
        (4^m*H*B*B')*D^k := by
  let f := rotatedChartAmplitude e (b x.1) y
  let g := rotatedChartAmplitude e (b' x.2) y
  let h := rotatedChartAmplitude e (fun w => (η w : ℂ)) y
  have hconj : ContDiff ℝ ∞ (fun u => conj (g u)) := Complex.conjCLE.contDiff.comp hb'
  have hconjb (k : ℕ) (hk : k ≤ m) :
      ‖iteratedDeriv k (fun u => conj (g u)) u‖ ≤ B'*D^k := by
    rw [PlanarFalconer.complex_iteratedDeriv_conj hb',Complex.norm_conj]
    exact hb'bound k hk
  have hpair (k : ℕ) (hk : k ≤ m) :
      ‖iteratedDeriv k (fun u => f u*conj (g u)) u‖ ≤ (2^m*B*B')*D^k := by
    apply (PlanarFalconer.complex_product_derivative_bound hb hconj hB hB' hD k u
      (fun j hj => hbbound j (hj.trans hk)) (fun j hj => hconjb j (hj.trans hk))).trans
    gcongr
    norm_num
  intro k hk
  change ‖iteratedDeriv k (fun u => h u*(f u*conj (g u))) u‖ ≤ _
  apply (PlanarFalconer.complex_product_derivative_bound hη (hb.mul hconj)
    hH (by positivity) hD k u (fun j hj => hηbound j (hj.trans hk))
    (fun j hj => hpair j (hj.trans hk))).trans
  calc
    _ ≤ (2^m*H*(2^m*B*B'))*D^k := by gcongr; norm_num
    _ = _ := by rw [show (4 : ℝ)^m = 2^m*2^m by rw [← mul_pow]; norm_num]; ring

theorem capPairAmplitude_cap_support {d : ℕ} (η : Sphere d → ℝ)
    (b b' : Space d → Sphere d → ℂ) (w₀ : Space d) (δ : ℝ)
    (hη : ∀ w, η w ≠ 0 → ‖(w : Space d)-w₀‖ ≤ δ)
    (x : Space d × Space d) (w : Sphere d)
    (h : capPairAmplitude η b b' x w ≠ 0) : ‖(w : Space d)-w₀‖ ≤ δ := by
  apply hη w
  intro hz
  exact h (by simp [capPairAmplitude,hz])

end Falconer

end OAI
