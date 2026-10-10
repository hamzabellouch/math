import OAI.Analysis.NumericalRange.BoundaryRepresentation

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_154 u_155 u_156

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset
open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Complex
open scoped Topology
open MeasureTheory Set Complex Metric
open scoped Topology

section
open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_154} [Fintype n] [DecidableEq n]

def pulledDiskDensity (D : Matrix n n ℂ) (ψ : ℂ → ℂ) (t : UnitAddCircle) : Matrix n n ℂ :=
  (((t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)/ψ (t.toCircle : ℂ))) •
    boundaryDiskDensity D (ψ (t.toCircle : ℂ))

lemma pulledDiskDensity_continuous {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1) :
    Continuous (pulledDiskDensity D ψ) := by
  let s : UnitAddCircle → ℂ := fun t => ψ (t.toCircle : ℂ)
  have ht (t : UnitAddCircle) : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by
    simp [Circle.norm_coe]
  have hc : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)) := by fun_prop
  have hs : Continuous s := hψ.continuousOn.comp_continuous hc ht
  have hv : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ)) :=
    hc.mul (hψ.deriv.continuousOn.comp_continuous hc ht)
  have hn (t : UnitAddCircle) : s t ∉ spectrum ℂ D := by
    intro he
    have hh := stable_spectrum_norm_lt_one hD he
    rw [show ‖s t‖ = 1 from hb _ (ht t)] at hh
    linarith
  have hR : AnalyticOnNhd ℂ (fun z : ℂ => (1-z • Dᴴ)⁻¹) (closedBall 0 1) := by
    intro z hz
    exact scalar_matrix_inverse_analytic (stable_star_disk_inverse_isUnit hD (by simpa using hz))
  have hQ : Continuous (fun t : UnitAddCircle => boundaryDiskDensity D (s t)) := by
    apply ((hs.smul (matrix_resolvent_continuous D hs hn)).add
      (hR.continuousOn.comp_continuous hs (fun t => by simpa using (hb _ (ht t)).le))).sub
        continuous_const |>.congr
    intro t
    exact (boundaryDiskDensity_eq hD (hb _ (ht t))).symm
  exact (hv.div hs (fun t => norm_ne_zero_iff.mp (by rw [show ‖s t‖ = 1 from hb _ (ht t)]; norm_num))).smul hQ

lemma pulledDiskDensity_nonneg {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) (hDc : Dᴴ*D ≤ 1) {ψ : ℂ → ℂ}
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hj : ∀ t ∈ sphere (0:ℂ) 1, 0 ≤ t*deriv ψ t/ψ t) (t : UnitAddCircle) :
    0 ≤ pulledDiskDensity D ψ t := by
  have ht : (t.toCircle : ℂ) ∈ sphere (0:ℂ) 1 := by simp [Circle.norm_coe]
  exact ((Matrix.nonneg_iff_posSemidef.mp (boundaryDiskDensity_nonneg hD hDc (hb _ ht))).smul
    (hj _ ht)).nonneg

theorem pulledDiskDensity_mass {D : Matrix n n ℂ}
    (hD : spectralRadius ℂ D < 1) {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1) :
    (∫ t : UnitAddCircle, pulledDiskDensity D ψ t ∂AddCircle.haarAddCircle) = 1 := by
  have he := complete_pulled_disk_representation (m := Unit) hD hψ hb hmass
    (H := fun _ => (1 : Matrix Unit Unit ℂ)) (fun _ _ _ _ => analyticAt_const)
  rw [completeAnalyticEval_const] at he
  have hc := pulledDiskDensity_continuous hD hψ hb
  have hi := hc.integrable_of_hasCompactSupport (μ := AddCircle.haarAddCircle)
    (HasCompactSupport.of_compactSpace _)
  have hkc : Continuous (fun t : UnitAddCircle =>
      (pulledDiskDensity D ψ t) ⊗ₖ (1 : Matrix Unit Unit ℂ)) :=
    continuous_kron hc continuous_const
  have hki := hkc.integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  change (∫ t : UnitAddCircle, (pulledDiskDensity D ψ t) ⊗ₖ (1 : Matrix Unit Unit ℂ)
    ∂AddCircle.haarAddCircle) = (1 : Matrix n n ℂ) ⊗ₖ (1 : Matrix Unit Unit ℂ) at he
  ext i j
  have hh := congrArg (fun M : Matrix (n × Unit) (n × Unit) ℂ => M (i,()) (j,())) he
  erw [matrix_integral_entry hki] at hh
  erw [matrix_integral_entry hi]
  simpa only [Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one] using hh

end

open MeasureTheory Set Metric Complex Filter
open scoped Topology Matrix.Norms.L2Operator Kronecker MatrixOrder ComplexOrder
variable {n : Type u_155} {m : Type u_156} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem interior_coordinate_exterior_representation (A : Matrix n n ℂ)
    {f g ψ G : ℂ → ℂ} {v : ℂ → Matrix m m ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hAU : spectrum ℂ A ⊆ U)
    (hf : ∀ z ∈ spectrum ℂ A, AnalyticAt ℂ f z)
    (hfd : ∀ z ∈ spectrum ℂ A, f z ∈ closedBall (0:ℂ) 1)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 1))
    (hgf : ∀ z ∈ U, g (f z) = z)
    (hv : AnalyticOnNhd ℂ v (g '' closedBall 0 1))
    (hD : spectralRadius ℂ (matrixAnalyticEval A f) < 1)
    (hψ : AnalyticOnNhd ℂ ψ (sphere 0 1))
    (hb : ∀ t ∈ sphere (0:ℂ) 1, ‖ψ t‖ = 1)
    (hgb : ∀ t ∈ sphere (0:ℂ) 1, g (ψ t) = G t)
    (hmass : ∀ z ∈ ball (0:ℂ) 1,
      (∫ t : UnitAddCircle, (t.toCircle : ℂ)*deriv ψ (t.toCircle : ℂ) /
        (ψ (t.toCircle : ℂ)-z) ∂AddCircle.haarAddCircle) = 1) :
    completeAnalyticEval A v =
      ∫ t : UnitAddCircle, pulledDiskDensity (matrixAnalyticEval A f) ψ t ⊗ₖ
        v (G (t.toCircle : ℂ)) ∂AddCircle.haarAddCircle := by
  have hvg : AnalyticOnNhd ℂ (fun z => v (g z)) (closedBall 0 1) := by
    intro z hz
    exact (hv (g z) ⟨z,hz,rfl⟩).comp (hg z hz)
  have he : completeAnalyticEval A v =
      completeAnalyticEval (matrixAnalyticEval A f) (fun z => v (g z)) := by
    rw [← completeAnalyticEval_comp A hf
      (F := fun z => v (g z)) (fun i j z hz => matrix_entry_analytic (hvg (f z) (hfd z hz)) i j)]
    apply completeAnalyticEval_eqOn A hU hAU
    intro z hz
    change v z = v (g (f z))
    rw [hgf z hz]
  rw [he, ← complete_pulled_disk_representation hD hψ hb hmass
    (fun i j z hz => matrix_entry_analytic (hvg z hz) i j)]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [hgb _ (by simp [Circle.norm_coe])]
  rfl


end CompleteCrouzeix

end

end OAI
