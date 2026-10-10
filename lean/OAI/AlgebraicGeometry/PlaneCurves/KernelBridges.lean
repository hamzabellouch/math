import OAI.AlgebraicGeometry.PlaneCurves.JetGerms

namespace OAI

/-!
# Identification of actual jets and polynomial section kernels
-/

section

/-! A genuine chart-local expression for each genuine section basis element
identifies the actual jet map with the finite separated mixed-derivative matrix.
No assumed equality of matrices is needed in this bridge. -/

noncomputable section
open Filter Topology Module
namespace Nagata.Workers.W12
open Nagata.W20 Nagata.Workers.W11 Nagata.Workers.W30 Nagata.FiniteExponents

/-- Local scalar formulas of actual basis elements prove every matrix entry.
It suffices to identify germs on a genuine neighborhood of the chart origin. -/
theorem actual_basisJetMatrix_eq_of_local_expressions
    {τ gammaL gammaP : ℂ} {d : ℤ} {q m : ℕ} {a delta : ℝ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) {z0 : ℂ} (hz0 : z0 ≠ 0)
    (e : Basis (Column d (m : ℤ) a delta) ℂ (ActualSection τ gammaL gammaP d m P))
    (coeff : Column d (m : ℤ) a delta → ℂ → ℂ)
    (hlocal : ∀ col, ∀ᶠ z : ℂ × ℂ in 𝓝 (0, 0),
      localScalar (e col) z0 z.1 z.2 =
        coeff col z.1 * Complex.exp ((col.val.1 : ℂ) * z.2)) :
    basisJetMatrix (K := ℂ) (V := ActualSection τ gammaL gammaP d m P) e (actualJetMap (τ := τ) (γL := gammaL) (γP := gammaP) (d := d) (m := m) hP hz0 q) =
      separatedJetMatrix d q m a delta coeff := by
  funext row col
  change actualJetMap (τ := τ) (γL := gammaL) (γP := gammaP) (d := d) (m := m) hP hz0 q (e col) row = _
  rw [actualJetMap_apply_eq_mixed_derivative]
  exact mixedJetAtZero_congr_of_eventuallyEq row.2.val row.1.val (hlocal col)

end Nagata.Workers.W12

end
end

section

noncomputable section
open Filter Topology Module
namespace Nagata.Workers.W12
open Nagata.W20 Nagata.Workers.W11 Nagata.Workers.W30 Nagata.FiniteExponents

/-- A nonzero genuine section in the actual jet kernel gives a nonzero vector
in the specified matrix kernel, through its genuine basis coordinates. -/
theorem actual_kernel_to_coefficients
    {τ gammaL gammaP : ℂ} {d : ℤ} {q m : ℕ} {a delta : ℝ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) {z0 : ℂ} (hz0 : z0 ≠ 0)
    (e : Basis (Column d (m : ℤ) a delta) ℂ (ActualSection τ gammaL gammaP d m P))
    (M : Matrix (JetIndex q m) (Column d (m : ℤ) a delta) ℂ)
    (hmatrix : basisJetMatrix (K := ℂ) (V := ActualSection τ gammaL gammaP d m P) e (actualJetMap hP hz0 q) = M)
    (F : ActualSection τ gammaL gammaP d m P)
    (hF : F ≠ 0) (hjet : actualJetMap hP hz0 q F = 0) :
    ∃ c : Column d (m : ℤ) a delta → ℂ, c ≠ 0 ∧ M.mulVec c = 0 := by
  obtain ⟨c, hc, hkernel⟩ := basisJetMatrix_nonzero_kernel (K := ℂ) (V := ActualSection τ gammaL gammaP d m P) e
    (actualJetMap hP hz0 q) F hF hjet
  exact ⟨c, hc, hmatrix ▸ hkernel⟩

/-- Moving actual sections with the genuine local Taylor multiplicities give
matrix kernel coefficients. This uses the collision proof, rather than assuming
vanishing of the target mixed jets or an already-existing kernel section. -/
theorem actual_collision_to_coefficients
    {τ gammaL gammaP : ℂ} {d : ℤ} {q m : ℕ} {a delta : ℝ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) {z0 : ℂ} (hz0 : z0 ≠ 0)
    (e : Basis (Column d (m : ℤ) a delta) ℂ (ActualSection τ gammaL gammaP d m P))
    (M : Matrix (JetIndex q m) (Column d (m : ℤ) a delta) ℂ)
    (hmatrix : basisJetMatrix (K := ℂ) (V := ActualSection τ gammaL gammaP d m P) e (actualJetMap hP hz0 q) = M)
    (F : ℕ → ActualSection τ gammaL gammaP d m P) (hF : ∀ n, F n ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (xi : ℕ → Fin q → ℂ)
    (hxilim : ∀ i, Tendsto (fun n => xi n i) atTop (𝓝 0))
    (hxiinj : ∀ n, Function.Injective (xi n))
    (hximem : ∀ n i, xi n i ∈ U)
    (S : ℕ → Fin q → FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ)
    (hS : ∀ n i, HasFPowerSeriesAt
      (fun p : ℂ × ℂ => localScalar (F n) z0 p.1 p.2) (S n i) (xi n i, 0))
    (hzero : ∀ n i j, j < m → S n i j = 0) :
    ∃ c : Column d (m : ℤ) a delta → ℂ, c ≠ 0 ∧ M.mulVec c = 0 := by
  obtain ⟨F0, hF0, hjet⟩ := actual_kernel_from_local_powerSeries hP hz0 e
    F hF hU h0 xi hxilim hxiinj hximem S hS hzero
  exact actual_kernel_to_coefficients hP hz0 e M hmatrix F0 hF0 hjet

/-- The same sufficiently small τ supplies both injectivity and the genuine
section kernel. The section/basis/coordinate data may vary arbitrarily with τ. -/
theorem actual_section_kernel_contradiction
    (d : ℤ) (q m : ℕ) (a delta : ℝ)
    (gammaL gammaP z0 : ℝ → ℂ) (P : ℝ → ℂ → ℂ)
    (M : ℝ → Matrix (JetIndex q m) (Column d (m : ℤ) a delta) ℂ)
    (hinjective : ∀ᶠ τ in 𝓝[>] (0 : ℝ), Function.Injective (M τ).mulVec)
    (hactual : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∃ (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ (P τ) z)
        (hz0 : z0 τ ≠ 0)
        (e : Basis (Column d (m : ℤ) a delta) ℂ
          (ActualSection (τ : ℂ) (gammaL τ) (gammaP τ) d m (P τ)))
        (F : ActualSection (τ : ℂ) (gammaL τ) (gammaP τ) d m (P τ)),
        basisJetMatrix (K := ℂ)
          (V := ActualSection (τ : ℂ) (gammaL τ) (gammaP τ) d m (P τ))
          e (actualJetMap hP hz0 q) = M τ ∧
          F ≠ 0 ∧ actualJetMap hP hz0 q F = 0) : False := by
  apply coefficient_kernel_contradiction d q m a delta M hinjective
  apply hactual.mono
  intro τ hτ
  obtain ⟨hP, hz0, e, F, hmatrix, hF, hjet⟩ := hτ
  exact actual_kernel_to_coefficients hP hz0 e (M τ) hmatrix F hF hjet

end Nagata.Workers.W12

end
end

section

noncomputable section
open Filter Topology Module
namespace Nagata.Workers.W12
open Nagata.W20 Nagata.Workers.W11 Nagata.Workers.W30 Nagata.FiniteExponents

/-- The source-facing fixed-τ bridge from ordinary polynomial multiplicities
through actual section collision to nonzero coefficient vectors. -/
theorem actual_polynomial_collision_to_coefficients
    {τ gammaL gammaP : ℂ} {d : ℤ} {q m : ℕ} {a delta : ℝ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) {z0 : ℂ} (hz0 : z0 ≠ 0)
    (e : Basis (Column d (m : ℤ) a delta) ℂ (ActualSection τ gammaL gammaP d m P))
    (coeff : Column d (m : ℤ) a delta → ℂ → ℂ)
    (hlocal : ∀ col, ∀ᶠ z : ℂ × ℂ in 𝓝 (0, 0),
      localScalar (e col) z0 z.1 z.2 =
        coeff col z.1 * Complex.exp ((col.val.1 : ℂ) * z.2))
    (F : ℕ → ActualSection τ gammaL gammaP d m P) (hF : ∀ n, F n ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (xi : ℕ → Fin q → ℂ)
    (hxilim : ∀ i, Tendsto (fun n => xi n i) atTop (𝓝 0))
    (hxiinj : ∀ n, Function.Injective (xi n))
    (hximem : ∀ n i, xi n i ∈ U)
    (A : ℕ → Fin q → MvPolynomial (Fin 2) ℂ)
    (kappa : ℕ → Fin q → (ℂ × ℂ) → (ℂ × ℂ))
    (hkappa : ∀ n i, AnalyticAt ℂ (kappa n i) (xi n i, 0))
    (hmult : ∀ n i, Nagata.AffineMultiplicity.orderAtLeast
      (fun j : Fin 2 => if j = 0 then (kappa n i (xi n i, 0)).1
        else (kappa n i (xi n i, 0)).2) m (A n i))
    (hrep : ∀ n i,
      (fun p : ℂ × ℂ => MvPolynomial.eval
        (fun j : Fin 2 => if j = 0 then (kappa n i p).1 else (kappa n i p).2) (A n i))
        =ᶠ[𝓝 (xi n i, 0)] (fun p => localScalar (F n) z0 p.1 p.2)) :
    ∃ c : Column d (m : ℤ) a delta → ℂ, c ≠ 0 ∧
      (separatedJetMatrix d q m a delta coeff).mulVec c = 0 := by
  obtain ⟨F0, hF0, hjet⟩ := actual_kernel_from_local_polynomial_multiplicity
    hP hz0 e F hF hU h0 xi hxilim hxiinj hximem A kappa hkappa hmult hrep
  exact actual_kernel_to_coefficients hP hz0 e (separatedJetMatrix d q m a delta coeff)
    (actual_basisJetMatrix_eq_of_local_expressions hP hz0 e coeff hlocal) F0 hF0 hjet

/-- The source-facing fixed-τ bridge from ordinary polynomial multiplicities
through actual section collision to nonzero coefficient vectors. -/
theorem actual_polynomial_frame_collision_to_coefficients
    {τ gammaL gammaP : ℂ} {d : ℤ} {q m : ℕ} {a delta : ℝ} {P : ℂ → ℂ}
    (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) {z0 : ℂ} (hz0 : z0 ≠ 0)
    (e : Basis (Column d (m : ℤ) a delta) ℂ (ActualSection τ gammaL gammaP d m P))
    (coeff : Column d (m : ℤ) a delta → ℂ → ℂ)
    (hlocal : ∀ col, ∀ᶠ z : ℂ × ℂ in 𝓝 (0, 0),
      localScalar (e col) z0 z.1 z.2 =
        coeff col z.1 * Complex.exp ((col.val.1 : ℂ) * z.2))
    (F : ℕ → ActualSection τ gammaL gammaP d m P) (hF : ∀ n, F n ≠ 0)
    {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (xi : ℕ → Fin q → ℂ)
    (hxilim : ∀ i, Tendsto (fun n => xi n i) atTop (𝓝 0))
    (hxiinj : ∀ n, Function.Injective (xi n))
    (hximem : ∀ n i, xi n i ∈ U)
    (A : ℕ → Fin q → MvPolynomial (Fin 2) ℂ)
    (kappa : ℕ → Fin q → (ℂ × ℂ) → (ℂ × ℂ))
    (hkappa : ∀ n i, AnalyticAt ℂ (kappa n i) (xi n i, 0))
    (hmult : ∀ n i, Nagata.AffineMultiplicity.orderAtLeast
      (fun j : Fin 2 => if j = 0 then (kappa n i (xi n i, 0)).1
        else (kappa n i (xi n i, 0)).2) m (A n i))
    (u : ℕ → Fin q → (ℂ × ℂ) → ℂ)
    (hu : ∀ n i, AnalyticAt ℂ (u n i) (xi n i, 0))
    (hrep : ∀ n i,
      (fun p : ℂ × ℂ => u n i p * MvPolynomial.eval
        (fun j : Fin 2 => if j = 0 then (kappa n i p).1 else (kappa n i p).2) (A n i))
        =ᶠ[𝓝 (xi n i, 0)] (fun p => localScalar (F n) z0 p.1 p.2)) :
    ∃ c : Column d (m : ℤ) a delta → ℂ, c ≠ 0 ∧
      (separatedJetMatrix d q m a delta coeff).mulVec c = 0 := by
  obtain ⟨F0, hF0, hjet⟩ := actual_kernel_from_local_polynomial_with_frame
    hP hz0 e F hF hU h0 xi hxilim hxiinj hximem A kappa hkappa hmult u hu hrep
  exact actual_kernel_to_coefficients hP hz0 e (separatedJetMatrix d q m a delta coeff)
    (actual_basisJetMatrix_eq_of_local_expressions hP hz0 e coeff hlocal) F0 hF0 hjet

end Nagata.Workers.W12

end
end

end OAI
