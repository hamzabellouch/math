import OAI.AlgebraicGeometry.PlaneCurves.KernelBridges
import OAI.AlgebraicGeometry.PlaneCurves.ScaledMatrices
import OAI.AlgebraicGeometry.PlaneCurves.SectionOrder

namespace OAI

/-!
# Same-basis coefficient and polynomial noncancellation
-/

section

/-! Literal source block bases assemble into the actual theta jet matrix.
The block basis evaluations and the Pi evaluation are explicit construction
inputs. Reindexing, the three branches, and the jet identity are proved here. -/
noncomputable section
open Module Filter Topology
namespace Nagata.Workers.W12
open Nagata.Workers.W10 Nagata.W20 Nagata.Workers.W11 Nagata.FiniteExponents Nagata.W22

variable (τ : ℝ) (γL γP : ℂ) (d : ℤ) (m : ℕ) (a delta : ℝ)
  (marks : Fin 9 → ℝ) (P : ℂ → ℂ) (z0 : ℂ)
  (hd : 3 * (m : ℤ) < d)
  (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
  (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
  (b : ∀ j : Fin ((d / 3).toNat + 1),
    Basis (ColumnFiber d (m : ℤ) a delta (j.val : ℤ)) ℂ
      (sourceBlock (τ : ℂ) γL γP d (m : ℤ) (j.val : ℤ)))
  (hblock : ∀ (j : Fin ((d / 3).toNat + 1))
      (K : ColumnFiber d (m : ℤ) a delta (j.val : ℤ)) (x : ℂ),
    (b j K).val (z0 * Complex.exp x) =
      if (j.val : ℤ) ≤ (m : ℤ) then
        normalizedThetaSeries (commonDegree d (m : ℤ) : ℝ)
          ((K.val : ℝ) - firstLower d (m : ℤ) (j.val : ℤ) a delta)
          (K.val : ℝ) ((-1 : ℂ) ^ ((m : ℤ) - (j.val : ℤ))) τ x
      else if 0 < d - 3 * (j.val : ℤ) then
        normalizedThetaSeries (sourceDegree d (j.val : ℤ) : ℝ)
          ((K.val : ℝ) - secondLower d (j.val : ℤ) a delta) (K.val : ℝ) 1 τ x
      else 1)
  (hPi : ∀ x : ℂ, P (z0 * Complex.exp x) = markedPi marks τ x)

include hblock hPi

/-- All literal column expressions, including the degree-zero tip, agree with
exactly the scalar basis used in the proved limiting matrix. -/
theorem sourceBasis_localScalar_eq_theta
    (col : Column d (m : ℤ) a delta) (x y : ℂ) :
    localScalar (polynomialBasisFromSourceBases (τ : ℂ) γL γP d m a delta P
      hd hP hPfin b col) z0 x y =
      basisCoefficient d (m : ℤ) a delta marks τ col x *
        Complex.exp ((col.val.1 : ℂ) * y) := by
  obtain ⟨⟨j, K⟩, rfl⟩ := (columnFiberEquiv d (m : ℤ) a delta
    (Int.natCast_nonneg m) hd).surjective col
  rw [polynomialBasisFromSourceBases_local, hblock, hPi]
  change _ = basisCoefficient d (m : ℤ) a delta marks τ
    ⟨((j.val : ℤ), K.val), K.property⟩ x * Complex.exp ((j.val : ℂ) * y)
  simp only [basisCoefficient]
  split_ifs <;> simp_all [multipliedThetaCoefficient]

/-- Actual mixed derivatives in the assembled genuine basis are the literal
finite theta matrix, without a separately assumed matrix identity. -/
theorem sourceBasis_actualJetMatrix_eq_theta (q : ℕ) (hz0 : z0 ≠ 0) :
    basisJetMatrix (K := ℂ)
      (V := ActualSection (τ : ℂ) γL γP d m P)
      (polynomialBasisFromSourceBases (τ : ℂ) γL γP d m a delta P hd hP hPfin b)
      (actualJetMap (τ := (τ : ℂ)) (γL := γL) (γP := γP) (d := d) (m := m)
        (fun z hz => (hP z hz).differentiableAt) hz0 q) =
      thetaJetMatrix d q m a delta marks τ := by
  apply actual_basisJetMatrix_eq_of_local_expressions
  intro col
  exact Filter.Eventually.of_forall (fun z =>
    sourceBasis_localScalar_eq_theta τ γL γP d m a delta marks P z0 hd hP hPfin b
      hblock hPi col z.1 z.2)

end Nagata.Workers.W12

end
end

section

noncomputable section
open Filter Topology
open scoped BigOperators
namespace Nagata.Workers.W12
open Nagata.Workers.W11 Nagata.Workers.W30 Nagata.FiniteExponents Nagata.W29

/-- The analytic and finite-matrix estimates rule out the stated coefficient-kernel
condition under the strict degree-ratio bounds. -/
theorem source_coefficient_bridge_contradiction
    (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / m) (hupp : (d : ℝ) / m < Real.sqrt r)
    (hbridge : ∀ (n : ℕ) (delta : ℝ) (x : Fin 9 → ℝ),
      0 < n → 0 < delta → delta < 1 / 2 → Function.Injective x →
      (∀ i, 0 < x i ∧ x i < 1 / 2) →
      (∑ i : Fin 9, sourceOffsets x i) = delta →
      (∀ j : ℤ, 0 ≤ j → j ≤ ((n * m : ℕ) : ℤ) →
        firstLower ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (∀ j : ℤ, ((n * m : ℕ) : ℤ) < j → j ≤ ((n * d : ℕ) : ℤ) / 3 →
        0 < ((n * d : ℕ) : ℤ) - 3 * j →
        secondLower ((n * d : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (exponentSet ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
        (3 * (Real.sqrt r - 3)) delta).Nonempty →
      ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∃ c : Column ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
          (3 * (Real.sqrt r - 3)) delta → ℂ,
          c ≠ 0 ∧ (thetaJetMatrix ((n * d : ℕ) : ℤ) (r - 9) (n * m)
            (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ).mulVec c = 0) :
    False := by
  obtain ⟨n, delta, x, hn, hd0, hdhalf, hxinj, hxbounds, hxsum,
    hfirst, hsecond, hnonempty, hinj⟩ :=
    exists_scaled_thetaJetMatrix_source_data r d m hr hm hlow hupp
  exact coefficient_kernel_contradiction ((n * d : ℕ) : ℤ) (r - 9) (n * m)
    (3 * (Real.sqrt r - 3)) delta
    (thetaJetMatrix ((n * d : ℕ) : ℤ) (r - 9) (n * m)
      (3 * (Real.sqrt r - 3)) delta (sourceOffsets x)) hinj
    (hbridge n delta x hn hd0 hdhalf hxinj hxbounds hxsum hfirst hsecond hnonempty)

end Nagata.Workers.W12

end
end

section

noncomputable section
open Filter Topology Module
open scoped BigOperators
namespace Nagata.Workers.W12
open Nagata.W20 Nagata.Workers.W11 Nagata.Workers.W30 Nagata.FiniteExponents Nagata.W29

/-- Single-witness source contradiction from concrete moving geometric data.
There is no kernel, Taylor-jet, matrix-equality, or rank hypothesis in hgeometry. -/
theorem source_polynomial_geometric_bridge_contradiction
    (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / m) (hupp : (d : ℝ) / m < Real.sqrt r)
    (hgeometry : ∀ (n : ℕ) (delta : ℝ) (x : Fin 9 → ℝ),
      0 < n → 0 < delta → delta < 1 / 2 → Function.Injective x →
      (∀ i, 0 < x i ∧ x i < 1 / 2) →
      (∑ i : Fin 9, sourceOffsets x i) = delta →
      (∀ j : ℤ, 0 ≤ j → j ≤ ((n * m : ℕ) : ℤ) →
        firstLower ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (∀ j : ℤ, ((n * m : ℕ) : ℤ) < j → j ≤ ((n * d : ℕ) : ℤ) / 3 →
        0 < ((n * d : ℕ) : ℤ) - 3 * j →
        secondLower ((n * d : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (exponentSet ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
        (3 * (Real.sqrt r - 3)) delta).Nonempty →
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        ∃ (gammaL gammaP z0 : ℂ) (P : ℂ → ℂ)
          (_ : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) (_ : z0 ≠ 0)
          (e : Basis (Column ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
            (3 * (Real.sqrt r - 3)) delta) ℂ
            (ActualSection (τ : ℂ) gammaL gammaP ((n * d : ℕ) : ℤ) (n * m) P))
          (F : ℕ → ActualSection (τ : ℂ) gammaL gammaP ((n * d : ℕ) : ℤ) (n * m) P)
          (U : Set ℂ) (xi : ℕ → Fin (r - 9) → ℂ)
          (A : ℕ → Fin (r - 9) → MvPolynomial (Fin 2) ℂ)
          (kappa : ℕ → Fin (r - 9) → (ℂ × ℂ) → (ℂ × ℂ))
          (u : ℕ → Fin (r - 9) → (ℂ × ℂ) → ℂ),
          (∀ col, ∀ᶠ z : ℂ × ℂ in 𝓝 (0, 0),
            localScalar (e col) z0 z.1 z.2 =
              Nagata.W22.basisCoefficient ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
                (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ col z.1 *
                Complex.exp ((col.val.1 : ℂ) * z.2)) ∧
          (∀ k, F k ≠ 0) ∧ IsOpen U ∧ (0 : ℂ) ∈ U ∧
          (∀ i, Tendsto (fun k => xi k i) atTop (𝓝 0)) ∧
          (∀ k, Function.Injective (xi k)) ∧ (∀ k i, xi k i ∈ U) ∧
          (∀ k i, AnalyticAt ℂ (kappa k i) (xi k i, 0)) ∧
          (∀ k i, Nagata.AffineMultiplicity.orderAtLeast
            (fun j : Fin 2 => if j = 0 then (kappa k i (xi k i, 0)).1
              else (kappa k i (xi k i, 0)).2) (n * m) (A k i)) ∧
          (∀ k i, AnalyticAt ℂ (u k i) (xi k i, 0)) ∧
          (∀ k i,
            (fun p : ℂ × ℂ => u k i p * MvPolynomial.eval
              (fun j : Fin 2 => if j = 0 then (kappa k i p).1 else (kappa k i p).2) (A k i))
              =ᶠ[𝓝 (xi k i, 0)] (fun p => localScalar (F k) z0 p.1 p.2))) : False := by
  apply source_coefficient_bridge_contradiction r d m hr hm hlow hupp
  intro n delta x hn hd0 hdhalf hxinj hxbounds hxsum hfirst hsecond hnonempty
  apply (hgeometry n delta x hn hd0 hdhalf hxinj hxbounds hxsum
    hfirst hsecond hnonempty).mono
  intro τ hτ
  obtain ⟨gammaL, gammaP, z0, P, hP, hz0, e, F, U, xi, A, kappa, u,
    hlocal, hF, hU, h0, hxilim, hxiinj, hximem, hkappa, hmult, hu, hrep⟩ := hτ
  exact actual_polynomial_frame_collision_to_coefficients hP hz0 e
    (Nagata.W22.basisCoefficient ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
      (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ)
    hlocal F hF hU h0 xi hxilim hxiinj hximem A kappa hkappa hmult u hu hrep

end Nagata.Workers.W12

end
end

section

/-!
# Conditional final contradiction on one simultaneous source witness
-/

noncomputable section
open Filter Topology Module
open scoped BigOperators
namespace Nagata.Workers.W12
open Nagata.W20 Nagata.Workers.W11 Nagata.Workers.W30 Nagata.FiniteExponents
open Nagata.W29

theorem source_actual_section_bridge_contradiction
    (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / m) (hupp : (d : ℝ) / m < Real.sqrt r)
    (hbridge : ∀ (n : ℕ) (delta : ℝ) (x : Fin 9 → ℝ),
      0 < n → 0 < delta → delta < 1 / 2 → Function.Injective x →
      (∀ i, 0 < x i ∧ x i < 1 / 2) →
      (∑ i : Fin 9, sourceOffsets x i) = delta →
      (∀ j : ℤ, 0 ≤ j → j ≤ ((n * m : ℕ) : ℤ) →
        firstLower ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (∀ j : ℤ, ((n * m : ℕ) : ℤ) < j → j ≤ ((n * d : ℕ) : ℤ) / 3 →
        0 < ((n * d : ℕ) : ℤ) - 3 * j →
        secondLower ((n * d : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (exponentSet ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
        (3 * (Real.sqrt r - 3)) delta).Nonempty →
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        ∃ (gammaL gammaP z0 : ℂ) (P : ℂ → ℂ)
          (hP : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) (hz0 : z0 ≠ 0)
          (e : Basis (Column ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
            (3 * (Real.sqrt r - 3)) delta) ℂ
            (ActualSection (τ : ℂ) gammaL gammaP ((n * d : ℕ) : ℤ) (n * m) P))
          (F : ActualSection (τ : ℂ) gammaL gammaP ((n * d : ℕ) : ℤ) (n * m) P),
          (∀ col, ∀ᶠ z : ℂ × ℂ in 𝓝 (0, 0),
            localScalar (e col) z0 z.1 z.2 =
              Nagata.W22.basisCoefficient ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
                (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ col z.1 *
                Complex.exp ((col.val.1 : ℂ) * z.2)) ∧
          F ≠ 0 ∧ actualJetMap hP hz0 (r - 9) F = 0) : False := by
  apply source_coefficient_bridge_contradiction r d m hr hm hlow hupp
  intro n delta x hn hd0 hdhalf hxinj hxbounds hxsum hfirst hsecond hnonempty
  apply (hbridge n delta x hn hd0 hdhalf hxinj hxbounds hxsum
    hfirst hsecond hnonempty).mono
  intro τ hτ
  obtain ⟨gammaL, gammaP, z0, P, hP, hz0, e, F, hlocal, hF, hjet⟩ := hτ
  have hmatrix := actual_basisJetMatrix_eq_of_local_expressions (q := r - 9) hP hz0 e
    (Nagata.W22.basisCoefficient ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
      (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ) hlocal
  exact actual_kernel_to_coefficients hP hz0 e
    (thetaJetMatrix ((n * d : ℕ) : ℤ) (r - 9) (n * m)
      (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ) hmatrix F hF hjet

/-- Source-facing interface with universal configurations in one open chart.
Collision centers and section sequences are constructed internally. This remains
conditional on the genuine geometric existence and theta-basis identification. -/
theorem source_every_configuration_bridge_contradiction
    (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / m) (hupp : (d : ℝ) / m < Real.sqrt r)
    (hgeometry : ∀ (n : ℕ) (delta : ℝ) (x : Fin 9 → ℝ),
      0 < n → 0 < delta → delta < 1 / 2 → Function.Injective x →
      (∀ i, 0 < x i ∧ x i < 1 / 2) →
      (∑ i : Fin 9, sourceOffsets x i) = delta →
      (∀ j : ℤ, 0 ≤ j → j ≤ ((n * m : ℕ) : ℤ) →
        firstLower ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (∀ j : ℤ, ((n * m : ℕ) : ℤ) < j → j ≤ ((n * d : ℕ) : ℤ) / 3 →
        0 < ((n * d : ℕ) : ℤ) - 3 * j →
        secondLower ((n * d : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (exponentSet ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
        (3 * (Real.sqrt r - 3)) delta).Nonempty →
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        ∃ (gammaL gammaP z0 : ℂ) (P : ℂ → ℂ)
          (_ : ∀ z, z ≠ 0 → DifferentiableAt ℂ P z) (_ : z0 ≠ 0)
          (e : Basis (Column ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
            (3 * (Real.sqrt r - 3)) delta) ℂ
            (ActualSection (τ : ℂ) gammaL gammaP ((n * d : ℕ) : ℤ) (n * m) P))
          (U : Set ℂ),
          (∀ col, ∀ᶠ z : ℂ × ℂ in 𝓝 (0, 0),
            localScalar (e col) z0 z.1 z.2 =
              Nagata.W22.basisCoefficient ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
                (3 * (Real.sqrt r - 3)) delta (sourceOffsets x) τ col z.1 *
                Complex.exp ((col.val.1 : ℂ) * z.2)) ∧
          IsOpen U ∧ (0 : ℂ) ∈ U ∧
          (∀ p : Fin (r - 9) → ℂ, Function.Injective p → (∀ i, p i ∈ U) →
            ∃ F : ActualSection (τ : ℂ) gammaL gammaP ((n * d : ℕ) : ℤ) (n * m) P,
              F ≠ 0 ∧ ∀ i, Nagata.Workers.W28.HasAnalyticOrderAtLeast (𝕜 := ℂ)
                (fun z : ℂ × ℂ => localScalar F z0 z.1 z.2) (p i, 0) (n * m))) : False := by
  apply source_actual_section_bridge_contradiction r d m hr hm hlow hupp
  intro n delta x hn hd0 hdhalf hxinj hxbounds hxsum hfirst hsecond hnonempty
  apply (hgeometry n delta x hn hd0 hdhalf hxinj hxbounds hxsum
    hfirst hsecond hnonempty).mono
  intro τ hτ
  obtain ⟨gammaL, gammaP, z0, P, hP, hz0, e, U, hlocal, hU, h0, hEvery⟩ := hτ
  obtain ⟨F, hF, hker⟩ := actual_kernel_of_every_configuration hP hz0 e hU h0 hEvery
  exact ⟨gammaL, gammaP, z0, P, hP, hz0, e, F, hlocal, hF, hker⟩

end Nagata.Workers.W12

end
end

section

noncomputable section
open Module Filter Topology
open scoped BigOperators
namespace Nagata.Workers.W12
open Nagata.Workers.W10 Nagata.W20 Nagata.Workers.W11 Nagata.FiniteExponents
open Nagata.W22 Nagata.CoefficientSpaces

variable {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
  (ξ : Fin 9 → ℝ) (a delta x0 : ℝ) (d : ℤ) (m : ℕ)
  (hs : (∑ i, ξ i) = 9 * x0 - delta)
  (hd : 3 * (m : ℤ) < d)
  (hfirst : ∀ j : ℤ, 0 ≤ j → j ≤ (m : ℤ) →
    firstLower d (m : ℤ) j a delta ∉ Set.range (Int.cast : ℤ → ℝ))
  (hsecond : ∀ j : ℤ, (m : ℤ) < j → j ≤ d / 3 → 0 < d - 3 * j →
    secondLower d j a delta ∉ Set.range (Int.cast : ℤ → ℝ))

/-- The genuine global section space at the actual nine marked ray lifts. -/
def genuineSourceSections :=
  ActualSection (τ : ℂ) (tauPower τ (((∑ i, ξ i) + a) / 3))
    (-tauPower τ (∑ i, ξ i)) d m (rayMarkedSection hτ hτone ξ).val

/-- The full actual section basis indexed by all literal manuscript columns. -/
def genuineSourceBasis : Basis (Column d (m : ℤ) a delta) ℂ
    (genuineSourceSections hτ hτone ξ a d m) :=
  polynomialBasisFromSourceBases (τ : ℂ) (tauPower τ (((∑ i, ξ i) + a) / 3))
    (-tauPower τ (∑ i, ξ i)) d m a delta (rayMarkedSection hτ hτone ξ).val hd
    (rayMarkedSection_analyticOnNhd hτ hτone ξ)
    (fun _ hz => rayMarkedSection_finite_order hτ hτone ξ hz)
    (actualSourceBlockBases hτ hτone (∑ i, ξ i) a delta x0 d m hs hd hfirst hsecond)

/-- Every basis column has the exact local scalar formula used in the matrix
limit. No local-formula assumption remains. -/
theorem genuineSourceBasis_localScalar (col : Column d (m : ℤ) a delta) (x y : ℂ) :
    localScalar (genuineSourceBasis hτ hτone ξ a delta x0 d m hs hd hfirst hsecond col)
      (tauPower τ x0) x y =
      basisCoefficient d (m : ℤ) a delta (fun i => x0 - ξ i) τ col x *
        Complex.exp ((col.val.1 : ℂ) * y) := by
  apply sourceBasis_localScalar_eq_theta
  · exact actualSourceBlockBases_local hτ hτone (∑ i, ξ i) a delta x0 d m
      hs hd hfirst hsecond
  · exact rayMarkedSection_centered hτ hτone ξ x0

/-- The actual linear jet map for the genuine source sections. -/
def genuineSourceJetMap (q : ℕ) :
    genuineSourceSections hτ hτone ξ a d m →ₗ[ℂ] (Nagata.Workers.W30.JetIndex q m → ℂ) :=
  actualJetMap
    (τ := (τ : ℂ)) (γL := tauPower τ (((∑ i, ξ i) + a) / 3))
    (γP := -tauPower τ (∑ i, ξ i)) (d := d) (m := m)
    (fun z hz => (rayMarkedSection_analyticOnNhd hτ hτone ξ z hz).differentiableAt)
    (tauPower_ne_zero hτ x0) q

/-- Fully instantiated actual-basis-to-literal-matrix identity. -/
theorem genuineSourceBasis_jetMatrix (q : ℕ) :
    basisJetMatrix (K := ℂ) (V := genuineSourceSections hτ hτone ξ a d m)
      (genuineSourceBasis hτ hτone ξ a delta x0 d m hs hd hfirst hsecond)
      (genuineSourceJetMap hτ hτone ξ a x0 d m q) =
        thetaJetMatrix d q m a delta (fun i => x0 - ξ i) τ := by
  apply actual_basisJetMatrix_eq_of_local_expressions
  intro col
  exact Filter.Eventually.of_forall (fun z =>
    genuineSourceBasis_localScalar hτ hτone ξ a delta x0 d m hs hd hfirst hsecond col z.1 z.2)

include hs hd hfirst hsecond

/-- Matrix injectivity transfers to the actual global section jet map. -/
theorem genuineSourceJetMap_injective (q : ℕ)
    (hinj : Function.Injective
      (thetaJetMatrix d q m a delta (fun i => x0 - ξ i) τ).mulVec) :
    Function.Injective (genuineSourceJetMap hτ hτone ξ a x0 d m q) := by
  apply injective_of_basisJetMatrix (K := ℂ)
    (V := genuineSourceSections hτ hτone ξ a d m)
    (genuineSourceBasis hτ hτone ξ a delta x0 d m hs hd hfirst hsecond)
  rw [genuineSourceBasis_jetMatrix]
  exact hinj

end Nagata.Workers.W12

end
end

section

noncomputable section
open Module Filter Topology
open scoped BigOperators
namespace Nagata.Workers.W12
open Nagata.Workers.W10 Nagata.W20 Nagata.Workers.W11 Nagata.FiniteExponents
open Nagata.W22 Nagata.CoefficientSpaces Nagata.W29

theorem genuine_source_geometric_contradiction
    (r d m : ℕ) (hr : 10 ≤ r) (hm : 0 < m)
    (hlow : 3 < (d : ℝ) / m) (hupp : (d : ℝ) / m < Real.sqrt r)
    (hgeometry : ∀ (n : ℕ) (delta : ℝ) (x : Fin 9 → ℝ),
      0 < n → 0 < delta → delta < 1 / 2 → Function.Injective x →
      (∀ i, 0 < x i ∧ x i < 1 / 2) →
      (∑ i : Fin 9, sourceOffsets x i) = delta →
      (∀ j : ℤ, 0 ≤ j → j ≤ ((n * m : ℕ) : ℤ) →
        firstLower ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (∀ j : ℤ, ((n * m : ℕ) : ℤ) < j → j ≤ ((n * d : ℕ) : ℤ) / 3 →
        0 < ((n * d : ℕ) : ℤ) - 3 * j →
        secondLower ((n * d : ℕ) : ℤ) j
          (3 * (Real.sqrt r - 3)) delta ∉ Set.range (Int.cast : ℤ → ℝ)) →
      (exponentSet ((n * d : ℕ) : ℤ) ((n * m : ℕ) : ℤ)
        (3 * (Real.sqrt r - 3)) delta).Nonempty →
      ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
        ∃ (hτ : 0 < τ) (hτone : τ < 1) (U : Set ℂ),
          IsOpen U ∧ (0 : ℂ) ∈ U ∧
          (∀ p : Fin (r - 9) → ℂ, Function.Injective p → (∀ i, p i ∈ U) →
            ∃ F : genuineSourceSections hτ hτone x (3 * (Real.sqrt r - 3))
                ((n * d : ℕ) : ℤ) (n * m),
              F ≠ 0 ∧ ∀ i, Nagata.Workers.W28.HasAnalyticOrderAtLeast (𝕜 := ℂ)
                (fun z : ℂ × ℂ => localScalar F (tauPower τ (1 / 2)) z.1 z.2)
                (p i, 0) (n * m))) : False := by
  apply source_every_configuration_bridge_contradiction r d m hr hm hlow hupp
  intro n delta x hn hd0 hdhalf hxinj hxbounds hxsum hfirst hsecond hnonempty
  have hs : (∑ i, x i) = 9 * (1 / 2 : ℝ) - delta := by
    have hh := hxsum
    simp only [sourceOffsets, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    linarith
  have hdmreal : 3 * (m : ℝ) < d :=
    (lt_div_iff₀ (Nat.cast_pos.mpr hm)).mp hlow
  have hdm : 3 * m < d := by exact_mod_cast hdmreal
  have hscale : 3 * (n * m) < n * d := by
    calc
      3 * (n * m) = n * (3 * m) := by ring
      _ < n * d := Nat.mul_lt_mul_of_pos_left hdm hn
  have hd : 3 * (((n * m : ℕ) : ℤ)) < ((n * d : ℕ) : ℤ) := by
    exact_mod_cast hscale
  apply (hgeometry n delta x hn hd0 hdhalf hxinj hxbounds hxsum
    hfirst hsecond hnonempty).mono
  intro τ hdata
  obtain ⟨hτ, hτone, U, hU, h0, hEvery⟩ := hdata
  refine ⟨tauPower τ (((∑ i, x i) + 3 * (Real.sqrt r - 3)) / 3),
    -tauPower τ (∑ i, x i), tauPower τ (1 / 2),
    (rayMarkedSection hτ hτone x).val,
    (fun z hz => (rayMarkedSection_analyticOnNhd hτ hτone x z hz).differentiableAt),
    tauPower_ne_zero hτ (1 / 2),
    genuineSourceBasis hτ hτone x (3 * (Real.sqrt r - 3)) delta (1 / 2)
      ((n * d : ℕ) : ℤ) (n * m) hs hd hfirst hsecond,
    U, ?_, hU, h0, hEvery⟩
  intro col
  exact Filter.Eventually.of_forall (fun z =>
    genuineSourceBasis_localScalar hτ hτone x (3 * (Real.sqrt r - 3)) delta (1 / 2)
      ((n * d : ℕ) : ℤ) (n * m) hs hd hfirst hsecond col z.1 z.2)

end Nagata.Workers.W12

end
end

end OAI
