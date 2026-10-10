import OAI.Geometry.RCD.Sobolev.LocalBochnerInput
import OAI.Geometry.RCD.Sobolev.PoissonReplacement
import OAI.Geometry.RCD.Sobolev.ShiftedBochnerMeasure
import OAI.Geometry.RCD.Harmonic.FirstOrderLocalization

namespace OAI

/-!
# Local constant-Laplacian calculus on the required finite span

The input is the local specialization of Gigli (2018),
Theorem 3.3.8, together with Han (2018), Proposition 3.2 and Theorem 3.3.
Local test regularity is as in Connell et al. (2021), Lemmas 2.6--2.7.
Only the span of n harmonic coordinates and two Poisson replacements is
used. The scalar shifted lower bound follows by expanding
`|Hess f - b g|² >= 0` and using `tr Hess f = Δf` on the noncollapsed
n-dimensional space.
-/

open Set Metric MeasureTheory
open scoped BigOperators NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The actual local weak equation with a constant source. -/
def IsConstantLaplacianOn (Ω : Set X) (f : SobolevSpace μ hQ) (c : ℝ) : Prop :=
  ∀ φ : SobolevSpace μ hQ, φ ∈ SobolevSpace.dirichlet μ hQ Ω →
    energyForm μ hQ f φ = -c * ∫ x in Ω, SobolevSpace.toLp μ hQ φ x ∂μ

omit [BorelSpace X] [ProperSpace X] in
theorem isConstantLaplacianOn_zero_iff (Ω : Set X) (f : SobolevSpace μ hQ) :
    IsConstantLaplacianOn μ hQ Ω f 0 ↔ IsSobolevHarmonicOn μ hQ Ω f := by
  simp only [IsConstantLaplacianOn, IsSobolevHarmonicOn, neg_zero, zero_mul]

namespace IsConstantLaplacianOn

omit [BorelSpace X] [ProperSpace X] in
theorem mono {S T : Set X} (hS : MeasurableSet S) (hst : S ⊆ T)
    {f : SobolevSpace μ hQ} {c : ℝ} (hf : IsConstantLaplacianOn μ hQ T f c) :
    IsConstantLaplacianOn μ hQ S f c := by
  intro φ hφ
  have hz := SobolevSpace.dirichlet_zero_off μ hQ S hS ⟨φ, hφ⟩
  have hz' := (ae_restrict_iff' hS.compl).mp hz
  have hiS : (∫ x in S, SobolevSpace.toLp μ hQ φ x ∂μ) =
      ∫ x, SobolevSpace.toLp μ hQ φ x ∂μ :=
    setIntegral_eq_integral_of_ae_compl_eq_zero hz'
  have hiT : (∫ x in T, SobolevSpace.toLp μ hQ φ x ∂μ) =
      ∫ x, SobolevSpace.toLp μ hQ φ x ∂μ := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hz'] with x hx hnot
    exact hx (fun hs => hnot (hst hs))
  rw [hf φ (dirichlet_mono μ hQ hst hφ), hiT, hiS]

omit [BorelSpace X] [ProperSpace X] in
theorem add {Ω : Set X} {f g : SobolevSpace μ hQ} {c d : ℝ}
    (hf : IsConstantLaplacianOn μ hQ Ω f c)
    (hg : IsConstantLaplacianOn μ hQ Ω g d) :
    IsConstantLaplacianOn μ hQ Ω (f + g) (c + d) := by
  intro φ hφ
  rw [energyForm_add_left, hf φ hφ, hg φ hφ]
  ring

omit [BorelSpace X] [ProperSpace X] in
theorem smul {Ω : Set X} {f : SobolevSpace μ hQ} {c : ℝ}
    (hf : IsConstantLaplacianOn μ hQ Ω f c) (a : ℝ) :
    IsConstantLaplacianOn μ hQ Ω (a • f) (a * c) := by
  intro φ hφ
  rw [energyForm_smul_left, hf φ hφ]
  ring

omit [BorelSpace X] [ProperSpace X] in
theorem sub {Ω : Set X} {f g : SobolevSpace μ hQ} {c d : ℝ}
    (hf : IsConstantLaplacianOn μ hQ Ω f c)
    (hg : IsConstantLaplacianOn μ hQ Ω g d) :
    IsConstantLaplacianOn μ hQ Ω (f - g) (c - d) := by
  intro φ hφ
  rw [energyForm_sub_left, hf φ hφ, hg φ hφ]
  ring

omit [BorelSpace X] [ProperSpace X] in
theorem sub_harmonic {Ω : Set X} {f g : SobolevSpace μ hQ} {c : ℝ}
    (hf : IsConstantLaplacianOn μ hQ Ω f c)
    (hg : IsConstantLaplacianOn μ hQ Ω g c) :
    IsSobolevHarmonicOn μ hQ Ω (f - g) := by
  apply (isConstantLaplacianOn_zero_iff μ hQ Ω (f - g)).mp
  simpa only [sub_self] using hf.sub μ hQ hg

omit [BorelSpace X] [ProperSpace X] in
theorem linearCombination {m : ℕ} {Ω : Set X}
    {u : Fin m → SobolevSpace μ hQ} {c : Fin m → ℝ}
    (hu : ∀ i, IsConstantLaplacianOn μ hQ Ω (u i) (c i)) (v : Euclidean m) :
    IsConstantLaplacianOn μ hQ Ω (sobolevColumnMap μ hQ u v) (∑ i, v i * c i) := by
  classical
  rw [sobolevColumnMap_apply]
  have hs : ∀ s : Finset (Fin m), IsConstantLaplacianOn μ hQ Ω
      (∑ i ∈ s, v i • u i) (∑ i ∈ s, v i * c i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro φ hφ
        simp [energyForm]
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        exact (hu i |>.smul μ hQ (v i)).add μ hQ ih
  simpa using hs Finset.univ

end IsConstantLaplacianOn

/-- local Bochner calculus, restricted to the n+2 directions
used in the Poisson comparison. The volume in the trace correction is
restricted to the interior ball and hence is finite. -/
def LocalConstantLaplacianBochnerInput {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → -κ ≤ K → ∀ (p : X) (r : ℝ), 0 < r →
    ∀ (L : ℝ≥0)
      (U : Euclidean (n + 2) →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
      (ell : Euclidean (n + 2) →ₗ[ℝ] ℝ),
      (∀ v, IsConstantLaplacianOn (hausdorff n X) hX.quadratic
        (ball p (8 * r)) (U v) (ell v)) →
      (∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * r)),
        localGamma (hausdorff n X) hX.quadratic (U v) (U v) x ≤
          (L : ℝ) ^ 2 * ‖v‖ ^ 2) →
      ∃ M : PositiveBilinearMeasure X (Euclidean (n + 2)),
        (∀ v, Nonempty (LocalHarmonicEnergy (hausdorff n X) hX.quadratic U M κ p r L v)) ∧
        ShiftedBochnerLowerBound M ((hausdorff n X).restrict (ball p (2 * r))) ell n

end RegularPointCoordinates

end

end OAI
