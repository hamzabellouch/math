import Mathlib

namespace OAI

/-!
# Grand-canonical hard-sphere probability and kinetic fluctuation preliminaries

This development proves microscopic law normalization, scattering and covariance algebra,
exact centering, and compact and Gaussian-growth test estimates. The dynamics, backward Gaussian
field, and finite-dimensional limit are specified, but their existence or convergence is not proved.
The almost-everywhere deterministic flow and backward Gaussian field constructions, connected-history
estimates, sharp cumulant bounds, discrepancy and centering transfer, and finite-dimensional
convergence remain open here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace ContDiff ZeroAtInfty

namespace HardSphereFluctuations

abbrev R3 := EuclideanSpace ℝ (Fin 3)
abbrev Phase := R3 × R3
abbrev Test := Phase → ℝ
abbrev Density := ℝ → Phase → ℝ
abbrev Sphere := Metric.sphere (0 : R3) 1

def sphereArea : Measure Sphere := (volume : Measure R3).toSphere

def collisionKernel (v w σ : R3) : ℝ := max (inner ℝ (v - w) σ) 0

def scatterLeft (v w σ : R3) : R3 := v - (inner ℝ (v - w) σ) • σ

def scatterRight (v w σ : R3) : R3 := w + (inner ℝ (v - w) σ) • σ

def pairDifference (φ : Test) (x v w σ : R3) : ℝ :=
  φ (x, scatterLeft v w σ) + φ (x, scatterRight v w σ) - φ (x, v) - φ (x, w)

def latticePoint (a : Fin 3 → ℤ) : R3 := WithLp.toLp 2 (fun j => (a j : ℝ))

def bolNorm {E : Type*} [NormedAddCommGroup E] (b : ℝ) (g : Phase → E) : ℝ≥0∞ :=
  ∑' a : Fin 3 → ℤ,
    ⨆ (x : R3) (_ : ‖x - latticePoint a‖ ≤ 1) (v : R3),
      ENNReal.ofReal (Real.exp (b * ‖v‖ ^ 2) * ‖g (x, v)‖)

def spatialDerivative (g : Test) (z : Phase) : R3 →L[ℝ] ℝ :=
  fderiv ℝ (fun x : R3 => g (x, z.2)) z.1

def boltzmannQ (g : Test) (z : Phase) : ℝ :=
  ∫ p : R3 × Sphere,
    collisionKernel z.2 p.1 p.2 *
      (g (z.1, scatterLeft z.2 p.1 p.2) * g (z.1, scatterRight z.2 p.1 p.2) -
        g z * g (z.1, p.1))
    ∂((volume : Measure R3).prod sphereArea)

structure ClassicalBoltzmann (T : ℝ) (f₀ : Test) (f : Density) : Prop where
  continuous : ContinuousOn (fun p : ℝ × Phase => f p.1 p.2) (Icc 0 T ×ˢ univ)
  nonnegative : ∀ t ∈ Icc 0 T, ∀ z, 0 ≤ f t z
  initial : f 0 = f₀
  classical : ∀ v : R3,
    ContDiffOn ℝ 1 (fun p : ℝ × R3 => f p.1 (p.2, v)) (Ioo 0 T ×ˢ univ)
  equation : ∀ t ∈ Ioo 0 T, ∀ z : Phase,
    deriv (fun s => f s z) t + spatialDerivative (f t) z z.2 = boltzmannQ (f t) z

structure KineticAssumption (β T : ℝ) (f₀ : Test) (f : Density) : Prop where
  beta_pos : 0 < β
  time_pos : 0 < T
  initial_smooth : ContDiff ℝ ∞ f₀
  initial_nonnegative : ∀ z, 0 ≤ f₀ z
  initial_integrable : Integrable f₀ (volume : Measure Phase)
  initial_mass : ∫ z, f₀ z = 1
  initial_bol : bolNorm (2 * β) f₀ + bolNorm (2 * β) (spatialDerivative f₀) < ⊤
  solution : ClassicalBoltzmann T f₀ f
  gaussian_bound : ∃ M : ℝ, ∀ t ∈ Icc 0 T, ∀ z : Phase,
    Real.exp (2 * β * ‖z.2‖ ^ 2) * f t z ≤ M

def collisionDrift (f : Density) (t : ℝ) (φ : Test) (z : Phase) : ℝ :=
  ∫ p : R3 × Sphere,
    collisionKernel z.2 p.1 p.2 * f t (z.1, p.1) * pairDifference φ z.1 z.2 p.1 p.2
    ∂((volume : Measure R3).prod sphereArea)

def drift (f : Density) (t : ℝ) (φ : Test) (z : Phase) : ℝ :=
  spatialDerivative φ z z.2 + collisionDrift f t φ z

abbrev Collision := R3 × R3 × R3 × Sphere

def collisionBase : Measure Collision :=
  (volume : Measure R3).prod ((volume : Measure R3).prod
    ((volume : Measure R3).prod sphereArea))

def collisionWeight (f : Density) (t : ℝ) (p : Collision) : ℝ :=
  (1 / 2 : ℝ) * collisionKernel p.2.1 p.2.2.1 p.2.2.2 *
    f t (p.1, p.2.1) * f t (p.1, p.2.2.1)

def collisionDifference (φ : Test) (p : Collision) : ℝ :=
  pairDifference φ p.1 p.2.1 p.2.2.1 p.2.2.2

def collisionCovariance (f : Density) (t : ℝ) (φ ψ : Test) : ℝ :=
  ∫ p, collisionWeight f t p * collisionDifference φ p * collisionDifference ψ p
    ∂collisionBase

def initialCovariance (f₀ φ ψ : Test) : ℝ := ∫ z, f₀ z * φ z * ψ z

abbrev CompactTest := {φ : Test // ContDiff ℝ ∞ φ ∧ HasCompactSupport φ}

abbrev TestCoordinates := C₀(Phase, ℝ)

def testAtExponent (a : ℝ) (h : TestCoordinates) : Test :=
  fun z => Real.exp (a * ‖z.2‖ ^ 2) * h z

def InTestSpace (a : ℝ) (h : Test) : Prop := ∃ k : TestCoordinates, testAtExponent a k = h

def SmallTest (β : ℝ) (h : Test) : Prop := ∃ a : ℝ, 0 ≤ a ∧ a < β ∧ InTestSpace a h

abbrev SmallTests (β : ℝ) := {h : Test // SmallTest β h}

def freeTransport (u : ℝ) (h : Test) : Test := fun z => h (z.1 + u • z.2, z.2)

abbrev Propagator := ℝ → ℝ → Test → Test

def BoundedOnScales (β T : ℝ) (U : Propagator) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b → b < 2 * β →
    ∃ V : ℝ → ℝ → TestCoordinates →L[ℝ] TestCoordinates,
      (∀ r ∈ Icc 0 T, ∀ t ∈ Icc r T, ∀ h,
        U r t (testAtExponent a h) = testAtExponent b (V r t h)) ∧
      (∃ C : ℝ, ∀ r ∈ Icc 0 T, ∀ t ∈ Icc r T, ‖V r t‖ ≤ C)

structure IsBackwardPropagator (β T : ℝ) (f : Density) (U : Propagator) : Prop where
  bounded : BoundedOnScales β T U
  diagonal : ∀ a, 0 ≤ a → a < 2 * β → ∀ t ∈ Icc 0 T, ∀ h,
    U t t (testAtExponent a h) = testAtExponent a h
  time_integrable : ∀ a b, 0 ≤ a → a < b → b < 2 * β →
    ∀ r ∈ Icc 0 T, ∀ t ∈ Icc r T, ∀ h : TestCoordinates, ∀ z,
      IntervalIntegrable (fun s => freeTransport (s - r)
        (collisionDrift f s (U s t (testAtExponent a h))) z) volume r t
  mild : ∀ a b, 0 ≤ a → a < b → b < 2 * β →
    ∀ r ∈ Icc 0 T, ∀ t ∈ Icc r T, ∀ h : TestCoordinates, ∀ z,
      U r t (testAtExponent a h) z = freeTransport (t - r) (testAtExponent a h) z +
        ∫ s in r..t, freeTransport (s - r)
          (collisionDrift f s (U s t (testAtExponent a h))) z
  composition : ∀ a, 0 ≤ a → a < 2 * β → ∀ r ∈ Icc 0 T,
    ∀ s ∈ Icc r T, ∀ t ∈ Icc s T, ∀ h : TestCoordinates,
      U r s (U s t (testAtExponent a h)) = U r t (testAtExponent a h)

abbrev Configuration (N : ℕ) := Fin N → Phase
abbrev Microstate := (N : ℕ) × Configuration N

def admissible (ε : ℝ) (N : ℕ) : Set (Configuration N) :=
  {Z | ∀ i j, i ≠ j → ε < ‖(Z i).1 - (Z j).1‖}

def particleIntensity (ε : ℝ) : ℝ := (ε ^ 2)⁻¹

def sectorLaw (f₀ : Test) (ε : ℝ) (N : ℕ) : Measure (Configuration N) := by
  classical
  exact (volume : Measure (Configuration N)).withDensity (fun Z =>
    if Z ∈ admissible ε N then
      ENNReal.ofReal (particleIntensity ε ^ N / (N.factorial : ℝ)) *
        ∏ i, ENNReal.ofReal (f₀ (Z i))
    else 0)

def grandCanonicalRaw (f₀ : Test) (ε : ℝ) : Measure Microstate :=
  Measure.sum (fun N => Measure.map (Sigma.mk N) (sectorLaw f₀ ε N))

def partitionFunction (f₀ : Test) (ε : ℝ) : ℝ≥0∞ :=
  grandCanonicalRaw f₀ ε univ

def grandCanonical (f₀ : Test) (ε : ℝ) : Measure Microstate :=
  (partitionFunction f₀ ε)⁻¹ • grandCanonicalRaw f₀ ε

def freeFlight {N : ℕ} (t : ℝ) (Z : Configuration N) : Configuration N :=
  fun i => ((Z i).1 + t • (Z i).2, (Z i).2)

def OneElasticImpact {N : ℕ} (ε : ℝ) (Z Z' : Configuration N) : Prop :=
  ∃ i j : Fin N, i ≠ j ∧
    ‖(Z j).1 - (Z i).1‖ = ε ∧
    0 < inner ℝ ((Z i).2 - (Z j).2) (ε⁻¹ • ((Z j).1 - (Z i).1)) ∧
    (∀ l, (Z' l).1 = (Z l).1) ∧
    (Z' i).2 = scatterLeft (Z i).2 (Z j).2 (ε⁻¹ • ((Z j).1 - (Z i).1)) ∧
    (Z' j).2 = scatterRight (Z i).2 (Z j).2 (ε⁻¹ • ((Z j).1 - (Z i).1)) ∧
    (∀ l, l ≠ i → l ≠ j → (Z' l).2 = (Z l).2) ∧
    (∀ l h, l ≠ h → ¬ (l = i ∧ h = j) → ¬ (l = j ∧ h = i) →
      ε < ‖(Z l).1 - (Z h).1‖)

def IsRegularTrajectory {N : ℕ} (ε T : ℝ) (Z : Configuration N)
    (q : ℝ → Configuration N) : Prop :=
  Z ∈ admissible ε N ∧ ∃ k : ℕ, ∃ τ : ℕ → ℝ, ∃ Q : ℕ → Configuration N,
    τ 0 = 0 ∧ τ (k + 1) = T ∧ StrictMonoOn τ (Icc 0 (k + 1)) ∧ Q 0 = Z ∧
    (∀ j ≤ k, ∀ t ∈ Ico (τ j) (τ (j + 1)), q t = freeFlight (t - τ j) (Q j)) ∧
    q T = freeFlight (T - τ k) (Q k) ∧ q T ∈ admissible ε N ∧
    (∀ j < k, OneElasticImpact ε (freeFlight (τ (j + 1) - τ j) (Q j)) (Q (j + 1))) ∧
    (∀ t ∈ Icc 0 T, ∀ i j, i ≠ j → ε ≤ ‖(q t i).1 - (q t j).1‖)

abbrev Dynamics := ℝ → ℝ → (N : ℕ) → Configuration N → Configuration N

def IsHardSphereDynamics (T : ℝ) (S : Dynamics) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    (∀ t ∈ Icc 0 T, Measurable (S ε t N)) ∧
    (∀ᵐ Z ∂((volume : Measure (Configuration N)).restrict (admissible ε N)),
      IsRegularTrajectory ε T Z (fun t => S ε t N Z) ∧
      ∀ q : ℝ → Configuration N, IsRegularTrajectory ε T Z q →
        ∀ t ∈ Icc 0 T, q t = S ε t N Z)

def empirical (ε : ℝ) (S : Dynamics) (t : ℝ) (φ : Test) (Z : Microstate) : ℝ :=
  (particleIntensity ε)⁻¹ * ∑ i, φ (S ε t Z.1 Z.2 i)

def microscopicFluctuation (f₀ : Test) (ε : ℝ) (S : Dynamics) (t : ℝ)
    (φ : Test) (Z : Microstate) : ℝ :=
  Real.sqrt (particleIntensity ε) *
    (empirical ε S t φ Z - ∫ Z', empirical ε S t φ Z' ∂grandCanonical f₀ ε)

def initialMeasure (f₀ : Test) : Measure Phase :=
  (volume : Measure Phase).withDensity (fun z => ENNReal.ofReal (f₀ z))

abbrev SpaceTimeCollision := ℝ × Collision

def noiseMeasure (T : ℝ) (f : Density) : Measure SpaceTimeCollision :=
  ((volume.restrict (Icc 0 T)).prod collisionBase).withDensity
    (fun p => ENNReal.ofReal (collisionWeight f p.1 p.2))

abbrev L2 {X : Type*} [MeasurableSpace X] (μ : Measure X) := Lp ℝ 2 μ

def toL2 {X : Type*} [MeasurableSpace X] (μ : Measure X) (h : X → ℝ) : L2 μ := by
  classical
  exact if hh : MemLp h 2 μ then hh.toLp h else 0

def constantNoiseKernel (t : ℝ) (h : Test) : SpaceTimeCollision → ℝ :=
  fun p => if p.1 ∈ Icc 0 t then collisionDifference h p.2 else 0

def backwardNoiseKernel (U : Propagator) (t : ℝ) (h : Test) : SpaceTimeCollision → ℝ :=
  fun p => if p.1 ∈ Icc 0 t then collisionDifference (U p.1 t h) p.2 else 0

structure IsonormalPair (T : ℝ) (f₀ : Test) (f : Density)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) where
  initial : L2 (initialMeasure f₀) →L[ℝ] L2 P
  source : L2 (noiseMeasure T f) →L[ℝ] L2 P
  initial_law : ∀ h, Measure.map (initial h) P = gaussianReal 0 (‖h‖₊ ^ 2)
  source_law : ∀ h, Measure.map (source h) P = gaussianReal 0 (‖h‖₊ ^ 2)
  independent : IndepFun
    (fun o : Ω => fun h : L2 (initialMeasure f₀) => initial h o)
    (fun o : Ω => fun h : L2 (noiseMeasure T f) => source h o) P

def gaussianNoise {T : ℝ} {f₀ : Test} {f : Density}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (G : IsonormalPair T f₀ f Ω P) (t : ℝ) (h : Test) : L2 P :=
  G.source (toL2 (noiseMeasure T f) (constantNoiseKernel t h))

def mildField {T : ℝ} {f₀ : Test} {f : Density}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (U : Propagator) (G : IsonormalPair T f₀ f Ω P) (t : ℝ) (h : Test) : L2 P :=
  G.initial (toL2 (initialMeasure f₀) (U 0 t h)) +
    G.source (toL2 (noiseMeasure T f) (backwardNoiseKernel U t h))

def CenteredGaussianFamily {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : I → Ω → ℝ) : Prop :=
  ∀ n : ℕ, ∀ idx : Fin n → I, ∀ a : Fin n → ℝ, ∃ v : ℝ≥0,
    Measure.map (fun o => ∑ i, a i * X (idx i) o) P = gaussianReal 0 v

structure IsFluctuationField (β T : ℝ) (f₀ : Test) (f : Density)
    (U : Propagator) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (G : IsonormalPair T f₀ f Ω P) : Prop where
  kernel_integrable : ∀ h : SmallTests β, ∀ t ∈ Icc 0 T,
    MemLp (U 0 t h) 2 (initialMeasure f₀) ∧
    MemLp (backwardNoiseKernel U t h) 2 (noiseMeasure T f) ∧
    MemLp (constantNoiseKernel t h) 2 (noiseMeasure T f)
  initial_integrable : ∀ h : SmallTests β, MemLp (h : Test) 2 (initialMeasure f₀)
  field_bounded_linear : ∀ a, 0 ≤ a → a < β →
    ∃ L : ℝ → TestCoordinates →L[ℝ] L2 P,
      (∀ t ∈ Icc 0 T, ∀ h, mildField U G t (testAtExponent a h) = L t h) ∧
      ∃ C : ℝ, ∀ t ∈ Icc 0 T, ‖L t‖ ≤ C
  centered_gaussian : CenteredGaussianFamily P
    (fun p : Icc (0 : ℝ) T × SmallTests β => (mildField U G p.1 p.2 : Ω → ℝ))
  noise_centered_gaussian : CenteredGaussianFamily P
    (fun p : Icc (0 : ℝ) T × SmallTests β => (gaussianNoise G p.1 p.2 : Ω → ℝ))
  drift_test : ∀ h : CompactTest, ∀ t ∈ Icc 0 T, SmallTest β (drift f t h)
  drift_integrable : ∀ h : CompactTest, ∀ t ∈ Icc 0 T,
    IntervalIntegrable (fun s => mildField U G s (drift f s h)) volume 0 t
  weak_equation : ∀ h : CompactTest, ∀ t ∈ Icc 0 T,
    mildField U G t h = mildField U G 0 h +
      (∫ s in 0..t, mildField U G s (drift f s h)) + gaussianNoise G t h
  initial_independent : IndepFun
    (fun o : Ω => fun h : SmallTests β => mildField U G 0 h o)
    (fun o : Ω => fun p : Icc (0 : ℝ) T × SmallTests β => gaussianNoise G p.1 p.2 o) P
  initial_covariance : ∀ h k : SmallTests β,
    (∫ o, mildField U G 0 h o * mildField U G 0 k o ∂P) = initialCovariance f₀ h k
  covariance_integrable : ∀ h k : SmallTests β,
    IntervalIntegrable (fun r => collisionCovariance f r h k) volume 0 T
  noise_covariance : ∀ h k : SmallTests β, ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T,
    (∫ o, gaussianNoise G t h o * gaussianNoise G s k o ∂P) =
      ∫ r in 0..min t s, collisionCovariance f r h k
  independent_increments : ∀ n : ℕ, ∀ τ : Fin (n + 1) → ℝ,
    (∀ i, τ i ∈ Icc 0 T) → Monotone τ →
      iIndepFun (fun i : Fin n => fun o : Ω => fun h : SmallTests β =>
        (gaussianNoise G (τ i.succ) h - gaussianNoise G (τ i.castSucc) h) o) P
  backward_covariance : ∀ h k : SmallTests β, ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 T,
    (∫ o, mildField U G t h o * mildField U G s k o ∂P) =
      initialCovariance f₀ (U 0 t h) (U 0 s k) +
        ∫ r in 0..min t s, collisionCovariance f r (U r t h) (U r s k)

def FiniteDimensionalLimit (T : ℝ) (f₀ : Test) (S : Dynamics)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ → Test → L2 P) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ ts : Fin m → ℝ, (∀ i, ts i ∈ Icc 0 T) →
    ∀ hs : Fin m → CompactTest, ∀ F : BoundedContinuousFunction (Fin m → ℝ) ℝ,
      Tendsto
        (fun ε => ∫ Z, F (fun i => microscopicFluctuation f₀ ε S (ts i) (hs i) Z)
          ∂grandCanonical f₀ ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ o, F (fun i => X (ts i) (hs i) o) ∂P))

structure ProbabilitySpaceData where
  carrier : Type
  measurable : MeasurableSpace carrier
  law : @Measure carrier measurable
  probability : @IsProbabilityMeasure carrier measurable law

attribute [instance] ProbabilitySpaceData.measurable ProbabilitySpaceData.probability

end HardSphereFluctuations

namespace HardSphereFluctuations

theorem collisionKernel_nonnegative (v w σ : R3) : 0 ≤ collisionKernel v w σ :=
  le_max_right _ _

theorem scatter_momentum (v w σ : R3) :
    scatterLeft v w σ + scatterRight v w σ = v + w := by
  unfold scatterLeft scatterRight
  abel

theorem scatter_energy (v w σ : R3) (hσ : ‖σ‖ = 1) :
    ‖scatterLeft v w σ‖ ^ 2 + ‖scatterRight v w σ‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  unfold scatterLeft scatterRight
  rw [norm_sub_sq_real, norm_add_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, hσ, mul_one, sq_abs,
    inner_sub_left]
  ring

theorem scatter_normal_reversed (v w σ : R3) (hσ : ‖σ‖ = 1) :
    inner ℝ (scatterLeft v w σ - scatterRight v w σ) σ = -inner ℝ (v - w) σ := by
  simp only [scatterLeft, scatterRight, inner_sub_left, inner_add_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, hσ]
  ring

theorem scatterLeft_involutive (v w σ : R3) (hσ : ‖σ‖ = 1) :
    scatterLeft (scatterLeft v w σ) (scatterRight v w σ) σ = v := by
  change scatterLeft v w σ -
    (inner ℝ (scatterLeft v w σ - scatterRight v w σ) σ) • σ = v
  rw [scatter_normal_reversed v w σ hσ]
  simp [scatterLeft, neg_smul]

theorem scatterRight_involutive (v w σ : R3) (hσ : ‖σ‖ = 1) :
    scatterRight (scatterLeft v w σ) (scatterRight v w σ) σ = w := by
  change scatterRight v w σ +
    (inner ℝ (scatterLeft v w σ - scatterRight v w σ) σ) • σ = w
  rw [scatter_normal_reversed v w σ hσ]
  simp [scatterRight, neg_smul]

theorem collisionKernel_prepost (v w σ : R3) (hσ : ‖σ‖ = 1) :
    collisionKernel (scatterLeft v w σ) (scatterRight v w σ) (-σ) =
      collisionKernel v w σ := by
  unfold collisionKernel
  rw [inner_neg_right, scatter_normal_reversed v w σ hσ, neg_neg]

theorem pairDifference_linear (φ ψ : Test) (a b : ℝ) (x v w σ : R3) :
    pairDifference (fun z => a * φ z + b * ψ z) x v w σ =
      a * pairDifference φ x v w σ + b * pairDifference ψ x v w σ := by
  unfold pairDifference
  ring

theorem pairDifference_constant (c : ℝ) (x v w σ : R3) :
    pairDifference (fun _ => c) x v w σ = 0 := by
  simp [pairDifference]

theorem pairDifference_momentum (u x v w σ : R3) :
    pairDifference (fun z => inner ℝ z.2 u) x v w σ = 0 := by
  simp only [pairDifference, scatterLeft, scatterRight, inner_sub_left,
    inner_add_left, real_inner_smul_left]
  ring

theorem pairDifference_energy (x v w σ : R3) (hσ : ‖σ‖ = 1) :
    pairDifference (fun z => ‖z.2‖ ^ 2) x v w σ = 0 := by
  unfold pairDifference
  rw [scatter_energy v w σ hσ]
  ring

theorem covariance_source_algebra
    (a b a' b' c d c' d' : ℝ) :
    ((a' * c' + b' * d' - a * c - b * d) +
      (a' * d' + b' * c' - a * d - b * c)) -
      ((c + d) * (a' + b' - a - b) + (a + b) * (c' + d' - c - d)) =
      (a' + b' - a - b) * (c' + d' - c - d) := by
  ring

theorem collisionWeight_nonnegative (f : Density) (t : ℝ)
    (hf : ∀ z, 0 ≤ f t z) (p : Collision) : 0 ≤ collisionWeight f t p := by
  unfold collisionWeight
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (collisionKernel_nonnegative _ _ _)) (hf _)) (hf _)

theorem collisionCovariance_symmetric (f : Density) (t : ℝ) (φ ψ : Test) :
    collisionCovariance f t φ ψ = collisionCovariance f t ψ φ := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun p => by ring)

theorem collisionCovariance_nonnegative (f : Density) (t : ℝ)
    (hf : ∀ z, 0 ≤ f t z) (φ : Test) : 0 ≤ collisionCovariance f t φ φ := by
  apply integral_nonneg
  intro p
  change 0 ≤ collisionWeight f t p * collisionDifference φ p * collisionDifference φ p
  have h := mul_nonneg (collisionWeight_nonnegative f t hf p)
    (sq_nonneg (collisionDifference φ p))
  nlinarith only [h]

theorem initialCovariance_symmetric (f₀ φ ψ : Test) :
    initialCovariance f₀ φ ψ = initialCovariance f₀ ψ φ := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by ring)

theorem initialCovariance_nonnegative (f₀ : Test) (hf : ∀ z, 0 ≤ f₀ z) (φ : Test) :
    0 ≤ initialCovariance f₀ φ φ := by
  apply integral_nonneg
  intro z
  change 0 ≤ f₀ z * φ z * φ z
  have h := mul_nonneg (hf z) (sq_nonneg (φ z))
  nlinarith only [h]

theorem sqrt_particleIntensity (ε : ℝ) (hε : 0 < ε) :
    Real.sqrt (particleIntensity ε) = ε⁻¹ := by
  simp [particleIntensity, Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos hε]

theorem microscopicFluctuation_integral_zero
    (f₀ : Test) (ε : ℝ) (S : Dynamics) (t : ℝ) (φ : Test)
    [IsProbabilityMeasure (grandCanonical f₀ ε)]
    (hi : Integrable (empirical ε S t φ) (grandCanonical f₀ ε)) :
    ∫ Z, microscopicFluctuation f₀ ε S t φ Z ∂grandCanonical f₀ ε = 0 := by
  unfold microscopicFluctuation
  rw [integral_const_mul, integral_sub hi (integrable_const _)]
  simp

theorem toL2_ae {X : Type*} [MeasurableSpace X] (μ : Measure X) (h : X → ℝ)
    (hh : MemLp h 2 μ) : (toL2 μ h : X → ℝ) =ᵐ[μ] h := by
  simp only [toL2, dite_eq_left hh]
  exact hh.coeFn_toLp

end HardSphereFluctuations

namespace HardSphereFluctuations

theorem product_density_lintegral (f₀ : Test)
    (hn : ∀ z, 0 ≤ f₀ z) (hi : Integrable f₀ (volume : Measure Phase))
    (hm : ∫ z, f₀ z = 1) (N : ℕ) :
    (∫⁻ Z : Configuration N, ∏ i, ENNReal.ofReal (f₀ (Z i))) = 1 := by
  have hp : Integrable (fun Z : Configuration N => ∏ i, f₀ (Z i)) volume :=
    Integrable.fintype_prod (fun _ => hi)
  have hp₀ : ∀ Z : Configuration N, 0 ≤ ∏ i, f₀ (Z i) :=
    fun Z => Finset.prod_nonneg (fun i _ => hn (Z i))
  calc
    _ = ∫⁻ Z : Configuration N, ENNReal.ofReal (∏ i, f₀ (Z i)) := by
      apply lintegral_congr
      intro Z
      exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => hn (Z i))).symm
    _ = ENNReal.ofReal (∫ Z : Configuration N, ∏ i, f₀ (Z i)) :=
      (ofReal_integral_eq_lintegral_ofReal hp (Filter.Eventually.of_forall hp₀)).symm
    _ = 1 := by
      rw [integral_fin_nat_prod_volume_eq_prod (fun _ => f₀)]
      simp [hm]

theorem sector_mass_le (f₀ : Test) (ε : ℝ)
    (hn : ∀ z, 0 ≤ f₀ z) (hi : Integrable f₀ (volume : Measure Phase))
    (hm : ∫ z, f₀ z = 1) (N : ℕ) :
    sectorLaw f₀ ε N univ ≤ ENNReal.ofReal (particleIntensity ε ^ N / (N.factorial : ℝ)) := by
  classical
  unfold sectorLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    _ ≤ ∫⁻ Z : Configuration N,
        ENNReal.ofReal (particleIntensity ε ^ N / (N.factorial : ℝ)) *
          ∏ i, ENNReal.ofReal (f₀ (Z i)) := by
      apply lintegral_mono
      intro Z
      dsimp only
      split_ifs <;> simp
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        product_density_lintegral f₀ hn hi hm N, mul_one]

theorem sector_zero_mass (f₀ : Test) (ε : ℝ) : sectorLaw f₀ ε 0 univ = 1 := by
  classical
  simp [sectorLaw, admissible]
  exact Measure.pi_empty_univ (fun _ : Fin 0 => (volume : Measure Phase))

theorem partitionFunction_eq_tsum (f₀ : Test) (ε : ℝ) :
    partitionFunction f₀ ε = ∑' N, sectorLaw f₀ ε N univ := by
  unfold partitionFunction grandCanonicalRaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  apply tsum_congr
  intro N
  have hs : Measurable (Sigma.mk N : Configuration N → Microstate) :=
    measurable_iff_le_map.mpr (iInf_le _ N)
  rw [Measure.map_apply hs MeasurableSet.univ, Set.preimage_univ]

theorem one_le_partitionFunction (f₀ : Test) (ε : ℝ) : 1 ≤ partitionFunction f₀ ε := by
  rw [partitionFunction_eq_tsum, ← sector_zero_mass f₀ ε]
  exact ENNReal.le_tsum (f := fun particleCount => sectorLaw f₀ ε particleCount univ) 0

theorem partitionFunction_le_exp (f₀ : Test) (ε : ℝ)
    (hn : ∀ z, 0 ≤ f₀ z) (hi : Integrable f₀ (volume : Measure Phase))
    (hm : ∫ z, f₀ z = 1) :
    partitionFunction f₀ ε ≤ ENNReal.ofReal (Real.exp (particleIntensity ε)) := by
  have hsum : HasSum (fun N : ℕ => particleIntensity ε ^ N / (N.factorial : ℝ))
      (Real.exp (particleIntensity ε)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hnn : ∀ N : ℕ, 0 ≤ particleIntensity ε ^ N / (N.factorial : ℝ) := by
    intro N
    unfold particleIntensity
    positivity
  calc
    _ = ∑' N, sectorLaw f₀ ε N univ := partitionFunction_eq_tsum f₀ ε
    _ ≤ ∑' N, ENNReal.ofReal (particleIntensity ε ^ N / (N.factorial : ℝ)) :=
      ENNReal.tsum_le_tsum (sector_mass_le f₀ ε hn hi hm)
    _ = ENNReal.ofReal (Real.exp (particleIntensity ε)) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable, hsum.tsum_eq]

theorem grandCanonical_isProbability (f₀ : Test) (ε : ℝ)
    (hn : ∀ z, 0 ≤ f₀ z) (hi : Integrable f₀ (volume : Measure Phase))
    (hm : ∫ z, f₀ z = 1) : IsProbabilityMeasure (grandCanonical f₀ ε) := by
  have hp : partitionFunction f₀ ε ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_partitionFunction f₀ ε))
  have hf : partitionFunction f₀ ε ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (partitionFunction_le_exp f₀ ε hn hi hm) ENNReal.ofReal_lt_top)
  constructor
  change (partitionFunction f₀ ε)⁻¹ * partitionFunction f₀ ε = 1
  exact ENNReal.inv_mul_cancel hp hf

end HardSphereFluctuations

namespace HardSphereFluctuations

theorem compactTest_small (β : ℝ) (hβ : 0 < β) (φ : CompactTest) :
    SmallTest β φ := by
  let k : TestCoordinates :=
    { toFun := φ
      continuous_toFun := φ.2.1.continuous
      zero_at_infty' := φ.2.2.is_zero_at_infty }
  refine ⟨0, le_rfl, hβ, k, ?_⟩
  funext z
  simp [testAtExponent, k]

theorem testAtExponent_bound (a : ℝ) (h : TestCoordinates) (z : Phase) :
    |testAtExponent a h z| ≤ ‖h‖ * Real.exp (a * ‖z.2‖ ^ 2) := by
  have hb : |h z| ≤ ‖h‖ := by
    simpa only [Real.norm_eq_abs, ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
      ZeroAtInftyContinuousMap.toBCF_apply]
      using h.toBCF.norm_coe_le_norm z
  calc
    _ = Real.exp (a * ‖z.2‖ ^ 2) * |h z| := by
      rw [testAtExponent, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (a * ‖z.2‖ ^ 2) * ‖h‖ :=
      mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
    _ = _ := mul_comm _ _

theorem pairDifference_gaussian_bound (a : ℝ) (ha : 0 ≤ a)
    (h : TestCoordinates) (x v w σ : R3) (hσ : ‖σ‖ = 1) :
    |pairDifference (testAtExponent a h) x v w σ| ≤
      4 * ‖h‖ * Real.exp (a * (‖v‖ ^ 2 + ‖w‖ ^ 2)) := by
  let E : ℝ := ‖v‖ ^ 2 + ‖w‖ ^ 2
  let R : ℝ := ‖h‖ * Real.exp (a * E)
  have hb (u : R3) (hu : ‖u‖ ^ 2 ≤ E) : |testAtExponent a h (x, u)| ≤ R := by
    calc
      _ ≤ ‖h‖ * Real.exp (a * ‖u‖ ^ 2) := testAtExponent_bound a h (x, u)
      _ ≤ R := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu ha)) (norm_nonneg h)
  have he := scatter_energy v w σ hσ
  have hv' : |testAtExponent a h (x, scatterLeft v w σ)| ≤ R :=
    hb _ (by dsimp [E]; nlinarith only [he, sq_nonneg ‖scatterRight v w σ‖])
  have hw' : |testAtExponent a h (x, scatterRight v w σ)| ≤ R :=
    hb _ (by dsimp [E]; nlinarith only [he, sq_nonneg ‖scatterLeft v w σ‖])
  have hv : |testAtExponent a h (x, v)| ≤ R :=
    hb _ (by dsimp [E]; nlinarith only [sq_nonneg ‖w‖])
  have hw : |testAtExponent a h (x, w)| ≤ R :=
    hb _ (by dsimp [E]; nlinarith only [sq_nonneg ‖v‖])
  calc
    _ ≤ (|testAtExponent a h (x, scatterLeft v w σ) +
          testAtExponent a h (x, scatterRight v w σ)| +
          |testAtExponent a h (x, v)|) + |testAtExponent a h (x, w)| :=
      (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ ((|testAtExponent a h (x, scatterLeft v w σ)| +
          |testAtExponent a h (x, scatterRight v w σ)|) +
          |testAtExponent a h (x, v)|) + |testAtExponent a h (x, w)| :=
      add_le_add_left (add_le_add_left (abs_add_le _ _) _) _
    _ ≤ (R + R) + R + R := add_le_add (add_le_add (add_le_add hv' hw') hv) hw
    _ = _ := by dsimp [R, E]; ring

end HardSphereFluctuations

end

end OAI
