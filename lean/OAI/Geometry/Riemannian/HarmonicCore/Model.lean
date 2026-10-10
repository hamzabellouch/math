import Mathlib

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise

namespace HarmonicCounterexample.Main

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ

def coordinateVector (i : Fin 3) : E3 := EuclideanSpace.single i 1

structure SmoothMetric3 where
  coeff : E3 → M3
  smooth : ∀ i j, ContDiff ℝ ∞ (fun x ↦ coeff x i j)
  positive : ∀ x, (coeff x).PosDef

namespace SmoothMetric3

def inner (g : SmoothMetric3) (x v w : E3) : ℝ :=
  ∑ i, ∑ j, g.coeff x i j * v i * w j

def coordDeriv (f : E3 → ℝ) (i : Fin 3) (x : E3) : ℝ :=
  fderiv ℝ f x (coordinateVector i)

def christoffel (g : SmoothMetric3) (x : E3) (l i j : Fin 3) : ℝ :=
  (1/2 : ℝ) * ∑ q, (g.coeff x)⁻¹ l q *
    (coordDeriv (fun y ↦ g.coeff y j q) i x +
     coordDeriv (fun y ↦ g.coeff y i q) j x -
     coordDeriv (fun y ↦ g.coeff y i j) q x)

def curvature (g : SmoothMetric3) (x : E3) (l i j k : Fin 3) : ℝ :=
  coordDeriv (fun y ↦ g.christoffel y l j k) i x -
  coordDeriv (fun y ↦ g.christoffel y l i k) j x +
  ∑ q, (g.christoffel x q j k * g.christoffel x l i q -
    g.christoffel x q i k * g.christoffel x l j q)

def ricci (g : SmoothMetric3) (x : E3) (i j : Fin 3) : ℝ :=
  ∑ l, g.curvature x l l i j

def RicciNonnegative (g : SmoothMetric3) : Prop :=
  ∀ x v : E3, 0 ≤ ∑ i, ∑ j, g.ricci x i j * v i * v j

def sectionNumerator (g : SmoothMetric3) (x v w : E3) : ℝ :=
  ∑ l, ∑ i, ∑ j, ∑ k, ∑ q,
    g.coeff x l q * g.curvature x l i j k * v i * w j * w k * v q

def sectionDenominator (g : SmoothMetric3) (x v w : E3) : ℝ :=
  g.inner x v v * g.inner x w w - (g.inner x v w)^2

def pathLength (g : SmoothMetric3) (γ : ℝ → E3) : ℝ :=
  ∫ t in (0 : ℝ)..1, Real.sqrt (g.inner (γ t) (deriv γ t) (deriv γ t))

def distance (g : SmoothMetric3) (x y : E3) : ℝ :=
  sInf {l : ℝ | ∃ γ : ℝ → E3, ContDiff ℝ 1 γ ∧ γ 0 = x ∧ γ 1 = y ∧
    l = g.pathLength γ}

lemma pathLength_nonneg (g : SmoothMetric3) (γ : ℝ → E3) : 0 ≤ g.pathLength γ := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  intro t _
  exact Real.sqrt_nonneg _

lemma distance_nonneg (g : SmoothMetric3) (x y : E3) : 0 ≤ g.distance x y := by
  apply Real.sInf_nonneg
  rintro l ⟨γ, _, _, _, rfl⟩
  exact g.pathLength_nonneg γ

def Complete (g : SmoothMetric3) : Prop :=
  ∀ x : ℕ → E3,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ, N ≤ m → N ≤ n →
      g.distance (x m) (x n) < ε) →
    ∃ y : E3, Tendsto (fun n ↦ g.distance (x n) y) atTop (𝓝 0)

def EuclideanNearOrigin (g : SmoothMetric3) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ x : E3, ‖x‖ < ε → g.coeff x = 1

def laplacian (g : SmoothMetric3) (f : E3 → ℝ) (x : E3) : ℝ :=
  ∑ i, ∑ j, (g.coeff x)⁻¹ i j *
    (iteratedFDeriv ℝ 2 f x ![coordinateVector i, coordinateVector j] -
      ∑ q, g.christoffel x q i j * coordDeriv f q x)

def PolynomialGrowth (g : SmoothMetric3) (k : ℕ) (f : E3 → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C * (1 + g.distance 0 x)^k

lemma coordDeriv_add {f h : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (i : Fin 3) (x : E3) : coordDeriv (f+h) i x = coordDeriv f i x + coordDeriv h i x := by
  unfold coordDeriv
  rw [fderiv_add (hf.differentiable (by simp) x) (hh.differentiable (by simp) x)]
  rfl

lemma coordDeriv_smul {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ)
    (i : Fin 3) (x : E3) : coordDeriv (c • f) i x = c * coordDeriv f i x := by
  unfold coordDeriv
  rw [fderiv_const_smul (hf.differentiable (by simp) x)]
  rfl

lemma laplacian_add (g : SmoothMetric3) {f h : E3 → ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h) (x : E3) :
    g.laplacian (f+h) x = g.laplacian f x + g.laplacian h x := by
  unfold laplacian
  rw [iteratedFDeriv_add_apply (hf.of_le (by norm_cast)).contDiffAt
    (hh.of_le (by norm_cast)).contDiffAt]
  simp only [add_apply, coordDeriv_add hf hh, mul_add,
    Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_add_distrib]
  ring

lemma laplacian_smul (g : SmoothMetric3) {f : E3 → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) (x : E3) :
    g.laplacian (c • f) x = c * g.laplacian f x := by
  unfold laplacian
  rw [iteratedFDeriv_const_smul_apply (hf.of_le (by norm_cast)).contDiffAt]
  simp only [smul_apply, smul_eq_mul, coordDeriv_smul hf]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : (∑ q, g.christoffel x q i j * (c * coordDeriv f q x)) =
      c * ∑ q, g.christoffel x q i j * coordDeriv f q x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hs]
  ring

lemma polynomialGrowth_zero (g : SmoothMetric3) (k : ℕ) :
    g.PolynomialGrowth k 0 := by
  refine ⟨0, le_rfl, ?_⟩
  simp

lemma polynomialGrowth_add (g : SmoothMetric3) {k : ℕ} {f h : E3 → ℝ}
    (hf : g.PolynomialGrowth k f) (hh : g.PolynomialGrowth k h) :
    g.PolynomialGrowth k (f+h) := by
  rcases hf with ⟨C, hC, hf⟩
  rcases hh with ⟨D, hD, hh⟩
  refine ⟨C+D, add_nonneg hC hD, fun x ↦ ?_⟩
  calc
    |(f+h) x| ≤ |f x| + |h x| := abs_add_le _ _
    _ ≤ C*(1+g.distance 0 x)^k+D*(1+g.distance 0 x)^k := add_le_add (hf x) (hh x)
    _ = (C+D)*(1+g.distance 0 x)^k := by ring

lemma polynomialGrowth_smul (g : SmoothMetric3) {k : ℕ} {f : E3 → ℝ}
    (hf : g.PolynomialGrowth k f) (c : ℝ) : g.PolynomialGrowth k (c • f) := by
  rcases hf with ⟨C, hC, hf⟩
  refine ⟨|c| *C, mul_nonneg (abs_nonneg _) hC, fun x ↦ ?_⟩
  calc
    |(c • f) x| = |c| *|f x| := abs_mul _ _
    _ ≤ |c| *(C*(1+g.distance 0 x)^k) := mul_le_mul_of_nonneg_left (hf x) (abs_nonneg c)
    _ = |c| *C*(1+g.distance 0 x)^k := by ring

lemma laplacian_zero (g : SmoothMetric3) (x : E3) : g.laplacian 0 x = 0 := by
  simpa using g.laplacian_smul (f := (0 : E3 → ℝ)) contDiff_const 0 x

def harmonicGrowthSpace (g : SmoothMetric3) (k : ℕ) : Submodule ℝ (E3 → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ (∀ x, g.laplacian f x = 0) ∧ g.PolynomialGrowth k f}
  zero_mem' := ⟨contDiff_const, g.laplacian_zero, g.polynomialGrowth_zero k⟩
  add_mem' := by
    rintro f h ⟨hf, hfh, hfg⟩ ⟨hh, hhh, hhg⟩
    refine ⟨hf.add hh, fun x ↦ ?_, g.polynomialGrowth_add hfg hhg⟩
    rw [g.laplacian_add hf hh, hfh, hhh, add_zero]
  smul_mem' := by
    rintro c f ⟨hf, hfh, hfg⟩
    refine ⟨hf.const_smul c, fun x ↦ ?_, g.polynomialGrowth_smul hfg c⟩
    rw [g.laplacian_smul hf, hfh, mul_zero]

def harmonicDimension (g : SmoothMetric3) (k : ℕ) : Cardinal :=
  Module.rank ℝ (g.harmonicGrowthSpace k)

def volumeMeasure (g : SmoothMetric3) : Measure E3 :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (Real.sqrt (g.coeff x).det))

def HasAVR (g : SmoothMetric3) (a : ℝ) : Prop :=
  Tendsto (fun R : ℝ ↦ (g.volumeMeasure {x | g.distance 0 x < R}).toReal /
    ((volume (Metric.ball (0 : E3) 1)).toReal * R^3)) atTop (𝓝 a)

def radialVector (g : SmoothMetric3) (x : E3) : E3 :=
  WithLp.toLp 2 (fun i ↦ ∑ j, (g.coeff x)⁻¹ i j * coordDeriv (g.distance 0) j x)

def NegativeRadialSequence (g : SmoothMetric3) : Prop :=
  ∃ x : ℕ → E3, ∃ w : ℕ → E3,
    Tendsto (fun n ↦ g.distance 0 (x n)) atTop atTop ∧
    ∀ n, DifferentiableAt ℝ (g.distance 0) (x n) ∧
      0 < g.sectionDenominator (x n) (g.radialVector (x n)) (w n) ∧
      g.sectionNumerator (x n) (g.radialVector (x n)) (w n) < 0

def IsTangentConeAtInfinity (g : SmoothMetric3) (Y : Type) [MetricSpace Y]
    [ProperSpace Y] (o : Y) : Prop :=
  ∃ R : ℕ → ℝ, (∀ n, 0 < R n) ∧ Tendsto R atTop atTop ∧
    ∀ L ε : ℝ, 0 < L → 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∃ F : E3 → Y, F 0 = o ∧
        (∀ x y : E3, g.distance 0 x ≤ R n * L → g.distance 0 y ≤ R n * L →
          |dist (F x) (F y) - g.distance x y / R n| < ε) ∧
        (∀ y : Y, dist o y ≤ L - ε →
          ∃ x : E3, g.distance 0 x ≤ R n * L ∧ dist (F x) y < ε)

def TwoNonisometricTangentCones (g : SmoothMetric3) : Prop :=
  ∃ (Y Z : Type) (mY : MetricSpace Y) (mZ : MetricSpace Z)
    (pY : @ProperSpace Y mY.toPseudoMetricSpace) (pZ : @ProperSpace Z mZ.toPseudoMetricSpace)
    (y : Y) (z : Z),
      @IsTangentConeAtInfinity g Y mY pY y ∧
      @IsTangentConeAtInfinity g Z mZ pZ z ∧
      ¬ ∃ e : @IsometryEquiv Y Z mY.toPseudoEMetricSpace mZ.toPseudoEMetricSpace, e y = z

end SmoothMetric3

def euclidean : SmoothMetric3 where
  coeff := fun _ ↦ 1
  smooth := fun _ _ ↦ contDiff_const
  positive := fun _ ↦ Matrix.PosDef.one

def MainStatement : Prop :=
  ∃ k₀ : ℤ, 0 ≤ k₀ ∧ ∀ k : ℤ, k₀ ≤ k → ∃ g : SmoothMetric3,
    g.Complete ∧ g.EuclideanNearOrigin ∧ g.RicciNonnegative ∧
    ((k.toNat+2)^2 : Cardinal) ≤ g.harmonicDimension k.toNat ∧
    ((k.toNat+1)^2 : Cardinal.{0}) < ((k.toNat+2)^2 : Cardinal.{0}) ∧
    euclidean.harmonicDimension k.toNat = ((k.toNat+1)^2 : Cardinal) ∧
    g.HasAVR ((24/25 : ℝ)^2) ∧ g.TwoNonisometricTangentCones ∧
    g.NegativeRadialSequence

end HarmonicCounterexample.Main

end

end OAI
