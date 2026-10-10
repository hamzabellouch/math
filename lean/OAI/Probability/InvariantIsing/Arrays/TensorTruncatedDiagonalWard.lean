import OAI.Probability.InvariantIsing.Arrays.TensorTruncatedWard

namespace OAI

/-! The one-replica diagonal Haar Ward identity for the actual finite
spin/leaf tensor model. The main quadratic coefficient has no extra factor two. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S : Type*}

def tensorRestrictionDiagonalObservable {N n : ℕ} (i j : Fin N)
    (x : S → Spin N × LabeledLeaf n) (U : SpecialOrthogonal N) (s : S) : ℝ :=
  coordinateProduct i j (specialToOrthogonal U) (x s).1

def tensorRestrictionDiagonalVariation {N n : ℕ} (i j : Fin N)
    (x : S → Spin N × LabeledLeaf n) (U : SpecialOrthogonal N) (s : S) : ℝ :=
  spinCoordinate (specialToOrthogonal U) (x s).1 j ^ 2 -
    spinCoordinate (specialToOrthogonal U) (x s).1 i ^ 2

def tensorRestrictionPrefix {N m k n d : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (U : SpecialOrthogonal N) (s : S) (a : Fin d) : ℝ :=
  tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x s) a

def tensorRestrictionPlanePrefix {N m k n d : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (U : SpecialOrthogonal N) (s : S) (a : Fin d) : ℝ :=
  tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree amplitude n v i j (x s) a

theorem tensorRestriction_diagonal_ward_prefix [Fintype S] {N m k n d : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (hij : i ≠ j) :
    let C := tensorRestrictionPrefix (d := d + 1) I degree amplitude v x
    let D := tensorRestrictionPlanePrefix (d := d + 1) I degree amplitude v x i j
    let H := tensorRestrictionBase eig c x
    let O := tensorRestrictionDiagonalObservable i j x
    (∫ U, (∫ g, finiteGibbsVariation w (fun s => H U s + linearGaussian (C U) g s)
        (O U) (fun s => (eig i - eig j) * O U s) (tensorRestrictionDiagonalVariation i j x U)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) +
      ∫ g, gaussianWardCorrection w (fun s => H U s + linearGaussian (C U) g s)
        (O U) (gaussianCross (D U) (C U))
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) ∂μ) = 0 := by
  intro C D H O
  let R := specialPlaneRotation i j
  let dH := fun (t : ℝ) (U : SpecialOrthogonal N) (s : S) => (eig i - eig j) * O (R t * U) s
  let dO := fun (t : ℝ) (U : SpecialOrthogonal N) => tensorRestrictionDiagonalVariation i j x (R t * U)
  let dC := fun (t : ℝ) (U : SpecialOrthogonal N) => D (R t * U)
  have hR : R 0 = 1 := specialPlaneRotation_zero i j
  have hOm (s : S) : Measurable (fun U => O U s) :=
    ((measurable_spinCoordinate (x s).1 i).mul (measurable_spinCoordinate (x s).1 j)).comp
      measurable_specialToOrthogonal
  have hHm (s : S) : Measurable (fun U => H U s) :=
    (measurable_orbitHamiltonian eig c (x s).1).comp measurable_specialToOrthogonal
  have hCm (s : S) (a : Fin (d + 1)) : Measurable (fun U => C U s a) :=
    measurable_tensorNamespacedCoefficient I degree amplitude n v (x s) a
  have hdHm (s : S) : Measurable (fun U => dH 0 U s) := by
    simpa only [dH, hR, one_mul] using (hOm s).const_mul (eig i - eig j)
  have hdOm (s : S) : Measurable (fun U => dO 0 U s) := by
    simp only [dO, hR, one_mul, tensorRestrictionDiagonalVariation]
    exact (((measurable_spinCoordinate (x s).1 j).pow_const 2).sub
      ((measurable_spinCoordinate (x s).1 i).pow_const 2)).comp measurable_specialToOrthogonal
  have hdCm (s : S) (a : Fin (d + 1)) : Measurable (fun U => dC 0 U s a) := by
    simp only [dC, hR, one_mul, D, tensorRestrictionPlanePrefix]
    exact (measurable_tensorNamespacedPlaneCoefficient I degree amplitude n v i j (x s) a).comp
      measurable_specialToOrthogonal
  have hHd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ s,
      HasDerivAt (fun r => H (R r * U) s) (dH t U s) t := by
    intro U t _ s
    simpa only [H, tensorRestrictionBase, orbitHamiltonian, dH, O, tensorRestrictionDiagonalObservable,
      R, map_mul, specialToOrthogonal_planeRotation, coordinateProduct, spinCoordinate, mul_assoc] using
      (hasDerivAt_planeRotation_energy i j (specialToOrthogonal U) eig (x s).1 t).add_const (fieldEnergy c (x s).1)
  have hOd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ s,
      HasDerivAt (fun r => O (R r * U) s) (dO t U s) t := by
    intro U t _ s
    simpa only [O, tensorRestrictionDiagonalObservable, dO, tensorRestrictionDiagonalVariation,
      R, map_mul, specialToOrthogonal_planeRotation] using
      hasDerivAt_plane_coordinateProduct i j hij (specialToOrthogonal U) (x s).1 t
  have hCd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ s a,
      HasDerivAt (fun r => C (R r * U) s a) (dC t U s a) t := by
    intro U t _ s a
    simpa only [C, D, tensorRestrictionPrefix, tensorRestrictionPlanePrefix, dC,
      ← matrixRotation_specialToOrthogonal, R, map_mul, specialToOrthogonal_planeRotation] using
      hasDerivAt_tensorNamespacedCoefficient_plane (specialToOrthogonal U) I degree amplitude n v i j (x s) a t
  have hOb : ∀ U s, |O U s| ≤ N := fun U s => abs_coordinateProduct_le i j _ (x s).1
  have hHb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ s, |dH t U s| ≤ |eig i - eig j| * N := by
    intro U t _ s
    rw [show dH t U s = (eig i - eig j) * O (R t * U) s from rfl, abs_mul]
    exact mul_le_mul_of_nonneg_left (hOb _ _) (abs_nonneg _)
  have hOdB : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ s, |dO t U s| ≤ N :=
    fun U t _ s => abs_coordinateSquareDifference_le i j _ (x s).1
  have hCdB : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ s a,
      |dC t U s a| ≤ tensorNamespacedDerivativeCap I degree amplitude n v :=
    fun U t _ s a => tensorNamespacedPlaneCoefficient_abs_le hN _ I degree amplitude n v i j (x s) a
  have hwrd := integral_special_gaussian_gibbs_rotation_identity μ R hR hw H O C hHm hOm hCm
    dH dO dC hdHm hdOm hdCm hHd hOd hCd N (|eig i - eig j| * N) N
    (fun _ => tensorNamespacedDerivativeCap I degree amplitude n v) (Nat.cast_nonneg _) hOb hHb hOdB hCdB
  simpa only [dH, dO, dC, hR, one_mul] using hwrd

def tensorRestrictionHamiltonian {N m k n : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (U : SpecialOrthogonal N) (g : ℕ → ℝ) (s : S) : ℝ :=
  tensorRestrictionBase eig c x U s +
    cylinderField (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x s)) g

def tensorRestrictionCovarianceDerivative {N m k n : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (U : SpecialOrthogonal N) (s t : S) : ℝ :=
  cylinderCross (tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree amplitude n v i j (x s))
    (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x t))

lemma tensorRestrictionPairHamiltonian_eq {N m k n : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (U : SpecialOrthogonal N) (g : ℕ → ℝ) (p : S × S) :
    tensorRestrictionPairHamiltonian eig c I degree amplitude v x U g p =
      tensorRestrictionHamiltonian eig c I degree amplitude v x U g p.1 +
        tensorRestrictionHamiltonian eig c I degree amplitude v x U g p.2 := by
  unfold tensorRestrictionPairHamiltonian tensorRestrictionPairBase tensorRestrictionHamiltonian
  ring

/-- The one-replica Ward equation for the actual full Gaussian coordinate
law on any finite spin/leaf restriction. -/
theorem tensorRestriction_diagonal_ward [Fintype S] {N m k n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (hij : i ≠ j) :
    let H := tensorRestrictionHamiltonian eig c I degree amplitude v x
    let O := tensorRestrictionDiagonalObservable i j x
    let K := tensorRestrictionCovarianceDerivative I degree amplitude v x i j
    (∫ U, (∫ g, finiteGibbsVariation w (H U g) (O U)
      (fun s => (eig i - eig j) * O U s) (tensorRestrictionDiagonalVariation i j x U)
      ∂gaussianCoordinates) +
      ∫ g, gaussianWardCorrection w (H U g) (O U) (K U) ∂gaussianCoordinates ∂μ) = 0 := by
  intro H O K
  obtain ⟨d, hC, hD⟩ := finite_tensorNamespaced_support_bound I degree amplitude n v i j x
  let Cp := tensorRestrictionPrefix (d := d + 1) I degree amplitude v x
  let Dp := tensorRestrictionPlanePrefix (d := d + 1) I degree amplitude v x i j
  let Hp := fun U g s => tensorRestrictionBase eig c x U s + linearGaussian (Cp U) g s
  have hfield (U : SpecialOrthogonal N) (g : ℕ → ℝ) (s : S) :
      H U g s = Hp U (fun a : Fin (d + 1) => g a) s := by
    change tensorRestrictionBase eig c x U s +
      cylinderField (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x s)) g = _
    simp only [← matrixRotation_specialToOrthogonal]
    rw [cylinderField_eq_prefix _ (hC (specialToOrthogonal U) s)]
    rfl
  have hkernel (U : SpecialOrthogonal N) (s t : S) :
      K U s t = gaussianCross (Dp U) (Cp U) s t :=
    cylinderCross_prefix _ _ (hD (specialToOrthogonal U) s)
  have hfield_fun (U : SpecialOrthogonal N) (g : ℕ → ℝ) :
      H U g = Hp U (fun a : Fin (d + 1) => g a) := funext (hfield U g)
  have hkernel_fun (U : SpecialOrthogonal N) : K U = gaussianCross (Dp U) (Cp U) :=
    funext fun s => funext fun t => hkernel U s t
  have hmeasH (U : SpecialOrthogonal N) (s : S) : Measurable (fun g => Hp U g s) := by
    unfold Hp linearGaussian
    fun_prop
  have hmean (U : SpecialOrthogonal N) :
      (∫ g, finiteGibbsVariation w (H U g) (O U)
        (fun s => (eig i - eig j) * O U s) (tensorRestrictionDiagonalVariation i j x U)
        ∂gaussianCoordinates) =
      ∫ g, finiteGibbsVariation w (Hp U g) (O U)
        (fun s => (eig i - eig j) * O U s) (tensorRestrictionDiagonalVariation i j x U)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
    simp_rw [hfield_fun]
    exact (gaussian_prefix_measurePreserving (d + 1)).hasLaw.integral_comp
      (measurable_finiteGibbsVariation w _ (fun _ => O U)
        (fun _ s => (eig i - eig j) * O U s) (fun _ => tensorRestrictionDiagonalVariation i j x U)
        (hmeasH U) (fun _ => measurable_const) (fun _ => measurable_const)
        (fun _ => measurable_const)).aestronglyMeasurable
  have hmeanK (U : SpecialOrthogonal N) :
      (∫ g, gaussianWardCorrection w (H U g) (O U) (K U) ∂gaussianCoordinates) =
      ∫ g, gaussianWardCorrection w (Hp U g) (O U) (gaussianCross (Dp U) (Cp U))
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
    simp_rw [hfield_fun, hkernel_fun]
    exact (gaussian_prefix_measurePreserving (d + 1)).hasLaw.integral_comp
      (measurable_gaussianWardCorrection hw (tensorRestrictionBase eig c x U) (O U)
        (Cp U) (gaussianCross (Dp U) (Cp U))).aestronglyMeasurable
  simp_rw [hmean, hmeanK]
  exact tensorRestriction_diagonal_ward_prefix hN μ hw eig c I degree amplitude v x i j hij

end InvariantIsing

end

end OAI
