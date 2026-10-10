import OAI.Probability.InvariantIsing.Arrays.TensorHaarWard

namespace OAI

/-! The finite spin/leaf pair application of the spectral Haar Ward identity.
The spin test is fixed under rotations and may be any function of total
overlap. Arbitrary finite leaf restrictions and zero prior weights are allowed. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

variable {S : Type*}

def tensorRestrictionBase {N : ℕ} (eig c : Fin N → ℝ) {n : ℕ}
    (x : S → Spin N × LabeledLeaf n) (U : SpecialOrthogonal N) (s : S) : ℝ :=
  orbitHamiltonian eig c (specialToOrthogonal U) (x s).1

def tensorRestrictionOffObservable {N n : ℕ} (i j : Fin N)
    (F : Spin N → Spin N → ℝ) (x : S → Spin N × LabeledLeaf n)
    (U : SpecialOrthogonal N) (p : S × S) : ℝ :=
  offCoordinateProduct i j F (specialToOrthogonal U) ((x p.1).1, (x p.2).1)

def tensorRestrictionOffVariation {N n : ℕ} (i j : Fin N)
    (F : Spin N → Spin N → ℝ) (x : S → Spin N × LabeledLeaf n)
    (U : SpecialOrthogonal N) (p : S × S) : ℝ :=
  offCoordinateVariation i j F (specialToOrthogonal U) ((x p.1).1, (x p.2).1)

def tensorRestrictionMainVariation {N n : ℕ} (eig : Fin N → ℝ) (i j : Fin N)
    (x : S → Spin N × LabeledLeaf n) (U : SpecialOrthogonal N) (p : S × S) : ℝ :=
  (eig i - eig j) * (coordinateProduct i j (specialToOrthogonal U) (x p.1).1 +
    coordinateProduct i j (specialToOrthogonal U) (x p.2).1)

def tensorRestrictionPairPrefix {N m k n d : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (U : SpecialOrthogonal N) (p : S × S) (a : Fin d) : ℝ :=
  tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x p.1) a +
    tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x p.2) a

def tensorRestrictionPairPlanePrefix {N m k n d : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (U : SpecialOrthogonal N) (p : S × S) (a : Fin d) : ℝ :=
  tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree amplitude n v i j (x p.1) a +
    tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree amplitude n v i j (x p.2) a

def tensorRestrictionPairBase {N n : ℕ} (eig c : Fin N → ℝ)
    (x : S → Spin N × LabeledLeaf n) (U : SpecialOrthogonal N) (p : S × S) : ℝ :=
  tensorRestrictionBase eig c x U p.1 + tensorRestrictionBase eig c x U p.2

/-- Exact Haar/Gaussian Ward equation for the actual finite tensor model
on any finite spin/leaf restriction, with a finite Gaussian prefix. -/
theorem tensorRestriction_off_ward_prefix [Fintype S] {N m k n d : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (hij : i ≠ j) (F : Spin N → Spin N → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hF : ∀ σ τ, |F σ τ| ≤ B) :
    let wp := fun p : S × S => w p.1 * w p.2
    let C := tensorRestrictionPairPrefix (d := d + 1) I degree amplitude v x
    let D := tensorRestrictionPairPlanePrefix (d := d + 1) I degree amplitude v x i j
    let H := tensorRestrictionPairBase eig c x
    let O := tensorRestrictionOffObservable i j F x
    (∫ U, (∫ g, finiteGibbsVariation wp (fun p => H U p + linearGaussian (C U) g p)
        (O U) (tensorRestrictionMainVariation eig i j x U) (tensorRestrictionOffVariation i j F x U)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) +
      ∫ g, gaussianWardCorrection wp (fun p => H U p + linearGaussian (C U) g p)
        (O U) (gaussianCross (D U) (C U))
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) ∂μ) = 0 := by
  intro wp C D H O
  let R := specialPlaneRotation i j
  let dH := fun (t : ℝ) (U : SpecialOrthogonal N) => tensorRestrictionMainVariation eig i j x (R t * U)
  let dO := fun (t : ℝ) (U : SpecialOrthogonal N) => tensorRestrictionOffVariation i j F x (R t * U)
  let dC := fun (t : ℝ) (U : SpecialOrthogonal N) => D (R t * U)
  have hR : R 0 = 1 := specialPlaneRotation_zero i j
  have hP (σ : Spin N) : Measurable (fun U : SpecialOrthogonal N =>
      coordinateProduct i j (specialToOrthogonal U) σ) :=
    ((measurable_spinCoordinate σ i).mul (measurable_spinCoordinate σ j)).comp
      measurable_specialToOrthogonal
  have hHm (p : S × S) : Measurable (fun U => H U p) :=
    ((measurable_orbitHamiltonian eig c (x p.1).1).comp measurable_specialToOrthogonal).add
      ((measurable_orbitHamiltonian eig c (x p.2).1).comp measurable_specialToOrthogonal)
  have hOm (p : S × S) : Measurable (fun U => O U p) :=
    (((measurable_spinCoordinate (x p.1).1 i).mul
      (measurable_spinCoordinate (x p.2).1 j)).mul_const _).comp measurable_specialToOrthogonal
  have hCm (p : S × S) (a : Fin (d + 1)) : Measurable (fun U => C U p a) :=
    (measurable_tensorNamespacedCoefficient I degree amplitude n v (x p.1) a).add
      (measurable_tensorNamespacedCoefficient I degree amplitude n v (x p.2) a)
  have hdHm (p : S × S) : Measurable (fun U => dH 0 U p) := by
    simp only [dH, hR, one_mul, tensorRestrictionMainVariation]
    exact ((hP (x p.1).1).add (hP (x p.2).1)).const_mul _
  have hdOm (p : S × S) : Measurable (fun U => dO 0 U p) := by
    simp only [dO, hR, one_mul, tensorRestrictionOffVariation, offCoordinateVariation]
    exact ((((measurable_spinCoordinate (x p.1).1 j).mul (measurable_spinCoordinate (x p.2).1 j)).sub
      ((measurable_spinCoordinate (x p.1).1 i).mul (measurable_spinCoordinate (x p.2).1 i))).mul_const _).comp
        measurable_specialToOrthogonal
  have hdCm (p : S × S) (a : Fin (d + 1)) : Measurable (fun U => dC 0 U p a) := by
    simp only [dC, hR, one_mul, D, tensorRestrictionPairPlanePrefix]
    exact ((measurable_tensorNamespacedPlaneCoefficient I degree amplitude n v i j (x p.1) a).comp
      measurable_specialToOrthogonal).add
        ((measurable_tensorNamespacedPlaneCoefficient I degree amplitude n v i j (x p.2) a).comp
          measurable_specialToOrthogonal)
  have hHd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ p,
      HasDerivAt (fun s => H (R s * U) p) (dH t U p) t := by
    intro U t _ p
    have h1 := (hasDerivAt_planeRotation_energy i j (specialToOrthogonal U) eig (x p.1).1 t).add_const
      (fieldEnergy c (x p.1).1)
    have h2 := (hasDerivAt_planeRotation_energy i j (specialToOrthogonal U) eig (x p.2).1 t).add_const
      (fieldEnergy c (x p.2).1)
    convert h1.fun_add h2 using 1
    · simp only [H, tensorRestrictionPairBase, tensorRestrictionBase, orbitHamiltonian, R,
        map_mul, specialToOrthogonal_planeRotation]
    · simp only [dH, tensorRestrictionMainVariation, R, map_mul, specialToOrthogonal_planeRotation,
        coordinateProduct, spinCoordinate]
      ring
  have hOd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ p,
      HasDerivAt (fun s => O (R s * U) p) (dO t U p) t := by
    intro U t _ p
    simpa only [O, tensorRestrictionOffObservable, dO, tensorRestrictionOffVariation,
      R, map_mul, specialToOrthogonal_planeRotation] using
      hasDerivAt_offCoordinateProduct i j hij F (specialToOrthogonal U) ((x p.1).1, (x p.2).1) t
  have hCd : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ p a,
      HasDerivAt (fun s => C (R s * U) p a) (dC t U p a) t := by
    intro U t _ p a
    have h1 := hasDerivAt_tensorNamespacedCoefficient_plane (specialToOrthogonal U) I degree amplitude n v
      i j (x p.1) a t
    have h2 := hasDerivAt_tensorNamespacedCoefficient_plane (specialToOrthogonal U) I degree amplitude n v
      i j (x p.2) a t
    simpa only [C, D, tensorRestrictionPairPrefix, dC, tensorRestrictionPairPlanePrefix,
      ← matrixRotation_specialToOrthogonal, R, map_mul, specialToOrthogonal_planeRotation] using h1.fun_add h2
  have hOb : ∀ U p, |O U p| ≤ N * B := by
    intro U p
    change |spinCoordinate (specialToOrthogonal U) (x p.1).1 i *
      spinCoordinate (specialToOrthogonal U) (x p.2).1 j * F (x p.1).1 (x p.2).1| ≤ _
    rw [abs_mul]
    exact mul_le_mul (abs_crossCoordinateProduct_le i j _ _ _) (hF _ _)
      (abs_nonneg _) (Nat.cast_nonneg _)
  have hHb : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ p,
      |dH t U p| ≤ |eig i - eig j| * (2 * N) := by
    intro U t _ p
    dsimp only [dH, tensorRestrictionMainVariation]
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have hh := (abs_add_le _ _).trans (add_le_add
      (abs_coordinateProduct_le i j (specialToOrthogonal (R t * U)) (x p.1).1)
      (abs_coordinateProduct_le i j (specialToOrthogonal (R t * U)) (x p.2).1))
    linarith
  have hOdB : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ p, |dO t U p| ≤ 2 * N * B := by
    intro U t _ p
    dsimp only [dO, tensorRestrictionOffVariation, offCoordinateVariation]
    rw [abs_mul]
    apply mul_le_mul _ (hF _ _) (abs_nonneg _) (by positivity)
    have hh := (abs_sub _ _).trans (add_le_add
      (abs_crossCoordinateProduct_le j j (specialToOrthogonal (R t * U)) (x p.1).1 (x p.2).1)
      (abs_crossCoordinateProduct_le i i (specialToOrthogonal (R t * U)) (x p.1).1 (x p.2).1))
    linarith
  have hCdB : ∀ U t, t ∈ Set.Ioo (-1 : ℝ) 1 → ∀ p a,
      |dC t U p a| ≤ 2 * tensorNamespacedDerivativeCap I degree amplitude n v := by
    intro U t _ p a
    dsimp only [dC, D, tensorRestrictionPairPlanePrefix]
    have hh := (abs_add_le _ _).trans (add_le_add
      (tensorNamespacedPlaneCoefficient_abs_le hN (specialToOrthogonal (R t * U)) I degree amplitude n v i j (x p.1) a)
      (tensorNamespacedPlaneCoefficient_abs_le hN (specialToOrthogonal (R t * U)) I degree amplitude n v i j (x p.2) a))
    linarith
  have hwrd := integral_special_gaussian_gibbs_rotation_identity μ R hR (GibbsReference_pair hw)
    H O C hHm hOm hCm dH dO dC hdHm hdOm hdCm hHd hOd hCd
    (N * B) (|eig i - eig j| * (2 * N)) (2 * N * B)
    (fun _ => 2 * tensorNamespacedDerivativeCap I degree amplitude n v) (by positivity)
    hOb hHb hOdB hCdB
  simpa only [dH, dO, dC, hR, one_mul] using hwrd

def tensorRestrictionPairHamiltonian {N m k n : ℕ} (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (U : SpecialOrthogonal N) (g : ℕ → ℝ) (p : S × S) : ℝ :=
  tensorRestrictionPairBase eig c x U p +
    (cylinderField (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x p.1)) g +
      cylinderField (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x p.2)) g)

def tensorRestrictionPairCovarianceDerivative {N m k n : ℕ}
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (U : SpecialOrthogonal N) (p q : S × S) : ℝ :=
  cylinderCross
    (tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree amplitude n v i j (x p.1) +
      tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree amplitude n v i j (x p.2))
    (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x q.1) +
      tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x q.2))

lemma measurable_gaussianWardCorrection [Fintype S] {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O : S → ℝ) (C : S → Fin d → ℝ) (K : S → S → ℝ) :
    Measurable (fun g => gaussianWardCorrection w (fun x => H x + linearGaussian C g x) O K) := by
  unfold gaussianWardCorrection gibbsAverage gibbsPairAverage gibbsTripleAverage
  change Measurable (fun g =>
    (∑ x, gaussianGibbs w H C g x * (O x * K x x)) -
      (∑ x, ∑ y, gaussianGibbs w H C g x * gaussianGibbs w H C g y * (O x * K x y)) -
      (∑ x, ∑ y, gaussianGibbs w H C g x * gaussianGibbs w H C g y * (O x * (K y x + K y y))) +
      2 * ∑ x, ∑ y, ∑ z, gaussianGibbs w H C g x * gaussianGibbs w H C g y * gaussianGibbs w H C g z * (O x * K y z))
  have hp (x : S) := (continuous_gaussianGibbs hw H C x).measurable
  exact (((Finset.measurable_sum _ fun x _ => (hp x).mul_const _).sub
    (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ =>
      ((hp x).mul (hp y)).mul_const _)).sub
    (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ =>
      ((hp x).mul (hp y)).mul_const _)).add
    ((Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ =>
      Finset.measurable_sum _ fun z _ => (((hp x).mul (hp y)).mul (hp z)).mul_const _).const_mul 2)

/-- The actual finite spin/leaf pair Ward equation, using the complete
Gaussian coordinate law. -/
theorem tensorRestriction_off_ward [Fintype S] {N m k n : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {w : S → ℝ} (hw : GibbsReference w) (eig c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amplitude : Fin k → ℝ)
    (v : Fin (n + 1) → SpinTensorIndex I degree → ℝ≥0) (x : S → Spin N × LabeledLeaf n)
    (i j : Fin N) (hij : i ≠ j) (F : Spin N → Spin N → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hF : ∀ σ τ, |F σ τ| ≤ B) :
    let wp := fun p : S × S => w p.1 * w p.2
    let H := tensorRestrictionPairHamiltonian eig c I degree amplitude v x
    let O := tensorRestrictionOffObservable i j F x
    let K := tensorRestrictionPairCovarianceDerivative I degree amplitude v x i j
    (∫ U, (∫ g, finiteGibbsVariation wp (H U g) (O U)
      (tensorRestrictionMainVariation eig i j x U) (tensorRestrictionOffVariation i j F x U)
      ∂gaussianCoordinates) +
      ∫ g, gaussianWardCorrection wp (H U g) (O U) (K U) ∂gaussianCoordinates ∂μ) = 0 := by
  intro wp H O K
  obtain ⟨d, hC, hD⟩ := finite_tensorNamespaced_support_bound I degree amplitude n v i j x
  let Cp := tensorRestrictionPairPrefix (d := d + 1) I degree amplitude v x
  let Dp := tensorRestrictionPairPlanePrefix (d := d + 1) I degree amplitude v x i j
  let Hp := fun U g p => tensorRestrictionPairBase eig c x U p + linearGaussian (Cp U) g p
  have hfield (U : SpecialOrthogonal N) (g : ℕ → ℝ) (p : S × S) :
      H U g p = Hp U (fun a : Fin (d + 1) => g a) p := by
    change tensorRestrictionPairBase eig c x U p +
      (cylinderField (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x p.1)) g +
        cylinderField (tensorNamespacedCoefficients (specialRotation U) I degree amplitude n v (x p.2)) g) = _
    simp only [← matrixRotation_specialToOrthogonal]
    rw [cylinderField_eq_prefix _ (hC (specialToOrthogonal U) p.1),
      cylinderField_eq_prefix _ (hC (specialToOrthogonal U) p.2)]
    simp only [Hp, Cp, tensorRestrictionPairPrefix, linearGaussian, add_mul, Finset.sum_add_distrib]
    rfl
  have hkernel (U : SpecialOrthogonal N) (p q : S × S) :
      K U p q = gaussianCross (Dp U) (Cp U) p q := by
    apply cylinderCross_prefix
    intro a ha
    by_contra hn
    have hz (s : S) : tensorNamespacedPlaneCoefficients (specialToOrthogonal U)
        I degree amplitude n v i j (x s) a = 0 := by
      by_contra hne
      exact hn (hD (specialToOrthogonal U) s a (Finsupp.mem_support_iff.mpr hne))
    exact Finsupp.mem_support_iff.mp ha (by simp only [Finsupp.add_apply, hz, add_zero])
  have hfield_fun (U : SpecialOrthogonal N) (g : ℕ → ℝ) :
      H U g = Hp U (fun a : Fin (d + 1) => g a) := funext (hfield U g)
  have hkernel_fun (U : SpecialOrthogonal N) : K U = gaussianCross (Dp U) (Cp U) :=
    funext fun p => funext fun q => hkernel U p q
  have hmeasH (U : SpecialOrthogonal N) (p : S × S) : Measurable (fun g => Hp U g p) := by
    unfold Hp linearGaussian
    fun_prop
  have hmean (U : SpecialOrthogonal N) :
      (∫ g, finiteGibbsVariation wp (H U g) (O U)
        (tensorRestrictionMainVariation eig i j x U) (tensorRestrictionOffVariation i j F x U)
        ∂gaussianCoordinates) =
      ∫ g, finiteGibbsVariation wp (Hp U g) (O U)
        (tensorRestrictionMainVariation eig i j x U) (tensorRestrictionOffVariation i j F x U)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
    simp_rw [hfield_fun]
    exact (gaussian_prefix_measurePreserving (d + 1)).hasLaw.integral_comp
      (measurable_finiteGibbsVariation wp _ (fun _ => O U)
        (fun _ => tensorRestrictionMainVariation eig i j x U)
        (fun _ => tensorRestrictionOffVariation i j F x U) (hmeasH U)
        (fun _ => measurable_const) (fun _ => measurable_const) (fun _ => measurable_const)).aestronglyMeasurable
  have hmeanK (U : SpecialOrthogonal N) :
      (∫ g, gaussianWardCorrection wp (H U g) (O U) (K U) ∂gaussianCoordinates) =
      ∫ g, gaussianWardCorrection wp (Hp U g) (O U) (gaussianCross (Dp U) (Cp U))
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
    simp_rw [hfield_fun, hkernel_fun]
    exact (gaussian_prefix_measurePreserving (d + 1)).hasLaw.integral_comp
      (measurable_gaussianWardCorrection (GibbsReference_pair hw)
        (tensorRestrictionPairBase eig c x U) (O U) (Cp U)
        (gaussianCross (Dp U) (Cp U))).aestronglyMeasurable
  simp_rw [hmean, hmeanK]
  exact tensorRestriction_off_ward_prefix hN μ hw eig c I degree amplitude v x i j hij F B hB hF

end InvariantIsing

end

end OAI
