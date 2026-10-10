import OAI.Probability.InvariantIsing.Arrays.TensorTruncatedWard

namespace OAI

/-! Uniform bounds on the complete finite Gaussian Ward correction after
spectral coordinate contraction. Constants do not depend on the leaf cutoff. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S ι : Type*} [Fintype S]

lemma gibbsPairAverage_const_mul (w H : S → ℝ) (O : S → S → ℝ) (a : ℝ) :
    gibbsPairAverage w H (fun x y => a * O x y) = a * gibbsPairAverage w H O := by
  simp only [gibbsPairAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma gibbsTripleAverage_const_mul (w H : S → ℝ) (O : S → S → S → ℝ) (a : ℝ) :
    gibbsTripleAverage w H (fun x y z => a * O x y z) = a * gibbsTripleAverage w H O := by
  simp only [gibbsTripleAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma abs_gibbsPairAverage_le {w : S → ℝ} (hw : GibbsReference w)
    (H : S → ℝ) (O : S → S → ℝ) {B : ℝ} (hO : ∀ x y, |O x y| ≤ B) :
    |gibbsPairAverage w H O| ≤ B := by
  have he : gibbsPairAverage w H O = gibbsAverage w H (fun x => gibbsAverage w H (O x)) := by
    simp only [gibbsPairAverage, gibbsAverage, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [he]
  exact abs_gibbsAverage_le hw H _ (fun x => abs_gibbsAverage_le hw H (O x) (hO x))

lemma abs_gibbsTripleAverage_le {w : S → ℝ} (hw : GibbsReference w)
    (H : S → ℝ) (O : S → S → S → ℝ) {B : ℝ} (hO : ∀ x y z, |O x y z| ≤ B) :
    |gibbsTripleAverage w H O| ≤ B := by
  have he : gibbsTripleAverage w H O = gibbsAverage w H (fun x => gibbsPairAverage w H (O x)) := by
    simp only [gibbsTripleAverage, gibbsAverage, gibbsPairAverage, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [he]
  exact abs_gibbsAverage_le hw H _ (fun x => abs_gibbsPairAverage_le hw H (O x) (hO x))

/-- The Gaussian correction written in terms of a contracted observable
and kernel. Its three arguments retain the observable and both endpoints. -/
def gibbsKernelCorrection (w H : S → ℝ) (C : S → S → S → ℝ) : ℝ :=
  gibbsAverage w H (fun s => C s s s) - gibbsPairAverage w H (fun s x => C s s x) -
    gibbsPairAverage w H (fun s x => C s x s + C s x x) +
    2 * gibbsTripleAverage w H C

lemma gibbsKernelCorrection_product (w H O : S → ℝ) (K : S → S → ℝ) :
    gibbsKernelCorrection w H (fun s x y => O s * K x y) = gaussianWardCorrection w H O K := by
  simp only [gibbsKernelCorrection, gaussianWardCorrection, mul_add]

lemma gibbsKernelCorrection_finset_sum (w H : S → ℝ) (t : Finset ι) (a : ℝ)
    (C : ι → S → S → S → ℝ) :
    gibbsKernelCorrection w H (fun s x y => ∑ i ∈ t, a * C i s x y) =
      ∑ i ∈ t, a * gibbsKernelCorrection w H (C i) := by
  unfold gibbsKernelCorrection
  have he (s x : S) : (∑ i ∈ t, a * C i s x s) + (∑ i ∈ t, a * C i s x x) =
      ∑ i ∈ t, a * (C i s x s + C i s x x) := by
    simp only [mul_add, Finset.sum_add_distrib]
  simp_rw [he, gibbsAverage_finset_sum, gibbsPairAverage_finset_sum, gibbsTripleAverage_finset_sum,
    gibbsAverage_const_mul, gibbsPairAverage_const_mul, gibbsTripleAverage_const_mul]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_sub, mul_add]
  simp only [mul_left_comm 2 a]

/-- Six times the contraction bound controls the entire Gaussian ratio
correction, including both normalization insertions. -/
lemma gibbsKernelCorrection_abs_le {w : S → ℝ} (hw : GibbsReference w)
    (H : S → ℝ) (C : S → S → S → ℝ) {B : ℝ}
    (hC : ∀ s x y, |C s x y| ≤ B) :
    |gibbsKernelCorrection w H C| ≤ 6 * B := by
  have h1 := abs_gibbsAverage_le hw H (fun s => C s s s) (fun s => hC s s s)
  have h2 := abs_gibbsPairAverage_le hw H (fun s x => C s s x) (fun s x => hC s s x)
  have h3 := abs_gibbsPairAverage_le hw H (fun s x => C s x s + C s x x)
    (fun s x => (abs_add_le _ _).trans (add_le_add (hC s x s) (hC s x x)))
  have h4 := abs_gibbsTripleAverage_le hw H C hC
  unfold gibbsKernelCorrection
  calc
    _ ≤ |gibbsAverage w H (fun s => C s s s)| + |gibbsPairAverage w H (fun s x => C s s x)| +
        |gibbsPairAverage w H (fun s x => C s x s + C s x x)| +
        |2 * gibbsTripleAverage w H C| :=
      (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
        (add_le_add ((abs_sub _ _).trans (add_le_add le_rfl le_rfl)) le_rfl)) le_rfl)
    _ ≤ 6 * B := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; linarith

omit [Fintype S] in
lemma cylinderCross_add_right (a b c : ℕ →₀ ℝ) :
    cylinderCross a (b + c) = cylinderCross a b + cylinderCross a c := by
  simp only [cylinderCross, Finsupp.sum, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

omit [Fintype S] in
def tensorRestrictionWardContraction {N m n : ℕ} (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (J K : Finset (Fin N)) (F : Spin N → Spin N → ℝ)
    (x : S → Spin N × LabeledLeaf n) (s p q : S × S) : ℝ :=
  F (x s.1).1 (x s.2).1 *
    (tensorWardPerturbationError U I degree treeDegree n u J K (x s.1).1 (x s.2).1 (x p.1) (x q.1) +
      tensorWardPerturbationError U I degree treeDegree n u J K (x s.1).1 (x s.2).1 (x p.1) (x q.2) +
      tensorWardPerturbationError U I degree treeDegree n u J K (x s.1).1 (x s.2).1 (x p.2) (x q.1) +
      tensorWardPerturbationError U I degree treeDegree n u J K (x s.1).1 (x s.2).1 (x p.2) (x q.2))

omit [Fintype S] in
lemma tensorRestrictionWardContraction_abs_le {N m n : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (J K : Finset (Fin N)) (F : Spin N → Spin N → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ σ τ, |F σ τ| ≤ B) (x : S → Spin N × LabeledLeaf n) (s p q : S × S) :
    |tensorRestrictionWardContraction U I degree treeDegree u J K F x s p q| ≤
      32 * B * D * perturbationScale N ^ 2 := by
  let E := fun a b : S => tensorWardPerturbationError U I degree treeDegree n u J K
    (x s.1).1 (x s.2).1 (x a) (x b)
  have he (a b : S) : |E a b| ≤ 8 * D * perturbationScale N ^ 2 :=
    tensorWardPerturbationError_abs_le hN U I degree treeDegree n u hu D hD hdegree
      J K (x s.1).1 (x s.2).1 (x a) (x b)
  change |F (x s.1).1 (x s.2).1 * (E p.1 q.1 + E p.1 q.2 + E p.2 q.1 + E p.2 q.2)| ≤ _
  rw [abs_mul]
  have hh : |E p.1 q.1 + E p.1 q.2 + E p.2 q.1 + E p.2 q.2| ≤
      32 * D * perturbationScale N ^ 2 := by
    have h11 := he p.1 q.1
    have h12 := he p.1 q.2
    have h21 := he p.2 q.1
    have h22 := he p.2 q.2
    have h1 := abs_add_le (E p.1 q.1) (E p.1 q.2)
    have h2 := abs_add_le (E p.1 q.1 + E p.1 q.2) (E p.2 q.1)
    have h3 := abs_add_le (E p.1 q.1 + E p.1 q.2 + E p.2 q.1) (E p.2 q.2)
    linarith
  calc
    _ ≤ B * (32 * D * perturbationScale N ^ 2) :=
      mul_le_mul (hF _ _) hh (abs_nonneg _) hB
    _ = _ := by ring

/-- The complete finite Gaussian Ward correction is uniformly quadratic
in the perturbation scale, independent of the leaf cutoff and all Gaussian
marks. The coefficient 192 is inessential for passage to the limit. -/
theorem tensorRestrictionWardCorrection_abs_le {N m n : ℕ}
    (hN : 0 < N) (U : Orthogonal N) {w : S → ℝ} (hw : GibbsReference w)
    (H : S × S → ℝ) (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ)
    (treeDegree : Fin N → ℕ) (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2)
    (D : ℝ) (hD : 0 ≤ D) (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (J K : Finset (Fin N)) (F : Spin N → Spin N → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ σ τ, |F σ τ| ≤ B) (x : S → Spin N × LabeledLeaf n) :
    |gibbsKernelCorrection (fun s : S × S => w s.1 * w s.2) H
      (tensorRestrictionWardContraction U I degree treeDegree u J K F x)| ≤
        192 * B * D * perturbationScale N ^ 2 := by
  have hh := gibbsKernelCorrection_abs_le (GibbsReference_pair hw) H
    (tensorRestrictionWardContraction U I degree treeDegree u J K F x)
    (tensorRestrictionWardContraction_abs_le hN U I degree treeDegree u hu D hD hdegree J K F B hB hF x)
  exact hh.trans_eq (by ring)

omit [Fintype S] in
lemma tensorRestrictionWardContraction_eq {N m n : ℕ} (U : SpecialOrthogonal N)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (F : Spin N → Spin N → ℝ)
    (x : S → Spin N × LabeledLeaf n) (s p q : S × S) :
    tensorRestrictionWardContraction (specialToOrthogonal U) I degree treeDegree u J K F x s p q =
      (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
        tensorRestrictionOffObservable i j F x U s *
          tensorRestrictionPairCovarianceDerivative I degree (tensorPerturbationAmplitude N u)
            (fun a => tensorPathProfile I degree n treeDegree h a) x i j U p q := by
  let η := (x s.1).1
  let θ := (x s.2).1
  let C := fun (i j : Fin N) (a b : S) => cylinderCross
    (tensorNamespacedPlaneCoefficients (specialToOrthogonal U) I degree (tensorPerturbationAmplitude N u) n
      (fun a => tensorPathProfile I degree n treeDegree h a) i j (x a))
    (tensorNamespacedCoefficients (specialRotation U) I degree (tensorPerturbationAmplitude N u) n
      (fun a => tensorPathProfile I degree n treeDegree h a) (x b))
  have hc (a b : S) :
      (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
        spinCoordinate (specialToOrthogonal U) η i * spinCoordinate (specialToOrthogonal U) θ j * C i j a b =
        tensorWardPerturbationError (specialToOrthogonal U) I degree treeDegree n u J K η θ (x a) (x b) :=
    tensorNamespacedPlane_contraction_eq (specialToOrthogonal U) I degree treeDegree n u h hh h0 J K η θ (x a) (x b)
  have hk (i j : Fin N) : tensorRestrictionPairCovarianceDerivative I degree (tensorPerturbationAmplitude N u)
      (fun a => tensorPathProfile I degree n treeDegree h a) x i j U p q =
      C i j p.1 q.1 + C i j p.1 q.2 + C i j p.2 q.1 + C i j p.2 q.2 := by
    simp only [tensorRestrictionPairCovarianceDerivative, cylinderCross_add_left, cylinderCross_add_right, C]
    ring
  simp_rw [hk]
  have ht (i j : Fin N) : tensorRestrictionOffObservable i j F x U s *
      (C i j p.1 q.1 + C i j p.1 q.2 + C i j p.2 q.1 + C i j p.2 q.2) =
      F η θ * (spinCoordinate (specialToOrthogonal U) η i * spinCoordinate (specialToOrthogonal U) θ j * C i j p.1 q.1 +
        spinCoordinate (specialToOrthogonal U) η i * spinCoordinate (specialToOrthogonal U) θ j * C i j p.1 q.2 +
        spinCoordinate (specialToOrthogonal U) η i * spinCoordinate (specialToOrthogonal U) θ j * C i j p.2 q.1 +
        spinCoordinate (specialToOrthogonal U) η i * spinCoordinate (specialToOrthogonal U) θ j * C i j p.2 q.2) := by
    unfold tensorRestrictionOffObservable offCoordinateProduct
    ring
  simp_rw [ht]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib]
  rw [show (N : ℝ)⁻¹ ^ 2 * (F η θ *
      ((∑ i ∈ J, ∑ j ∈ K, spinCoordinate (specialToOrthogonal U) η i * spinCoordinate (specialToOrthogonal U) θ j * C i j p.1 q.1) +
        (∑ i ∈ J, ∑ j ∈ K, spinCoordinate (specialToOrthogonal U) η i * spinCoordinate (specialToOrthogonal U) θ j * C i j p.1 q.2) +
        (∑ i ∈ J, ∑ j ∈ K, spinCoordinate (specialToOrthogonal U) η i * spinCoordinate (specialToOrthogonal U) θ j * C i j p.2 q.1) +
        (∑ i ∈ J, ∑ j ∈ K, spinCoordinate (specialToOrthogonal U) η i * spinCoordinate (specialToOrthogonal U) θ j * C i j p.2 q.2))) =
      F η θ * (((N : ℝ)⁻¹ ^ 2 * (∑ i ∈ J, ∑ j ∈ K, spinCoordinate (specialToOrthogonal U) η i * spinCoordinate (specialToOrthogonal U) θ j * C i j p.1 q.1)) +
        ((N : ℝ)⁻¹ ^ 2 * (∑ i ∈ J, ∑ j ∈ K, spinCoordinate (specialToOrthogonal U) η i * spinCoordinate (specialToOrthogonal U) θ j * C i j p.1 q.2)) +
        ((N : ℝ)⁻¹ ^ 2 * (∑ i ∈ J, ∑ j ∈ K, spinCoordinate (specialToOrthogonal U) η i * spinCoordinate (specialToOrthogonal U) θ j * C i j p.2 q.1)) +
        ((N : ℝ)⁻¹ ^ 2 * (∑ i ∈ J, ∑ j ∈ K, spinCoordinate (specialToOrthogonal U) η i * spinCoordinate (specialToOrthogonal U) θ j * C i j p.2 q.2))) by ring]
  simp only [hc]
  rfl

lemma tensorRestrictionWardCorrection_eq {N m n : ℕ} (U : SpecialOrthogonal N)
    (w : S → ℝ) (H : S × S → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (F : Spin N → Spin N → ℝ) (x : S → Spin N × LabeledLeaf n) :
    gibbsKernelCorrection (fun p : S × S => w p.1 * w p.2) H
      (tensorRestrictionWardContraction (specialToOrthogonal U) I degree treeDegree u J K F x) =
      (N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
        gaussianWardCorrection (fun p : S × S => w p.1 * w p.2) H
          (tensorRestrictionOffObservable i j F x U)
          (tensorRestrictionPairCovarianceDerivative I degree (tensorPerturbationAmplitude N u)
            (fun a => tensorPathProfile I degree n treeDegree h a) x i j U) := by
  have he : tensorRestrictionWardContraction (specialToOrthogonal U) I degree treeDegree u J K F x =
      fun s p q => ∑ a ∈ J ×ˢ K, (N : ℝ)⁻¹ ^ 2 *
        (tensorRestrictionOffObservable a.1 a.2 F x U s *
          tensorRestrictionPairCovarianceDerivative I degree (tensorPerturbationAmplitude N u)
            (fun a => tensorPathProfile I degree n treeDegree h a) x a.1 a.2 U p q) := by
    funext s p q
    rw [tensorRestrictionWardContraction_eq U I degree treeDegree u h hh h0 J K F x s p q]
    simp only [Finset.sum_product, ← Finset.mul_sum]
  rw [he, gibbsKernelCorrection_finset_sum]
  simp only [gibbsKernelCorrection_product, Finset.sum_product, Finset.mul_sum]

/-- The normalized Gaussian error in the actual finite-prior Ward equation
has a uniform bound tending to zero with the perturbation scale. -/
theorem tensorRestriction_actualWardCorrection_abs_le {N m n : ℕ} (hN : 0 < N)
    (U : SpecialOrthogonal N) {w : S → ℝ} (hw : GibbsReference w) (H : S × S → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin N → Fin m → ℕ) (treeDegree : Fin N → ℕ)
    (u : Fin N → ℝ) (hu : ∀ r, |u r| ≤ 2) (D : ℝ) (hD : 0 ≤ D)
    (hdegree : ∀ r, (∑ a, (degree r a : ℝ)) ≤ D * ((r : ℝ) + 1))
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0)
    (J K : Finset (Fin N)) (F : Spin N → Spin N → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ σ τ, |F σ τ| ≤ B) (x : S → Spin N × LabeledLeaf n) :
    |(N : ℝ)⁻¹ ^ 2 * ∑ i ∈ J, ∑ j ∈ K,
      gaussianWardCorrection (fun p : S × S => w p.1 * w p.2) H
        (tensorRestrictionOffObservable i j F x U)
        (tensorRestrictionPairCovarianceDerivative I degree (tensorPerturbationAmplitude N u)
          (fun a => tensorPathProfile I degree n treeDegree h a) x i j U)| ≤
      192 * B * D * perturbationScale N ^ 2 := by
  rw [← tensorRestrictionWardCorrection_eq U w H I degree treeDegree u h hh h0 J K F x]
  exact tensorRestrictionWardCorrection_abs_le hN (specialToOrthogonal U) hw H I degree treeDegree u hu D hD hdegree
    J K F B hB hF x

end InvariantIsing

end

end OAI
