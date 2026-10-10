import OAI.Probability.InvariantIsing.Haar.SpecialPlaneRotation
import OAI.Probability.InvariantIsing.Arrays.TensorWardError
import OAI.Probability.InvariantIsing.Arrays.OffDiagonalWard

namespace OAI

/-! Finite-prior Gaussian insertions in the spectral Haar Ward calculation.
The covariance correction is derived by Gaussian integration by parts, with
no assumed Ward identity. Finite spin/leaf restrictions are permitted to
have zero prior weights. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {S : Type*} [Fintype S]

/-- The exact correction obtained from inserting the derivative of a
Gaussian Hamiltonian into a normalized finite Gibbs average. The kernel
need not be symmetric: its first endpoint is the differentiated one. -/
def gaussianWardCorrection (w H O : S → ℝ) (K : S → S → ℝ) : ℝ :=
  gibbsAverage w H (fun x => O x * K x x) -
    gibbsPairAverage w H (fun x y => O x * K x y) -
    gibbsPairAverage w H (fun x y => O x * (K y x + K y y)) +
    2 * gibbsTripleAverage w H (fun x y z => O x * K y z)

/-- Insertion in any specified replica, with an arbitrary bounded finite
replica test. No symmetry or constant-diagonal assumption is used. -/
lemma gaussian_replica_selected_insertion {d r : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H : S → ℝ) (A C : S → Fin (d + 1) → ℝ)
    (l : Fin r) (D : (Fin r → S) → ℝ) :
    (∫ g, ∑ σ : Fin r → S,
      D σ * (linearGaussian A g (σ l) * replicaGibbs w H C g σ)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) =
      ∫ g, ∑ σ : Fin r → S, D σ * (replicaGibbs w H C g σ *
        ∑ k, (gaussianCross A C (σ l) (σ k) -
          ∑ z, gaussianGibbs w H C g z * gaussianCross A C (σ l) z))
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
  rw [integral_finsetSum _ (fun σ _ =>
      (integrable_linear_mul_replica hw H A C (σ l) σ).const_mul (D σ)),
    integral_finsetSum _ (fun σ _ =>
      (integrable_replica_covariance hw H A C (σ l) σ).const_mul (D σ))]
  apply Finset.sum_congr rfl
  intro σ _
  rw [integral_const_mul, integral_const_mul, gaussian_replica_insertion hw]

lemma integrable_gaussian_gibbs_linear_test {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O : S → ℝ) (A C : S → Fin d → ℝ) :
    Integrable (fun g => gibbsAverage w (fun x => H x + linearGaussian C g x)
      (fun x => O x * linearGaussian A g x))
        (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  unfold gibbsAverage
  apply integrable_finsetSum
  intro x _
  convert (integrable_linearGaussian_mul_gibbs hw H A C x x).const_mul (O x) using 1
  funext g
  change _ = O x * (linearGaussian A g x * finiteGibbs w _ x)
  ring

lemma integrable_gaussian_gibbs_linear_product {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O : S → ℝ) (A C : S → Fin d → ℝ) :
    Integrable (fun g => gibbsAverage w (fun x => H x + linearGaussian C g x) O *
      gibbsAverage w (fun x => H x + linearGaussian C g x) (linearGaussian A g))
        (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  have hm : Measurable (fun g => gibbsAverage w (fun x => H x + linearGaussian C g x) O) :=
    measurable_gibbsAverage w _ _ (fun x => by unfold linearGaussian; fun_prop)
      (fun _ => measurable_const)
  apply (integrable_gaussian_gibbs_linear_test hw H (fun _ => 1) A C).mul_bdd
    hm.aestronglyMeasurable (c := ∑ x, |O x|)
    (ae_of_all _ fun g => by
      rw [Real.norm_eq_abs]
      exact abs_gibbsAverage_le hw _ O (fun x =>
        Finset.single_le_sum (fun y _ => abs_nonneg (O y)) (Finset.mem_univ x))) |>.congr
        (ae_of_all _ fun g => by simp only [one_mul]; ring)

lemma integrable_gaussian_gibbs_test {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O : S → ℝ) (C : S → Fin d → ℝ) :
    Integrable (fun g => gibbsAverage w (fun x => H x + linearGaussian C g x) O)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  have hm : Measurable (fun g : Fin d → ℝ =>
      gibbsAverage w (fun x => H x + linearGaussian C g x) O) :=
    measurable_gibbsAverage w _ (fun _ => O)
      (fun x => by unfold linearGaussian; fun_prop) (fun _ => measurable_const)
  apply Integrable.of_bound hm.aestronglyMeasurable (∑ x, |O x|)
  exact ae_of_all _ fun g => by
    rw [Real.norm_eq_abs]
    exact abs_gibbsAverage_le hw _ O (fun x =>
      Finset.single_le_sum (fun y _ => abs_nonneg (O y)) (Finset.mem_univ x))

/-- The Gibbs insertion in the current replica produces the derivative
covariance with one subtraction replica. -/
lemma gaussian_gibbs_test_insertion {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O : S → ℝ) (A C : S → Fin (d + 1) → ℝ) :
    (∫ g, gibbsAverage w (fun x => H x + linearGaussian C g x)
      (fun x => O x * linearGaussian A g x)
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) =
      ∫ g, gibbsAverage w (fun x => H x + linearGaussian C g x)
        (fun x => O x * gaussianCross A C x x) -
        gibbsPairAverage w (fun x => H x + linearGaussian C g x)
          (fun x y => O x * gaussianCross A C x y)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)
  have hi (x : S) : Integrable (fun g => O x * (gaussianGibbs w H C g x *
      (gaussianCross A C x x - ∑ z, gaussianGibbs w H C g z * gaussianCross A C x z))) μ := by
    simpa only [replicaGibbs, Fin.prod_univ_one, Fin.sum_univ_one] using
      (integrable_replica_covariance (r := 1) hw H A C x (fun _ => x)).const_mul (O x)
  have he (g : Fin (d + 1) → ℝ) :
      gibbsAverage w (fun x => H x + linearGaussian C g x)
        (fun x => O x * gaussianCross A C x x) -
        gibbsPairAverage w (fun x => H x + linearGaussian C g x)
          (fun x y => O x * gaussianCross A C x y) =
      ∑ x, O x * (gaussianGibbs w H C g x *
        (gaussianCross A C x x - ∑ z, gaussianGibbs w H C g z * gaussianCross A C x z)) := by
    simp only [gibbsAverage, gibbsPairAverage, gaussianGibbs,
      ← Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro z _
      ring
  have hl (g : Fin (d + 1) → ℝ) :
      gibbsAverage w (fun x => H x + linearGaussian C g x)
        (fun x => O x * linearGaussian A g x) =
      ∑ x, O x * (linearGaussian A g x * gaussianGibbs w H C g x) := by
    unfold gibbsAverage gaussianGibbs
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [he, hl]
  rw [integral_finsetSum _ (fun x _ =>
      (integrable_linearGaussian_mul_gibbs hw H A C x x).const_mul (O x)),
    integral_finsetSum _ (fun x _ => hi x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_const_mul, integral_const_mul, gaussian_gibbs_insertion hw]

lemma gaussian_gibbs_normalization_insertion {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O : S → ℝ) (A C : S → Fin (d + 1) → ℝ) :
    (∫ g, gibbsAverage w (fun x => H x + linearGaussian C g x) O *
      gibbsAverage w (fun x => H x + linearGaussian C g x) (linearGaussian A g)
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) =
      ∫ g, gibbsPairAverage w (fun x => H x + linearGaussian C g x)
          (fun x y => O x * (gaussianCross A C y x + gaussianCross A C y y)) -
        2 * gibbsTripleAverage w (fun x => H x + linearGaussian C g x)
          (fun x y z => O x * gaussianCross A C y z)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)
  have hr (g : Fin (d + 1) → ℝ) (x y : S) :
      replicaGibbs w H C g ![x, y] = gaussianGibbs w H C g x * gaussianGibbs w H C g y := by
    simp only [replicaGibbs, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hi (x y : S) : Integrable (fun g => O x * (linearGaussian A g y *
      (gaussianGibbs w H C g x * gaussianGibbs w H C g y))) μ := by
    simpa only [hr] using (integrable_linear_mul_replica hw H A C y ![x, y]).const_mul (O x)
  have hi' (x y : S) : Integrable (fun g => O x *
      (gaussianGibbs w H C g x * gaussianGibbs w H C g y *
        (gaussianCross A C y x + gaussianCross A C y y -
          2 * ∑ z, gaussianGibbs w H C g z * gaussianCross A C y z))) μ := by
    have hh := (integrable_replica_covariance hw H A C y ![x, y]).const_mul (O x)
    simp only [hr, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hh
    convert hh using 1
    funext g
    ring
  have hl (g : Fin (d + 1) → ℝ) :
      gibbsAverage w (fun x => H x + linearGaussian C g x) O *
        gibbsAverage w (fun x => H x + linearGaussian C g x) (linearGaussian A g) =
      ∑ x, ∑ y, O x * (linearGaussian A g y *
        (gaussianGibbs w H C g x * gaussianGibbs w H C g y)) := by
    simp only [gibbsAverage, Finset.sum_mul_sum, gaussianGibbs]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have he (g : Fin (d + 1) → ℝ) :
      gibbsPairAverage w (fun x => H x + linearGaussian C g x)
          (fun x y => O x * (gaussianCross A C y x + gaussianCross A C y y)) -
        2 * gibbsTripleAverage w (fun x => H x + linearGaussian C g x)
          (fun x y z => O x * gaussianCross A C y z) =
      ∑ x, ∑ y, O x * (gaussianGibbs w H C g x * gaussianGibbs w H C g y *
        (gaussianCross A C y x + gaussianCross A C y y -
          2 * ∑ z, gaussianGibbs w H C g z * gaussianCross A C y z)) := by
    simp only [gibbsPairAverage, gibbsTripleAverage, gaussianGibbs, Finset.mul_sum,
      ← Finset.sum_sub_distrib, mul_sub]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro z _
      ring
  simp_rw [hl, he]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hi x y)),
    integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hi' x y))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_finsetSum _ (fun y _ => hi x y),
    integral_finsetSum _ (fun y _ => hi' x y)]
  apply Finset.sum_congr rfl
  intro y _
  rw [integral_const_mul, integral_const_mul]
  have hh := gaussian_replica_insertion hw H A C y ![x, y]
  simp only [hr, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hh
  convert congrArg (fun a : ℝ => O x * a) hh using 1
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun g => by ring

lemma integrable_gaussian_pair_test {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H : S → ℝ) (O : S → S → ℝ) (C : S → Fin d → ℝ) :
    Integrable (fun g => gibbsPairAverage w (fun x => H x + linearGaussian C g x) O)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  unfold gibbsPairAverage
  apply integrable_finsetSum
  intro x _
  apply integrable_finsetSum
  intro y _
  have hp := (integrable_const (O x y) : Integrable (fun _ : Fin d → ℝ => O x y)
    (Measure.pi (fun _ : Fin d => gaussianReal 0 1))).mul_bdd
    ((continuous_gaussianGibbs hw H C x).mul
      (continuous_gaussianGibbs hw H C y)).aestronglyMeasurable (c := 1)
      (ae_of_all _ fun g => by
        simp only [Pi.mul_apply, gaussianGibbs]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (finiteGibbs_nonneg hw _ x)
          (finiteGibbs_nonneg hw _ y))]
        exact (mul_le_mul_of_nonneg_right (finiteGibbs_le_one hw _ x)
          (finiteGibbs_nonneg hw _ y)).trans
            (by simpa only [one_mul] using finiteGibbs_le_one hw _ y))
  convert hp using 1
  funext g
  change _ = O x y * (finiteGibbs w _ x * finiteGibbs w _ y)
  ring

lemma integrable_gaussian_triple_test {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H : S → ℝ) (O : S → S → S → ℝ) (C : S → Fin d → ℝ) :
    Integrable (fun g => gibbsTripleAverage w (fun x => H x + linearGaussian C g x) O)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  unfold gibbsTripleAverage
  apply integrable_finsetSum
  intro x _
  apply integrable_finsetSum
  intro y _
  apply integrable_finsetSum
  intro z _
  have hp := (integrable_const (O x y z) : Integrable (fun _ : Fin d → ℝ => O x y z)
    (Measure.pi (fun _ : Fin d => gaussianReal 0 1))).mul_bdd
    (((continuous_gaussianGibbs hw H C x).mul (continuous_gaussianGibbs hw H C y)).mul
      (continuous_gaussianGibbs hw H C z)).aestronglyMeasurable (c := 1)
      (ae_of_all _ fun g => by
        simp only [Pi.mul_apply, gaussianGibbs]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
          (mul_nonneg (finiteGibbs_nonneg hw _ x) (finiteGibbs_nonneg hw _ y))
          (finiteGibbs_nonneg hw _ z))]
        have hxy : finiteGibbs w (fun a => H a + linearGaussian C g a) x *
            finiteGibbs w (fun a => H a + linearGaussian C g a) y ≤ 1 :=
          (mul_le_mul_of_nonneg_right (finiteGibbs_le_one hw _ x)
          (finiteGibbs_nonneg hw _ y)).trans
            (by simpa only [one_mul] using finiteGibbs_le_one hw _ y)
        exact (mul_le_mul_of_nonneg_right hxy (finiteGibbs_nonneg hw _ z)).trans
          (by simpa only [one_mul] using finiteGibbs_le_one hw _ z))
  convert hp using 1
  funext g
  change _ = O x y z * (finiteGibbs w _ x * finiteGibbs w _ y * finiteGibbs w _ z)
  ring

/-- Exact Gaussian covariance-derivative correction for a finite prior.
The first coefficient map is the Hamiltonian derivative and the second
is the Gaussian coefficient in the Gibbs exponent. -/
theorem gaussian_gibbs_covariance_insertion {d : ℕ} {w : S → ℝ}
    (hw : GibbsReference w) (H O : S → ℝ) (A C : S → Fin (d + 1) → ℝ) :
    (∫ g, gibbsAverage w (fun x => H x + linearGaussian C g x)
        (fun x => O x * linearGaussian A g x) -
      gibbsAverage w (fun x => H x + linearGaussian C g x) O *
        gibbsAverage w (fun x => H x + linearGaussian C g x) (linearGaussian A g)
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) =
      ∫ g, gaussianWardCorrection w (fun x => H x + linearGaussian C g x) O
        (gaussianCross A C)
        ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
  rw [integral_sub (integrable_gaussian_gibbs_linear_test hw H O A C)
    (integrable_gaussian_gibbs_linear_product hw H O A C),
    gaussian_gibbs_test_insertion hw H O A C, gaussian_gibbs_normalization_insertion hw H O A C]
  have hsub := integral_sub
    ((integrable_gaussian_gibbs_test hw H (fun x => O x * gaussianCross A C x x) C).sub
      (integrable_gaussian_pair_test hw H (fun x y => O x * gaussianCross A C x y) C))
    ((integrable_gaussian_pair_test hw H (fun x y => O x *
      (gaussianCross A C y x + gaussianCross A C y y)) C).sub
      ((integrable_gaussian_triple_test hw H (fun x y z => O x * gaussianCross A C y z) C).const_mul 2))
  simp only [Pi.sub_apply] at hsub
  rw [← hsub]
  apply integral_congr_ae
  exact ae_of_all _ fun g => by unfold gaussianWardCorrection; ring

end InvariantIsing

end

end OAI
