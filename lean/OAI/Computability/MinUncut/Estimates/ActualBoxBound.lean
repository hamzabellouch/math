import Mathlib
import OAI.Computability.MinUncut.Analysis.SmoothingRho
import OAI.Computability.MinUncut.Estimates.ExpectResampleRow

namespace OAI

variable {m n : ℕ}
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianHermite Subbox MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] pointEmbed coordinateEnum gaussianSlice Slice.centeredClip zeroProcessedOnBox faceCorrelation
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

theorem actual_zero_box_bound (f : FoldedProof A) (σ η : ℝ) (hm : 0 < m) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) {A₀ : ℝ} (hA : 0≤A₀)
    (B : FaceArray A m n) :
    (∫ c, faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c) ∂γpi (Point m n)) ≤
      2*A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) := by
  have hx : 0≤∫ c, faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c) ∂γpi (Point m n) :=
    integral_nonneg (fun c => faceCorrelation_nonneg _)
  have hd : 0≤(m:ℝ)/(k+1) := by positivity
  have hq : (2^m:ℕ)≠0 := by positivity
  apply (pow_le_pow_iff_left₀ hx (by positivity) hq).mp
  rw [mul_pow,Real.rpow_inv_natCast_pow hd hq]
  exact actual_zero_box_power f σ η hm Y J hA B

theorem actual_zero_box_average (f : FoldedProof A) (σ η : ℝ) (hm : 0 < m) {k : ℕ}
    (Y : UnpointedBox (Fin m) (Fin n) k)
    (J : Finset (Finset (Row m n) × (Point m n → ℕ))) {A₀ : ℝ} (hA : 0≤A₀) :
    (∫ c, (𝔼 B : FaceArray A m n,
      faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c)) ∂γpi (Point m n)) ≤
      2*A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) := by
  have hb (B : FaceArray A m n) (c : Point m n → ℝ) :
      |faceCorrelation (zeroProcessedOnBox f σ η Y J A₀ B c)|≤2*A₀ := by
    rw [abs_of_nonneg (faceCorrelation_nonneg _)]
    exact (faceCorrelation_le_l1 _).trans ((Finset.expect_le_expect (fun u _ =>
      zeroProcessedOnBox_abs_le f σ η Y J hA B c u)).trans_eq (Fintype.expect_const _))
  rw [Box.integral_expect _ (fun B => Box.bounded_integrable
    (faceCorrelation_measurable_field _ (zeroProcessedOnBox_measurable f σ η Y J A₀ B)).aestronglyMeasurable (hb B))]
  exact (Finset.expect_le_expect (fun B _ => actual_zero_box_bound f σ η hm Y J hA B)).trans_eq
    (Fintype.expect_const _)
end MinUncut.Inner

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

def firstFailure (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c g : Point m n → ℝ) (l : Code m n → ℝ) : ℝ :=
  if f.answer (pullQuery B c 0) = f.answer (pullQuery B (c+σ•g) (η•l)) then 0 else 1

def firstRejection (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : ℝ :=
  ∫ g, ∫ l, firstFailure f B σ η c g l ∂gauss (Code m n) ∂gauss (Point m n)

omit [Fintype A] in
lemma firstFailure_eq (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c g : Point m n → ℝ) (l : Code m n → ℝ) :
    firstFailure f B σ η c g l =
      (1-bitSign (f.answer (pullQuery B c 0))*bitSign (f.answer (pullQuery B (c+σ•g) (η•l))))/2 := by
  unfold firstFailure
  cases f.answer (pullQuery B c 0) <;> cases f.answer (pullQuery B (c+σ•g) (η•l)) <;> norm_num [bitSign]

lemma measurable_smooth (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) :
    Measurable (smooth f B σ η) := by
  have hh : Measurable (fun p : (Point m n → ℝ) × (Point m n → ℝ) =>
      tableSmooth f B η (p.1+σ•p.2)) := (measurable_tableSmooth f B η).comp (by fun_prop)
  exact hh.stronglyMeasurable.integral_prod_right.measurable

omit [Fintype A] in
lemma smooth_abs_le (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : |smooth f B σ η c|≤1 := by
  change |∫ g, tableSmooth f B η (c+σ•g) ∂gauss (Point m n)|≤1
  simpa only [Real.norm_eq_abs,MeasureTheory.probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := gauss (Point m n)) (f := fun g => tableSmooth f B η (c+σ•g)) (C := 1)
      (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using tableSmooth_abs_le f B η (c+σ•g)))

lemma firstRejection_eq (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) :
    firstRejection f B σ η c = (1-bitSign (f.answer (pullQuery B c 0))*smooth f B σ η c)/2 := by
  have hi (g : Point m n → ℝ) : Integrable
      (fun l => bitSign (f.answer (pullQuery B (c+σ•g) (η•l)))) (gauss (Code m n)) :=
    Box.bounded_integrable ((measurable_answer f B η).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (fun l => (bitSign_abs _).le)
  have ht : Integrable (fun g => tableSmooth f B η (c+σ•g)) (gauss (Point m n)) :=
    Box.bounded_integrable ((measurable_tableSmooth f B η).comp (by fun_prop)).aestronglyMeasurable
      (fun g => tableSmooth_abs_le f B η _)
  unfold firstRejection
  simp_rw [firstFailure_eq, integral_div]
  simp_rw [integral_sub (integrable_const 1) ((hi _).const_mul _), integral_const_mul]
  simp only [integral_const,MeasureTheory.probReal_univ,one_smul]
  change (∫ g, (1-bitSign (f.answer (pullQuery B c 0))*tableSmooth f B η (c+σ•g)) ∂gauss (Point m n))/2=_
  rw [integral_sub (integrable_const 1) (ht.const_mul _),integral_const_mul]
  simp only [integral_const,MeasureTheory.probReal_univ,one_smul]
  rfl

lemma measurable_firstRejection (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ) :
    Measurable (firstRejection f B σ η) := by
  simp_rw [show firstRejection f B σ η = fun c =>
    (1-bitSign (f.answer (pullQuery B c 0))*smooth f B σ η c)/2 by
    funext c; exact firstRejection_eq f B σ η c]
  have h0 : Measurable (fun c : Point m n → ℝ => bitSign (f.answer (pullQuery B c 0))) :=
    (measurable_of_finite bitSign).comp ((measurable_of_finite f.answer).comp
      ((measurable_pullQuery B).comp (measurable_id.prodMk measurable_const)))
  exact (measurable_const.sub (h0.mul (measurable_smooth f B σ η))).div_const _

lemma firstRejection_range (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : 0≤firstRejection f B σ η c ∧ firstRejection f B σ η c≤1 := by
  rw [firstRejection_eq]
  have hb := abs_le.mp (smooth_abs_le f B σ η c)
  cases f.answer (pullQuery B c 0) <;> norm_num [bitSign] <;> constructor <;> linarith

lemma smooth_energy_first (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) :
    1-4*firstRejection f B σ η c≤(smooth f B σ η c)^2 := by
  rw [firstRejection_eq]
  cases f.answer (pullQuery B c 0) <;> simp only [bitSign,Bool.false_eq_true,↓reduceIte] <;>
    nlinarith [sq_nonneg (smooth f B σ η c-1),sq_nonneg (smooth f B σ η c+1)]

theorem gradient_energy_first (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0 < n) {σ η : ℝ} (hσ : σ≠0) (hη : η≠0) :
    1-4*(∫ c, firstRejection f B σ η c ∂gauss (Point m n)) ≤
      ∫ c, spatialEnergy (gradient f B σ η c) ∂gauss (Point m n) := by
  have hr : Integrable (firstRejection f B σ η) (gauss (Point m n)) :=
    Box.bounded_integrable (measurable_firstRejection f B σ η).aestronglyMeasurable (fun c => by
      rw [abs_of_nonneg (firstRejection_range f B σ η c).1]
      exact (firstRejection_range f B σ η c).2)
  have hs : MemLp (smooth f B σ η) 2 (gauss (Point m n)) :=
    MemLp.of_bound (measurable_smooth f B σ η).aestronglyMeasurable 1
      (ae_of_all _ (fun c => by simpa only [Real.norm_eq_abs] using smooth_abs_le f B σ η c))
  apply le_trans _ (smooth_energy_le_gradient f B hn hσ hη)
  calc
    _ = ∫ c, 1-4*firstRejection f B σ η c ∂gauss (Point m n) := by
      rw [integral_sub (integrable_const 1) (hr.const_mul 4),integral_const_mul]
      simp
    _ ≤ _ := integral_mono ((integrable_const 1).sub (hr.const_mul 4)) hs.integrable_sq
      (smooth_energy_first f B σ η)
end MinUncut.Inner

end

end OAI
