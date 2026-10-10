import Mathlib
import OAI.Computability.MinUncut.Estimates.F2

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory

variable {m n : ℕ}

lemma gauss_neg_preserving (ι : Type*) [Fintype ι] :
    MeasurePreserving (fun g : ι → ℝ => -g) (gauss ι) (gauss ι) := by
  apply measurePreserving_pi (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 1)
    (f := fun _ (x : ℝ) => -x)
  intro i
  exact ⟨by fun_prop, by simpa using (gaussianReal_map_neg (μ := 0) (v := 1))⟩

lemma gauss_integral_neg (ι : Type*) [Fintype ι] (f : (ι → ℝ) → ℝ) :
    (∫ g, f (-g) ∂gauss ι) = ∫ g, f g ∂gauss ι := by
  exact (gauss_neg_preserving ι).integral_comp (Homeomorph.neg _).measurableEmbedding f

lemma query_neg (u : Point m n → ℝ) (d : Code m n → ℝ) (z : Code m n)
    (h : (Real.sqrt (n^m : ℕ))⁻¹ *
      (∑ x : Point m n, u x * BinaryFourier.sign (z.val x)) + d z ≠ 0) :
    query (-u) (-d) z = !(query u d z) := by
  simp only [query, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · intro ht hpos
    apply h
    linarith
  · intro ht
    linarith

lemma query_no_ties (u : Point m n → ℝ) {η : ℝ} (hη : η ≠ 0) :
    ∀ᵐ l ∂gauss (Code m n), ∀ z : Code m n,
      (Real.sqrt (n^m : ℕ))⁻¹ *
        (∑ x : Point m n, u x * BinaryFourier.sign (z.val x)) + (η • l) z ≠ 0 := by
  rw [ae_all_iff]
  intro z
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  let t := (Real.sqrt (n^m : ℕ))⁻¹ *
    (∑ x : Point m n, u x * BinaryFourier.sign (z.val x))
  have he := (measurePreserving_eval (fun _ : Code m n => gaussianReal 0 1) z).quasiMeasurePreserving.ae
    (Measure.ae_ne (gaussianReal 0 1) (-t / η))
  filter_upwards [he] with l hl
  change t + η * l z ≠ 0
  intro hh
  apply hl
  change l z = -t / η
  apply (eq_div_iff hη).mpr
  linarith

variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]

lemma tableSmooth_odd (f : FoldedProof A) (B : FaceArray A m n)
    {η : ℝ} (hη : η ≠ 0) (u : Point m n → ℝ) :
    tableSmooth f B η (-u) = -tableSmooth f B η u := by
  unfold tableSmooth
  rw [← gauss_integral_neg (Code m n) (fun l => bitSign (f.answer (pullQuery B (-u) (η • l))))]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [query_no_ties u hη] with l hl
  have hP : pullQuery B (-u) (η • (-l)) = fun a => !(pullQuery B u (η • l) a) := by
    funext a
    simp only [pullQuery, smul_neg]
    exact query_neg u (η • l) (labelCode B a) (hl _)
  rw [hP, f.folded, bitSign_not]

lemma smooth_odd (f : FoldedProof A) (B : FaceArray A m n)
    (σ : ℝ) {η : ℝ} (hη : η ≠ 0) (c : Point m n → ℝ) :
    smooth f B σ η (-c) = -smooth f B σ η c := by
  change (∫ g, tableSmooth f B η (-c + σ • g) ∂gauss (Point m n)) =
    -(∫ g, tableSmooth f B η (c + σ • g) ∂gauss (Point m n))
  rw [← gauss_integral_neg (Point m n) (fun g => tableSmooth f B η (-c + σ • g))]
  simp only [smul_neg, ← neg_add, tableSmooth_odd f B hη, integral_neg]

lemma smooth_mean_zero (f : FoldedProof A) (B : FaceArray A m n)
    (σ : ℝ) {η : ℝ} (hη : η ≠ 0) :
    (∫ c : Point m n → ℝ, smooth f B σ η c ∂gauss (Point m n)) = 0 := by
  have h := gauss_integral_neg (Point m n) (smooth f B σ η)
  simp_rw [smooth_odd f B σ hη, integral_neg] at h
  linarith

end MinUncut.Inner

open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology

end

end OAI
