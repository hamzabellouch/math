import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.MatrixKernel

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace ContDiff
open scoped Manifold
open MeasureTheory Set Metric
open scoped ENNReal Pointwise Matrix
section SignedExtension
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ν ι : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ν
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Nonempty ν] in
lemma matrix_images_orthogonal {P N : Matrix ν ν ℝ} (hP : 0 ≤ P) (hPN : P * N = 0)
    (x y : E) : ⟪op P x, op N y⟫ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint]
  have hs : star (op P) = op P := by rw [← map_star, hP.star_eq]
  rw [hs]
  change ⟪x, (op P * op N) y⟫ = 0
  rw [← map_mul, hPN, map_zero]
  simp

lemma Admissible.positiveExtension_orthogonal {f : E → ι → ℝ} (hf : Admissible f)
    {P N : Matrix ν ν ℝ} (hP : 0 ≤ P) (hN : 0 ≤ N) (hPN : P * N = 0) (i : ι) :
    positiveExtension f P i * positiveExtension f N i = 0 := by
  apply mul_eq_zero.mpr
  by_contra hn
  push Not at hn
  have hp := lt_of_le_of_ne (hf.positiveExtension_nonneg P i) (Ne.symm hn.1)
  have hn' := lt_of_le_of_ne (hf.positiveExtension_nonneg N i) (Ne.symm hn.2)
  obtain ⟨v, ⟨x, rfl⟩, hv, hx⟩ := (hf.positiveExtension_support hP i).mp hp
  obtain ⟨w, ⟨y, rfl⟩, hw, hy⟩ := (hf.positiveExtension_support hN i).mp hn'
  exact hf.orthogonal _ _ hv hw (matrix_images_orthogonal hP hPN x y) i ⟨hx, hy⟩

noncomputable def signedExtension (f : E → ι → ℝ) (A : Matrix ν ν ℝ) : ι → ℝ :=
  positiveExtension f A⁺ - positiveExtension f A⁻

omit [Nonempty ν] [Fintype ι] in
lemma signedExtension_odd (f : E → ι → ℝ) (A : Matrix ν ν ℝ) :
    signedExtension f (-A) = -signedExtension f A := by
  simp [signedExtension, CFC.posPart_neg, CFC.negPart_neg]

omit [Nonempty ν] [Fintype ι] in
lemma signedExtension_smul_nonneg (f : E → ι → ℝ) (A : Matrix ν ν ℝ)
    {t : ℝ} (ht : 0 ≤ t) : signedExtension f (t • A) = t • signedExtension f A := by
  rw [signedExtension, CFC.posPart_smul_of_nonneg ht, CFC.negPart_smul_of_nonneg ht,
    positiveExtension_smul_nonneg f (CFC.posPart_nonneg A) ht,
    positiveExtension_smul_nonneg f (CFC.negPart_nonneg A) ht, ← smul_sub]
  rfl

lemma Admissible.signedExtension_sum {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) :
    ∑ i, signedExtension f A i = Matrix.trace A := by
  classical
  simp only [signedExtension, Pi.sub_apply, Finset.sum_sub_distrib,
    hf.positiveExtension_sum (CFC.posPart_nonneg A), hf.positiveExtension_sum (CFC.negPart_nonneg A)]
  rw [← Matrix.trace_sub, CFC.posPart_sub_negPart A hA]

lemma Admissible.signedExtension_abs_sum {f : E → ι → ℝ} (hf : Admissible f)
    {A : Matrix ν ν ℝ} (hA : IsSelfAdjoint A) :
    ∑ i, |signedExtension f A i| = Matrix.trace (CFC.abs A) := by
  classical
  have hcoord (i : ι) : |signedExtension f A i| =
      positiveExtension f A⁺ i + positiveExtension f A⁻ i := by
    have hp := hf.positiveExtension_nonneg A⁺ i
    have hn := hf.positiveExtension_nonneg A⁻ i
    have hprod := hf.positiveExtension_orthogonal (CFC.posPart_nonneg A)
      (CFC.negPart_nonneg A) (CFC.posPart_mul_negPart A) i
    rcases mul_eq_zero.mp hprod with hz | hz
    · simp [signedExtension, hz, abs_of_nonneg hn]
    · simp [signedExtension, hz, abs_of_nonneg hp]
  simp_rw [hcoord]
  rw [Finset.sum_add_distrib, hf.positiveExtension_sum (CFC.posPart_nonneg A),
    hf.positiveExtension_sum (CFC.negPart_nonneg A), ← Matrix.trace_add,
    CFC.posPart_add_negPart A hA]

omit [Nonempty ν] in
lemma matrix_posPart_continuousOn :
    ContinuousOn (fun A : Matrix ν ν ℝ => A⁺) {A | IsSelfAdjoint A} := by
  have hc : Continuous (fun A : Matrix ν ν ℝ => (1 / 2 : ℝ) • (CFC.abs A + A)) :=
    (continuous_const (y := (1 / 2 : ℝ))).smul (CFC.continuous_abs.add continuous_id)
  apply hc.continuousOn.congr
  intro A hA
  change A⁺ = (1 / 2 : ℝ) • (CFC.abs A + A)
  rw [CFC.abs_add_self A hA, two_smul, smul_add]
  module

omit [Nonempty ν] in
lemma matrix_negPart_continuousOn :
    ContinuousOn (fun A : Matrix ν ν ℝ => A⁻) {A | IsSelfAdjoint A} := by
  have hc : Continuous (fun A : Matrix ν ν ℝ => (1 / 2 : ℝ) • (CFC.abs A - A)) :=
    (continuous_const (y := (1 / 2 : ℝ))).smul (CFC.continuous_abs.sub continuous_id)
  apply hc.continuousOn.congr
  intro A hA
  change A⁻ = (1 / 2 : ℝ) • (CFC.abs A - A)
  rw [CFC.abs_sub_self A hA, two_smul, smul_add]
  module

lemma Admissible.signedExtension_continuousOn {f : E → ι → ℝ} (hf : Admissible f) :
    ContinuousOn (signedExtension f) {A : Matrix ν ν ℝ | IsSelfAdjoint A} := by
  apply ContinuousOn.sub
  · exact hf.positiveExtension_continuousOn.comp matrix_posPart_continuousOn
      (fun A _ => CFC.posPart_nonneg A)
  · exact hf.positiveExtension_continuousOn.comp matrix_negPart_continuousOn
      (fun A _ => CFC.negPart_nonneg A)

end SignedExtension

end BorsukNine

end OAI
