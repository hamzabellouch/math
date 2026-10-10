import Mathlib
import OAI.Probability.SKRatio.Matrices.GaussianFiniteIBPError
import OAI.Probability.SKRatio.Matrices.MatrixCoordinates

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma symmetricElementary_comm (a b : ι) : symmetricElementary a b = symmetricElementary b a :=
  add_comm _ _

omit [Fintype ι] in
lemma goeMatrix_updated_observable_derivative {r : ℝ}
    {H : Matrix ι ι ℝ → ℝ} {g : MatrixCoordinates ι → ℝ} {a b : ι} {d : ℝ}
    (hd : HasDerivAt (fun t : ℝ => H (goeMatrix r g+t • symmetricElementary a b)) d 0) :
    HasDerivAt (fun t => H (goeMatrix r (Function.update g (.inl (a,b)) t)))
      ((sqrt (2*r)/2)*d) (g (.inl (a,b))) := by
  have ha := ((hasDerivAt_id (g (.inl (a,b)))).sub_const (g (.inl (a,b)))).const_mul (sqrt (2*r)/2)
  have ho : HasDerivAt (fun t : ℝ => H (goeMatrix r g+t • symmetricElementary a b)) d
      ((fun y : ℝ => (sqrt (2*r)/2)*(y-g (.inl (a,b)))) (g (.inl (a,b)))) := by simpa using hd
  have hh := ho.comp (g (.inl (a,b))) ha
  simpa only [Function.comp_def,goeMatrix_update,mul_one,one_mul,mul_comm,id_eq] using! hh

theorem goe_IBP_error {r : ℝ} (hr : 0 ≤ r) (a b : ι)
    {H : Matrix ι ι ℝ → ℝ} {d : (MatrixCoordinates ι → ℝ) → ℝ}
    {L : ℝ≥0} {C D : ℝ} {s : Set (MatrixCoordinates ι → ℝ)}
    (hf : LipschitzWith L (fun g => H (goeMatrix r g)))
    (hC : ∀ g, ‖H (goeMatrix r g)‖ ≤ C)
    (hd : Measurable d) (hD : ∀ g, ‖d g‖ ≤ D) (hs : MeasurableSet s)
    (hder : ∀ g ∈ s, HasDerivAt (fun t : ℝ => H (goeMatrix r g+t • symmetricElementary a b)) (d g) 0) :
    |(∫ g, goeMatrix r g a b * H (goeMatrix r g)
        ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)) -
      r*(∫ g, d g ∂Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))| ≤
      (sqrt (2*r)*(L:ℝ)+r*D)*
        (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real sᶜ := by
  let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
  let c : ℝ := sqrt (2*r)/2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc2 : 2*c^2 = r := by
    dsimp [c]; rw [div_pow,Real.sq_sqrt (by positivity)]; ring
  have hD' : ∀ g, ‖c*d g‖ ≤ c*D := fun g => by
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left (hD g) hc
  have h₁ := gaussianFinite_IBP_error (.inl (a,b)) hf hC (hd.const_mul c) hD' hs
    (fun g hg => goeMatrix_updated_observable_derivative (hder g hg))
  have h₂ := gaussianFinite_IBP_error (.inl (b,a)) hf hC (hd.const_mul c) hD' hs
    (fun g hg => goeMatrix_updated_observable_derivative (by
      simpa only [symmetricElementary_comm b a] using hder g hg))
  rw [integral_const_mul] at h₁ h₂
  have hi (i : MatrixCoordinates ι) : Integrable (fun g : MatrixCoordinates ι → ℝ =>
      g i*H (goeMatrix r g)) μ := by
    simpa only [mul_comm] using (integrable_eval (i := i) IsGaussian.integrable_id).bdd_mul
      hf.continuous.aestronglyMeasurable (ae_of_all _ hC)
  have he : (∫ g, goeMatrix r g a b*H (goeMatrix r g) ∂μ) =
      c*((∫ g, g (.inl (a,b))*H (goeMatrix r g) ∂μ)+
        ∫ g, g (.inl (b,a))*H (goeMatrix r g) ∂μ) := by
    simp_rw [goeMatrix,mul_assoc,add_mul]
    rw [integral_const_mul,integral_add (hi _) (hi _)]
  change |(∫ g, goeMatrix r g a b*H (goeMatrix r g) ∂μ)-r*(∫ g, d g ∂μ)| ≤ _
  rw [he]
  have he' : c*((∫ g, g (.inl (a,b))*H (goeMatrix r g) ∂μ)+
        ∫ g, g (.inl (b,a))*H (goeMatrix r g) ∂μ)-r*(∫ g, d g ∂μ) =
      c*(((∫ g, g (.inl (a,b))*H (goeMatrix r g) ∂μ)-c*(∫ g, d g ∂μ))+
        ((∫ g, g (.inl (b,a))*H (goeMatrix r g) ∂μ)-c*(∫ g, d g ∂μ))) := by
    rw [← hc2]; ring
  rw [he',abs_mul,abs_of_nonneg hc]
  calc
    _ ≤ c*(|((∫ g, g (.inl (a,b))*H (goeMatrix r g) ∂μ)-c*(∫ g, d g ∂μ))|+
        |((∫ g, g (.inl (b,a))*H (goeMatrix r g) ∂μ)-c*(∫ g, d g ∂μ))|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hc
    _ ≤ c*(((L:ℝ)+c*D)*μ.real sᶜ+((L:ℝ)+c*D)*μ.real sᶜ) :=
      mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hc
    _ = _ := by
      change _ = (sqrt (2*r)*(L:ℝ)+r*D)*μ.real sᶜ
      have hec : sqrt (2*r) = 2*c := by dsimp [c]; ring
      rw [hec,← hc2]; ring

end SKRatioGaussian

end
end
end
end

end OAI
