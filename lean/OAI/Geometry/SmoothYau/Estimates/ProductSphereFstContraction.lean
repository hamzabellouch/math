import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.SphereProjection
import OAI.Geometry.SmoothYau.Spectrum.UnitSphereProjection

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
section ProductSphereContraction
variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
  {n m : ℕ} [Fact (Module.finrank ℝ A = n+1)] [Fact (Module.finrank ℝ B = m+1)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [FiniteDimensional ℝ A] in
lemma productSphere_fst_contraction (b : Basis ι ℝ (WithLp 2 (Euclidean n×Euclidean m)))
    (p : Metric.sphere (0:A) 1) (a c : A) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j *
      inner ℝ (unitSphereFrame p (b j).fst) a * inner ℝ (unitSphereFrame p (b i).fst) c =
        inner ℝ a c-inner ℝ (p:A) a*inner ℝ (p:A) c := by
  simp_rw [unitSphereFrame_inner]
  rw [lp_inverse_gram_fst_contraction,unitSphereCoordinates_inner]
omit [FiniteDimensional ℝ B] in
lemma productSphere_snd_contraction (b : Basis ι ℝ (WithLp 2 (Euclidean n×Euclidean m)))
    (q : Metric.sphere (0:B) 1) (a c : B) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j *
      inner ℝ (unitSphereFrame q (b j).snd) a * inner ℝ (unitSphereFrame q (b i).snd) c =
        inner ℝ a c-inner ℝ (q:B) a*inner ℝ (q:B) c := by
  simp_rw [unitSphereFrame_inner]
  rw [lp_inverse_gram_snd_contraction,unitSphereCoordinates_inner]
omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] in
lemma productSphere_mixed_contraction (b : Basis ι ℝ (WithLp 2 (Euclidean n×Euclidean m)))
    (p : Metric.sphere (0:A) 1) (q : Metric.sphere (0:B) 1) (a : A) (c : B) :
    ∑ i, ∑ j, (Matrix.gram ℝ b)⁻¹ i j *
      inner ℝ (unitSphereFrame p (b j).fst) a * inner ℝ (unitSphereFrame q (b i).snd) c = 0 := by
  simp_rw [unitSphereFrame_inner]
  exact lp_inverse_gram_mixed_contraction b _ _
omit [FiniteDimensional ℝ A] in
lemma productSphere_fst_planar_contraction
    (e : Basis ι ℝ (WithLp 2 (Euclidean n×Euclidean m)))
    (p : Metric.sphere (0:A) 1) (a b : A)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    ∑ i, ∑ j, ((Matrix.gram ℝ e)⁻¹ i j : ℂ) *
      planarLinear a b (unitSphereFrame p (e j).fst) *
      planarLinear a b (unitSphereFrame p (e i).fst) = -(planarLinear a b (p : A))^2 := by
  simp_rw [planarLinear_apply_flip,complex_bilinear_expand]
  simp_rw [Finset.sum_add_distrib,← Finset.mul_sum,← Complex.ofReal_sum,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_add_distrib]
  rw [productSphere_fst_contraction,productSphere_fst_contraction,
    productSphere_fst_contraction,productSphere_fst_contraction]
  rw [ha,hb,hab,real_inner_comm a b,hab]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,pow_two]; ring
omit [FiniteDimensional ℝ B] in
lemma productSphere_snd_planar_contraction
    (e : Basis ι ℝ (WithLp 2 (Euclidean n×Euclidean m)))
    (p : Metric.sphere (0:B) 1) (a b : B)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    ∑ i, ∑ j, ((Matrix.gram ℝ e)⁻¹ i j : ℂ) *
      planarLinear a b (unitSphereFrame p (e j).snd) *
      planarLinear a b (unitSphereFrame p (e i).snd) = -(planarLinear a b (p : B))^2 := by
  simp_rw [planarLinear_apply_flip,complex_bilinear_expand]
  simp_rw [Finset.sum_add_distrib,← Finset.mul_sum,← Complex.ofReal_sum,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_add_distrib]
  rw [productSphere_snd_contraction,productSphere_snd_contraction,
    productSphere_snd_contraction,productSphere_snd_contraction]
  rw [ha,hb,hab,real_inner_comm a b,hab]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,pow_two]; ring
omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] in
lemma productSphere_mixed_planar_contraction
    (e : Basis ι ℝ (WithLp 2 (Euclidean n×Euclidean m)))
    (p : Metric.sphere (0:A) 1) (q : Metric.sphere (0:B) 1) (a b : A) (c d : B) :
    ∑ i, ∑ j, ((Matrix.gram ℝ e)⁻¹ i j : ℂ) *
      planarLinear a b (unitSphereFrame p (e j).fst) *
      planarLinear c d (unitSphereFrame q (e i).snd) = 0 := by
  simp_rw [planarLinear_apply_flip,complex_bilinear_expand]
  simp_rw [Finset.sum_add_distrib,← Finset.mul_sum,← Complex.ofReal_sum,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_add_distrib]
  rw [productSphere_mixed_contraction,productSphere_mixed_contraction,
    productSphere_mixed_contraction,productSphere_mixed_contraction]
  simp
end ProductSphereContraction
lemma complexIdentityPlanar (z : ℂ) : planarLinear (1:ℂ) Complex.I z = z := by
  apply Complex.ext <;> simp [planarLinear_apply,Complex.inner,Complex.mul_re,Complex.mul_im]
end YauCounterexamples
end

end OAI
