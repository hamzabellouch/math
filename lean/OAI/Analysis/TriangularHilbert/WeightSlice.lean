import OAI.Analysis.TriangularHilbert.GaussianExpectation

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι]

lemma weight_slice_integrable {h : ℝ} (hh : 0 < h) (a b d : ℝ)
    (c f : ι → ℝ) (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    Integrable (fun z : ℝ×ℝ => weight h a (chart 2 d z 0) (σ 0)*weight h b (chart 2 d z 1) (σ 1)*
      ∑ m, f m*weight h (c m) (chart 2 d z v) (σ v)) := by
  have hi : Integrable (fun z : ℝ×ℝ => ∑ m, f m*(weight h a (chart 2 d z 0) (σ 0)*
      weight h b (chart 2 d z 1) (σ 1)*weight h (c m) (chart 2 d z v) (σ v))) :=
    integrable_finsetSum _ (fun m _ => (weight_three_integrable hh a b (c m) d σ hσ v).const_mul (f m))
  convert hi using 1
  ext z
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

lemma planeIntegral_weight_slice {h : ℝ} (hh : 0 < h) (a b d : ℝ)
    (c f : ι → ℝ) (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) (v : Three) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*
      ∑ m, f m*weight h (c m) (p v) (σ v)) d =
      ∑ m, f m*planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*weight h (c m) (p v) (σ v)) d := by
  unfold planeIntegral
  have he (z : ℝ×ℝ) : weight h a (chart 2 d z 0) (σ 0)*weight h b (chart 2 d z 1) (σ 1)*
      (∑ m, f m*weight h (c m) (chart 2 d z v) (σ v)) =
      ∑ m, f m*(weight h a (chart 2 d z 0) (σ 0)*weight h b (chart 2 d z 1) (σ 1)*weight h (c m) (chart 2 d z v) (σ v)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun m _ => (weight_three_integrable hh a b (c m) d σ hσ v).const_mul (f m))]
  simp only [integral_const_mul]

lemma weight_slice_zero_integral {h : ℝ} (hh : 0 < h) (a b d : ℝ) (c f : ι → ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*
      ∑ m, f m*weight h (c m) (p 0) (σ 0)) d = h^2*∑ m, f m*(h*density (2*σ 0) (a-c m)) := by
  rw [planeIntegral_weight_slice hh a b d c f σ hσ 0]
  simp_rw [planeIntegral_weight_repeat_zero h a b _ d σ hσ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

lemma weight_slice_one_integral {h : ℝ} (hh : 0 < h) (a b d : ℝ) (c f : ι → ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*
      ∑ m, f m*weight h (c m) (p 1) (σ 1)) d = h^2*∑ m, f m*(h*density (2*σ 1) (b-c m)) := by
  rw [planeIntegral_weight_slice hh a b d c f σ hσ 1]
  simp_rw [planeIntegral_weight_repeat_one h a b _ d σ hσ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

lemma weight_slice_two_integral {h : ℝ} (hh : 0 < h) (a b : ℝ) (c f : ι → ℝ)
    (σ : Three → ℝ) (hσ : ∀ v, 0 < σ v) :
    planeIntegral (fun p => weight h a (p 0) (σ 0)*weight h b (p 1) (σ 1)*
      ∑ m, f m*weight h (c m) (p 2) (σ 2)) 0 = h^2*∑ m, f m*(h*density (σ 0+σ 1+σ 2) (a+b+c m)) := by
  rw [planeIntegral_weight_slice hh a b 0 c f σ hσ 2]
  simp_rw [planeIntegral_weight_triple h a b _ σ hσ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring
end
end TriangularHilbert.Heat
end

end OAI
