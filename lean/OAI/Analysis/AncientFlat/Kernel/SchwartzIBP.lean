import OAI.Analysis.AncientFlat.Energy.EnergyLaplacian

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff SchwartzMap Laplacian
namespace FlatDuality
open ParametrixUniqueness
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma integrable_mul_bounded {f g : V → ℂ} (hf : Integrable f)
    (hg : Continuous g) (hb : Bounded g) : Integrable (fun x => f x*g x) := by
  obtain ⟨M,hM,hb⟩ := hb
  exact (hf.norm.mul_const M).mono' (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Eventually.of_forall (fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)))
def schwartzDir (v : V) (f : SchwartzMap V ℂ) : SchwartzMap V ℂ :=
  SchwartzMap.evalCLM ℝ V ℂ v (SchwartzMap.fderivCLM ℝ V ℂ f)
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma schwartzDir_apply (v : V) (f : SchwartzMap V ℂ) (x : V) :
    schwartzDir v f x=dir v (f : V → ℂ) x := rfl
lemma integral_dir (v : V) (φ : SchwartzMap V ℂ) (u : V → ℂ)
    (hu : ContDiff ℝ 1 u) (hb : BoundedJets 1 u) :
    (∫ x, φ x*dir v u x)=-(∫ x, schwartzDir v φ x*u x) := by
  apply integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℂ) (v := v)
  · exact integrable_mul_bounded (schwartzDir v φ).integrable hu.continuous hb.zero
  · exact integrable_mul_bounded φ.integrable (contDiff_dir (n := 0) v u hu).continuous (hb.dir hu v).zero
  · exact integrable_mul_bounded φ.integrable hu.continuous hb.zero
  · exact fun x _ => φ.differentiableAt
  · exact fun x _ => (hu.differentiable (by norm_num)).differentiableAt
lemma integral_dir_dir (v : V) (φ : SchwartzMap V ℂ) (u : V → ℂ)
    (hu : ContDiff ℝ 2 u) (hb : BoundedJets 2 u) :
    (∫ x, φ x*dir v (dir v u) x)=∫ x, schwartzDir v (schwartzDir v φ) x*u x := by
  rw [integral_dir v φ (dir v u) (contDiff_dir v u hu) (hb.dir hu v)]
  rw [integral_dir v (schwartzDir v φ) u (hu.of_le (by norm_num)) (hb.of_le (by norm_num)),neg_neg]
lemma integral_laplacian (φ : SchwartzMap V ℂ) (u : V → ℂ)
    (hu : ContDiff ℝ 2 u) (hb : BoundedJets 2 u) :
    (∫ x, φ x*Δ u x)=∫ x, (Δ φ : SchwartzMap V ℂ) x*u x := by
  have he : (fun x => (Δ φ : SchwartzMap V ℂ) x)=Δ (φ : V → ℂ) :=
    funext (SchwartzMap.laplacian_apply φ)
  simp_rw [he,laplacian_eq_sum_dir u hu,laplacian_eq_sum_dir (φ : V → ℂ) (φ.smooth 2)]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  rw [integral_finsetSum,integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => integral_dir_dir _ φ u hu hb)
  · intro i _
    exact integrable_mul_bounded (schwartzDir _ (schwartzDir _ φ)).integrable hu.continuous hb.zero
  · intro i _
    exact integrable_mul_bounded φ.integrable
      (contDiff_dir (n := 0) _ _ (contDiff_dir (n := 1) _ _ hu)).continuous
      ((hb.dir hu _).dir (contDiff_dir _ _ hu) _).zero
lemma integral_bilaplacian (φ : SchwartzMap V ℂ) (u : V → ℂ)
    (hu : ContDiff ℝ 4 u) (hb : BoundedJets 4 u) :
    (∫ x, φ x*Δ (Δ u) x)=∫ x, (Δ (Δ φ : SchwartzMap V ℂ) : SchwartzMap V ℂ) x*u x := by
  rw [integral_laplacian φ (Δ u) (ClassicalIBP.contDiff_laplacian u 2 hu) (hb.laplacian 2 hu),
    integral_laplacian (Δ φ : SchwartzMap V ℂ) u (hu.of_le (by norm_num)) (hb.of_le (by norm_num))]
end FlatDuality

end

end OAI
