import Mathlib
import OAI.Probability.SKGap.Localization.GeneralTemplateRegularity
import OAI.Probability.SKGap.Gaussian.GaussianProductPower

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ T : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
variable [TopologicalSpace T] [FirstCountableTopology T]

lemma matrixEntryMean_continuous (F : T→EuclideanSpace ℝ κ→Matrix ι ι ℝ)
    (hF : ∀ θ,∃ L,LipschitzWith L (F θ)) (hc : ∀ x,Continuous (fun θ=>F θ x))
    {C : ℝ} (hb : ∀ θ x i k,|F θ x i k| ≤ C) :
    Continuous (fun θ=>matrixEntryMean (F θ)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  apply continuous_of_dominated (bound:=fun _=>C)
  · intro θ
    obtain ⟨L,hL⟩ := hF θ
    exact (gaussianProduct_integrable_lipschitz (matrixEntry_lip hL i k)).aestronglyMeasurable
  · intro θ
    exact ae_of_all _ (fun g=>by simpa only [norm_eq_abs] using hb θ (WithLp.toLp 2 g) i k)
  · exact integrable_const _
  · exact ae_of_all _ (fun g=>(hc (WithLp.toLp 2 g)).matrix_elem i k)

lemma matrixCentered_continuous (F : T→EuclideanSpace ℝ κ→Matrix ι ι ℝ)
    (hF : ∀ θ,∃ L,LipschitzWith L (F θ)) (hc : ∀ x,Continuous (fun θ=>F θ x))
    {C : ℝ} (hb : ∀ θ x i k,|F θ x i k| ≤ C) (x : EuclideanSpace ℝ κ) :
    Continuous (fun θ=>matrixCentered (F θ) x) := by
  exact (hc x).sub (matrixEntryMean_continuous F hF hc hb)
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

lemma real_continuous_of_sqrt_increment {X : Type*} [PseudoMetricSpace X] {g : X→ℝ} {C : ℝ}
    (h : ∀ x y,|g x-g y| ≤ C*sqrt (dist x y)) : Continuous g := by
  rw [continuous_iff_continuousAt]
  intro y
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun x=>norm_nonneg _))
    (Eventually.of_forall (fun x=>by simpa only [Real.norm_eq_abs] using h x y))
  have hc : Continuous (fun x : X=>C*sqrt (dist x y)) :=
    continuous_const.mul (Real.continuous_sqrt.comp (continuous_id.dist continuous_const))
  simpa only [dist_self,Real.sqrt_zero,mul_zero] using hc.tendsto y

lemma templateMatrix_continuous [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hD : 0 ≤ D) (F : List (WordTemplateLetter m)) (M : Matrix ι ι ℝ) :
    Continuous (fun θ : WordParameter m ι=>templateMatrix f R hR j D F θ M) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  apply real_continuous_of_sqrt_increment (C:=
    (wordParameterCoeff ⟨actualWordBound f R j 1 D,(actualWordBound_pos f hR hj zero_le_one hD).le⟩ F.length:ℝ)*templateHolder f R j D)
  intro θ η
  have hh := (templateMatrix_increments f hR hj hD F θ η).1 M
  apply (matrix_entry_le_opNorm _ i k).trans
  simpa only [NNReal.coe_mk,mul_assoc] using! hh

lemma templateMatrix_bounds [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hD : 0 ≤ D) (F : List (WordTemplateLetter m)) (θ : WordParameter m ι) :
    (∀ M,opNorm (templateMatrix f R hR j D F θ M) ≤ (actualWordBound f R j 1 D)^F.length) ∧
    LipschitzWith ((F.length:NNReal)*⟨actualWordBound f R j 1 D,(actualWordBound_pos f hR hj zero_le_one hD).le⟩^F.length)
      (templateMatrix f R hR j D F θ) := by
  have hh := actualWord_bounds f hR hj zero_le_one hD
    (fun i=>(templateInverse_bounds zero_le_one θ i).1) (fun i=>(templateInverse_bounds zero_le_one θ i).2)
    ⟨zero_le_one,le_rfl⟩ (templateWord D θ F) (templateWord_bounded hD θ F)
  simpa only [templateMatrix,templateWord,List.length_map] using hh

lemma templateGaussian_centered_continuous [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hD : 0 ≤ D) (F : List (WordTemplateLetter m)) (r : ℝ)
    (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    Continuous (fun θ : WordParameter m ι=>matrixCentered
      (fun x : EuclideanSpace ℝ (MatrixCoordinates ι)=>templateMatrix f R hR j D F θ (goeMatrix r x)) g) := by
  apply matrixCentered_continuous
  · intro θ
    exact ⟨_,(templateMatrix_bounds f hR hj hD F θ).2.comp (goeMatrix_L2_lipschitz r)⟩
  · intro x
    exact templateMatrix_continuous f hR hj hD F _
  · intro θ x i k
    exact (matrix_entry_le_opNorm _ i k).trans ((templateMatrix_bounds f hR hj hD F θ).1 _)
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

lemma generalTemplateMatrix_continuous [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (F : List (WordTemplateLetter m)) (M : Matrix ι ι ℝ) :
    Continuous (fun θ : WordParameter m ι=>generalTemplateMatrix f R hR j A D F θ M) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  apply real_continuous_of_sqrt_increment (C:=
    (wordParameterCoeff ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩ F.length:ℝ)*generalTemplateHolder f R j A D)
  intro θ η
  have hh := (generalTemplateMatrix_increments f hR hj hA hD F θ η).1 M
  apply (matrix_entry_le_opNorm _ i k).trans
  simpa only [NNReal.coe_mk,mul_assoc] using! hh

lemma generalTemplateMatrix_bounds [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (F : List (WordTemplateLetter m)) (θ : WordParameter m ι) :
    (∀ M,opNorm (generalTemplateMatrix f R hR j A D F θ M) ≤ (actualWordBound f R j A D)^F.length) ∧
    LipschitzWith ((F.length:NNReal)*⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩^F.length)
      (generalTemplateMatrix f R hR j A D F θ) := by
  have hh := actualWord_bounds f hR hj hA hD
    (fun i=>(templateInverse_bounds hA θ i).1) (fun i=>(templateInverse_bounds hA θ i).2)
    ⟨zero_le_one,le_rfl⟩ (templateWord D θ F) (templateWord_bounded hD θ F)
  simpa only [generalTemplateMatrix,templateWord,List.length_map] using hh

lemma generalTemplateGaussian_centered_continuous [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) (F : List (WordTemplateLetter m)) (r : ℝ)
    (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    Continuous (fun θ : WordParameter m ι=>matrixCentered
      (fun x : EuclideanSpace ℝ (MatrixCoordinates ι)=>generalTemplateMatrix f R hR j A D F θ (goeMatrix r x)) g) := by
  apply matrixCentered_continuous
  · intro θ
    exact ⟨_,(generalTemplateMatrix_bounds f hR hj hA hD F θ).2.comp (goeMatrix_L2_lipschitz r)⟩
  · intro x
    exact generalTemplateMatrix_continuous f hR hj hA hD F _
  · intro θ x i k
    exact (matrix_entry_le_opNorm _ i k).trans ((generalTemplateMatrix_bounds f hR hj hA hD F θ).1 _)
end SKGap
end
end

end OAI
