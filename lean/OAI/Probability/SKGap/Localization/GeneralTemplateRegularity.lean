import Mathlib
import OAI.Probability.SKGap.Matrix.GlobalWordIncrement

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

def generalTemplateMatrix (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (j A D : ℝ)
    (F : List (WordTemplateLetter m)) (θ : WordParameter m ι) : Matrix ι ι ℝ→Matrix ι ι ℝ :=
  actualWord f R hR j (templateInverse A θ) 1 (templateWord D θ F)

def generalTemplateHolder (f : 𝓢(ℝ,ℂ)) (R j A D : ℝ) : ℝ :=
  globalWordHolder f R j A D*sqrt (templateScale A D)

lemma generalTemplateHolder_nonneg (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    0 ≤ generalTemplateHolder f R j A D :=
  mul_nonneg (globalWordHolder_nonneg f hR hj hA hD) (sqrt_nonneg _)

theorem generalTemplateMatrix_increments [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (F : List (WordTemplateLetter m)) (θ η : WordParameter m ι) :
    let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj hA hD).le⟩
    let Δ : NNReal := ⟨generalTemplateHolder f R j A D*sqrt (dist θ η),mul_nonneg (generalTemplateHolder_nonneg f hR hj hA hD) (sqrt_nonneg _)⟩
    (∀ M,opNorm (generalTemplateMatrix f R hR j A D F θ M-generalTemplateMatrix f R hR j A D F η M) ≤
      (wordParameterCoeff B F.length:ℝ)*Δ) ∧
    LipschitzWith (wordMixedCoeff B F.length*Δ)
      (fun M=>generalTemplateMatrix f R hR j A D F θ M-generalTemplateMatrix f R hR j A D F η M) := by
  intro B Δ
  have hK : 0 ≤ templateScale A D := by dsimp [templateScale];positivity
  have hh := actualWord_pair_global f hR hj hA hD (mul_nonneg hK dist_nonneg)
    (fun i=>(templateInverse_bounds hA θ i).1) (fun i=>(templateInverse_bounds hA η i).1)
    (fun i=>(templateInverse_bounds hA θ i).2) (fun i=>(templateInverse_bounds hA η i).2)
    (templateInverse_dist hA hD θ η)
    (F.map (fun l=>(l.realize D θ,l.realize D η))) (templateWord_paired hA hD θ η F)
  simpa only [generalTemplateMatrix,generalTemplateHolder,B,Δ,List.length_map,List.map_map,
    Function.comp_def,templateWord,Real.sqrt_mul hK,mul_assoc] using! hh
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

omit [DecidableEq ι] in
lemma wordParameter_dist_le_one (θ η : WordParameter m ι) : dist θ η ≤ 1 := by
  apply (dist_pi_le_iff zero_le_one).mpr
  intro s
  rw [Subtype.dist_eq,Real.dist_eq]
  exact abs_le.mpr ⟨by linarith [(θ s).property.1,(η s).property.2],by linarith [(θ s).property.2,(η s).property.1]⟩

def templateMatrix (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (j D : ℝ)
    (F : List (WordTemplateLetter m)) (θ : WordParameter m ι) : Matrix ι ι ℝ→Matrix ι ι ℝ :=
  actualWord f R hR j (templateInverse 1 θ) 1 (templateWord D θ F)

def templateHolder (f : 𝓢(ℝ,ℂ)) (R j D : ℝ) : ℝ := wordHolderScale f R j 1+2*D+1

lemma templateHolder_nonneg (f : 𝓢(ℝ,ℂ)) {R j D : ℝ} (hj : 0 ≤ j) (hD : 0 ≤ D) :
    0 ≤ templateHolder f R j D := by
  have hh := wordHolderScale_ge_one f R 1 hj
  dsimp [templateHolder]
  linarith

lemma templateFactor_pair [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hD : 0 ≤ D) (θ η : WordParameter m ι) (l : WordTemplateLetter m) :
    let B : NNReal := ⟨actualWordBound f R j 1 D,(actualWordBound_pos f hR hj zero_le_one hD).le⟩
    let Δ : NNReal := ⟨templateHolder f R j D*sqrt (dist θ η),mul_nonneg (templateHolder_nonneg f hj hD) (sqrt_nonneg _)⟩
    MatrixFactorPairBounds B Δ
      ((l.realize D θ).eval f R hR j (templateInverse 1 θ) 1)
      ((l.realize D η).eval f R hR j (templateInverse 1 η) 1) := by
  intro B Δ
  have ha (θ : WordParameter m ι) (i : ι) := templateInverse_bounds zero_le_one θ i
  have hl (θ : WordParameter m ι) : (l.realize D θ).bounded D :=
    templateWord_bounded hD θ [l] _ (by simp [templateWord])
  obtain ⟨h1,h2⟩ := WordLetter.eval_bounds f hR hj zero_le_one hD (fun i=>(ha θ i).1) (fun i=>(ha θ i).2) ⟨zero_le_one,le_rfl⟩ _ (hl θ)
  obtain ⟨h3,h4⟩ := WordLetter.eval_bounds f hR hj zero_le_one hD (fun i=>(ha η i).1) (fun i=>(ha η i).2) ⟨zero_le_one,le_rfl⟩ _ (hl η)
  have hδ1 := wordParameter_dist_le_one θ η
  have hlarge : wordHolderScale f R j 1 ≤ templateHolder f R j D := by dsimp [templateHolder];linarith
  have haη (i : ι) : |templateInverse 1 θ i-templateInverse 1 η i| ≤ dist θ η := by
    simpa only [templateInverse,one_mul] using template_coord_dist θ η (none,i)
  refine ⟨h1,h3,h2,h4,?_,?_⟩
  · intro M
    cases l with
    | diag k =>
      change opNorm (diagonal (templateDiagonal D θ k)-diagonal (templateDiagonal D η k)) ≤ _
      rw [Matrix.diagonal_sub]
      apply (opNorm_diagonal_le (show 0 ≤ 2*D*dist θ η by positivity) (fun i=>?_)).trans
      · change 2*D*dist θ η ≤ templateHolder f R j D*sqrt (dist θ η)
        have hp := parameter_sqrt_small dist_nonneg hδ1
        have hH := wordHolderScale_ge_one f R 1 hj
        have hh : 2*D ≤ templateHolder f R j D := by dsimp [templateHolder];linarith
        exact mul_le_mul hh hp dist_nonneg (templateHolder_nonneg f hj hD)
      · have he : templateDiagonal D θ k i-templateDiagonal D η k i=
            (2*D)*((θ (some k,i):ℝ)-(η (some k,i):ℝ)) := by dsimp [templateDiagonal];ring
        rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*D)]
        exact mul_le_mul_of_nonneg_left (template_coord_dist θ η (some k,i)) (by positivity)
    | noise =>
      simp only [WordTemplateLetter.realize,WordLetter.eval,sub_self,opNorm,map_zero,norm_zero]
      exact Δ.coe_nonneg
    | inverse =>
      have hh := WordLetter.eval_pair f hR hj zero_le_one hD dist_nonneg hδ1
        (fun i=>(ha θ i).1) (fun i=>(ha η i).1) (fun i=>(ha θ i).2) (fun i=>(ha η i).2)
        haη WordLetter.inverse WordLetter.inverse trivial trivial trivial
      exact (hh.parameter M).trans (mul_le_mul_of_nonneg_right hlarge (sqrt_nonneg _))
  · cases l with
    | diag k =>
      exact (LipschitzWith.const (diagonal (templateDiagonal D θ k)-diagonal (templateDiagonal D η k))).weaken (show (0:NNReal) ≤ Δ from zero_le)
    | noise =>
      simpa only [WordTemplateLetter.realize,WordLetter.eval,sub_self] using
        (LipschitzWith.const (0:Matrix ι ι ℝ)).weaken (show (0:NNReal) ≤ Δ from zero_le)
    | inverse =>
      have hh := WordLetter.eval_pair f hR hj zero_le_one hD dist_nonneg hδ1
        (fun i=>(ha θ i).1) (fun i=>(ha η i).1) (fun i=>(ha θ i).2) (fun i=>(ha η i).2)
        haη WordLetter.inverse WordLetter.inverse trivial trivial trivial
      exact hh.increment.weaken (show (⟨wordHolderScale f R j 1*sqrt (dist θ η),mul_nonneg (zero_le_one.trans (wordHolderScale_ge_one f R 1 hj)) (sqrt_nonneg _)⟩:NNReal) ≤ Δ from
        mul_le_mul_of_nonneg_right hlarge (sqrt_nonneg _))

theorem templateMatrix_increments [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j D : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hD : 0 ≤ D) (F : List (WordTemplateLetter m)) (θ η : WordParameter m ι) :
    let B : NNReal := ⟨actualWordBound f R j 1 D,(actualWordBound_pos f hR hj zero_le_one hD).le⟩
    let Δ : NNReal := ⟨templateHolder f R j D*sqrt (dist θ η),mul_nonneg (templateHolder_nonneg f hj hD) (sqrt_nonneg _)⟩
    (∀ M,opNorm (templateMatrix f R hR j D F θ M-templateMatrix f R hR j D F η M) ≤
      (wordParameterCoeff B F.length:ℝ)*Δ) ∧
    LipschitzWith (wordMixedCoeff B F.length*Δ) (fun M=>templateMatrix f R hR j D F θ M-templateMatrix f R hR j D F η M) := by
  intro B Δ
  let G := F.map (fun l=>((l.realize D θ).eval f R hR j (templateInverse 1 θ) 1,
    (l.realize D η).eval f R hR j (templateInverse 1 η) 1))
  have hG : ∀ p∈G,MatrixFactorPairBounds B Δ p.1 p.2 := by
    intro p hp
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hp
    exact templateFactor_pair f hR hj hD θ η l
  simpa only [G,List.length_map,List.map_map,Function.comp_def,templateMatrix,actualWord,templateWord] using! matrixWord_pair_increments G hG
end SKGap
end
end

end OAI
