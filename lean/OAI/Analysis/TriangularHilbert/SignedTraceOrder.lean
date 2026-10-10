import OAI.Analysis.TriangularHilbert.PlaneDissipation

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def windowDiags (u : ι → ℝ) (p : Three → ℝ) (s : ℝ) : Three → Matrix ι ι ℂ :=
  fun v => Matrix.diagonal (fun i => (windowRatio s (u i-p v):ℂ))

def windowTrace (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ) (p : Three → ℝ) (s : ℝ) : ℂ :=
  Matrix.trace (windowDiags u p s 0 * heatArray A h u p (fun _ => (11/10)*s) 0 *
    windowDiags u p s 1 * heatArray A h u p (fun _ => (11/10)*s) 1 *
    windowDiags u p s 2 * heatArray A h u p (fun _ => (11/10)*s) 2)

lemma rowBare_strict_eq_base (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p : Three → ℝ) (s : ℝ) (v : Three) :
    rowBare A (heatWeights h u p (fun z => strictRate v z*s)) v =
      rowBare A (heatWeights h u p (fun _ => (11/10)*s)) v := by
  apply rowBare_congr
  intro w hw i
  simp [heatWeights,strictRate,hw]

omit [Fintype ι] [DecidableEq ι] in
lemma heatWeights_strict_le_base {h s : ℝ} (hh : 0 < h) (hs : 0 < s)
    (u : ι → ℝ) (p : Three → ℝ) (v w : Three) (i : ι) :
    heatWeights h u p (fun z => strictRate v z*s) w i ≤
      Real.sqrt (11/10)*heatWeights h u p (fun _ => (11/10)*s) w i := by
  have hr : 1 ≤ Real.sqrt (11/10) := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  by_cases hw : w=v
  · subst w
    simp only [heatWeights,strictRate,ite_true,one_mul,weight]
    have hd := mul_le_mul_of_nonneg_left (density_le_lambda hs (u i-p v)) hh.le
    simpa only [mul_left_comm] using hd
  · simp only [heatWeights,strictRate,ite_eq_right hw]
    exact le_mul_of_one_le_left (weight_pos hh (by positivity) _ _).le hr

lemma strict_starGram_le_base (A : Three → Matrix ι ι ℂ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s) (u : ι → ℝ) (p : Three → ℝ) (v : Three) :
    starGram (heatArray A h u p (fun z => strictRate v z*s)) v ≤
      Real.sqrt (11/10) • starGram (heatArray A h u p (fun _ => (11/10)*s)) v := by
  have hb (w : Three) (i : ι) : 0 ≤ heatWeights h u p (fun _ => (11/10)*s) w i :=
    (weight_pos hh (by positivity) _ _).le
  have ht (w : Three) (i : ι) : 0 ≤ heatWeights h u p (fun z => strictRate v z*s) w i :=
    (weight_pos hh (mul_pos (strictRate_pos v w) hs) _ _).le
  unfold heatArray
  rw [starGram_weightedArray _ _ ht,starGram_weightedArray _ _ hb,
    rowBare_strict_eq_base,← weightedGram_smul]
  exact weightedGram_mono _ _ _ (fun a => heatWeights_strict_le_base hh hs u p v a.1 a.2)

lemma windowInsertion_eq_score (A : Three → Matrix ι ι ℂ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s) (u : ι → ℝ) (p : Three → ℝ) (v : Three) :
    starInsert (heatArray A h u p (fun _ => (11/10)*s)) (windowDiags u p s) v =
      Real.sqrt s • starInsert (heatArray A h u p (fun z => strictRate v z*s))
        (heatScores u p (fun z => strictRate v z*s)) v := by
  have hb (w : Three) (i : ι) : 0 ≤ heatWeights h u p (fun _ => (11/10)*s) w i :=
    (weight_pos hh (by positivity) _ _).le
  have ht (w : Three) (i : ι) : 0 ≤ heatWeights h u p (fun z => strictRate v z*s) w i :=
    (weight_pos hh (mul_pos (strictRate_pos v w) hs) _ _).le
  unfold heatArray windowDiags heatScores
  rw [← rowBare_insert _ _ _ hb,← rowBare_insert _ _ _ ht,
    rowBare_strict_eq_base,← weightedGram_smul]
  apply weightedGram_rowBare_congr
  intro i
  dsimp only
  simp only [heatWeights,strictRate,ite_true,one_mul,weight]
  have hn : density ((11/10)*s) (u i-p v) ≠ 0 := (density_pos (by positivity) _).ne'
  unfold windowRatio
  rw [oddWindow_score hs]
  simp only [div_eq_mul_inv]
  calc
    _ = (Real.sqrt s*(h*density s (u i-p v)*score (u i) (p v) s))*
        (density ((11/10)*s) (u i-p v)*(density ((11/10)*s) (u i-p v))⁻¹) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hn]; ring

lemma windowStarCost_le (A : Three → Matrix ι ι ℂ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s) (u : ι → ℝ) (p : Three → ℝ) (v : Three) :
    hessianCost (starGram (heatArray A h u p (fun _ => (11/10)*s)) v)
      (starInsert (heatArray A h u p (fun _ => (11/10)*s)) (windowDiags u p s) v) ≤
      2*s*heatCost A h u p (fun z => strictRate v z*s) v v := by
  have hσ : ∀ z, 0 < strictRate v z*s := fun z => mul_pos (strictRate_pos v z) hs
  let P := starGram (heatArray A h u p (fun z => strictRate v z*s)) v
  let K := starInsert (heatArray A h u p (fun z => strictRate v z*s))
    (heatScores u p (fun z => strictRate v z*s)) v
  have hsol : ∃ Y, sylv (CFC.sqrt P) Y = K := sylv_solvable_inserted_gram _ _
  have hsol' : ∃ Y, sylv (CFC.sqrt P) Y = Real.sqrt s • K := by
    obtain ⟨Y,hY⟩ := hsol
    exact ⟨Real.sqrt s • Y,by rw [sylv_smul_right,hY]⟩
  have hc := hessianCost_le_of_le_smul
    (Matrix.posSemidef_conjTranspose_mul_self (rowStar (heatArray A h u p (fun _ => (11/10)*s)) v))
    hsol' (by positivity : 0 < Real.sqrt (11/10)) (strict_starGram_le_base A hh hs u p v)
  rw [windowInsertion_eq_score A hh hs,heatCost_center A hh u p hσ]
  change hessianCost _ (Real.sqrt s • K) ≤ 2*s*hessianCost P K
  rw [hessianCost_smul_direction hsol,Real.sq_sqrt hs.le] at hc
  have hr : Real.sqrt (Real.sqrt (11/10)) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · rw [Real.sqrt_le_iff]; norm_num
  have hn : 0 ≤ hessianCost P K := hessianCost_nonneg _ _
  exact hc.trans (by
    calc
      _ ≤ 2*(s*hessianCost P K) := mul_le_mul_of_nonneg_right hr (mul_nonneg hs.le hn)
      _ = _ := by ring)

lemma windowTrace_le (A : Three → Matrix ι ι ℂ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s) (u : ι → ℝ) (p : Three → ℝ) :
    ‖windowTrace A h u p s‖ ≤ (440/3)*s*∑ v,
      heatCost A h u p (fun z => strictRate v z*s) v v := by
  have hD (v : Three) : (windowDiags u p s v).IsHermitian := by
    unfold windowDiags Matrix.IsHermitian
    rw [Matrix.diagonal_conjTranspose]
    simp
  have hd : ‖blockD (windowDiags u p s)‖ ≤ 44 :=
    norm_blockD_real_diagonal_le _ (by norm_num) (fun v i => abs_windowRatio_le hs _)
  have hm := mixed_trace_le (heatArray A h u p (fun _ => (11/10)*s)) (windowDiags u p s) hD
  have hi := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset Three)) =>
    windowStarCost_le A hh hs u p v)
  apply hm.trans
  calc
    _ ≤ (5/3:ℝ)*44*(∑ v, 2*s*heatCost A h u p (fun z => strictRate v z*s) v v) := by
      gcongr
      exact Finset.sum_nonneg (fun v _ => hessianCost_nonneg _ _)
    _ = _ := by rw [← Finset.mul_sum]; ring

end
end TriangularHilbert.Heat
end

end OAI
