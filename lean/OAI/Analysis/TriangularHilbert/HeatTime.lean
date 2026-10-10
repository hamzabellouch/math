import OAI.Analysis.TriangularHilbert.GramDeriv

namespace OAI

universe uν uι uE

section
namespace TriangularHilbert.Heat
open MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology BigOperators
open Filter
noncomputable section

lemma hasDerivAt_of_coordinates {ν : Type uν} [Fintype ν] [DecidableEq ν]
    {f : (ν → ℝ) → ℝ} {g : ℝ → ν → ℝ} {g' k : ν → ℝ} {s : ℝ}
    (hf : DifferentiableAt ℝ f (g s)) (hg : HasDerivAt g g' s)
    (hk : ∀ i, HasDerivAt (fun q => f (Function.update (g s) i q)) (k i) (g s i)) :
    HasDerivAt (fun t => f (g t)) (∑ i, g' i * k i) s := by
  let T := fderiv ℝ f (g s)
  have hTi : ∀ i, T (Pi.single i 1) = k i := by
    intro i
    have hfu : HasFDerivAt f T (Function.update (g s) i (g s i)) := by
      simpa only [Function.update_eq_self] using hf.hasFDerivAt
    have hi := hfu.comp_hasDerivAt (g s i)
      ((hasFDerivAt_update (i := i) (g s) (g s i)).hasDerivAt)
    have he : (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ ℝ)) : ℝ →L[ℝ] (ν → ℝ)) 1 =
        Pi.single i (1 : ℝ) := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    rw [he] at hi
    exact hi.unique (hk i)
  have hT : T g' = ∑ i, g' i * k i := by
    conv_lhs => rw [← Finset.univ_sum_single g']
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he : Pi.single i (g' i) = g' i • Pi.single i (1 : ℝ) := by
      ext j
      by_cases hj : j = i <;> simp [hj]
    rw [he, map_smul, hTi, smul_eq_mul]
  have hd := hf.hasFDerivAt.comp_hasDerivAt s hg
  change HasDerivAt _ (T g') s at hd
  rwa [hT] at hd

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma weight_differentiableAt_variances (h a b : ℝ) (w : Three)
    {σ : Three → ℝ} (hσ : 0 < σ w) :
    DifferentiableAt ℝ (fun τ : Three → ℝ => weight h a b (τ w)) σ := by
  have hap : DifferentiableAt ℝ (fun τ : Three → ℝ => τ w) σ := by
    convert! (ContinuousLinearMap.proj w : (Three → ℝ) →L[ℝ] ℝ).differentiableAt
  have hd := (weight_hasDerivAt_variance h a b (σ w) hσ).differentiableAt.comp σ hap
  exact hd

omit [DecidableEq ι] in
lemma heatArray_differentiableAt_variances (A : Three → Matrix ι ι ℂ) {h : ℝ}
    (hh : 0 < h) (u : ι → ℝ) (p : Three → ℝ)
    {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    DifferentiableAt ℝ (fun τ => heatArray A h u p τ v) σ := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have hleft := (weight_differentiableAt_variances h (u i) (p v) v (hσ v)).sqrt
    (weight_pos hh (hσ v) (u i) (p v)).ne'
  have hright := (weight_differentiableAt_variances h (u j) (p (v+1)) (v+1) (hσ (v+1))).sqrt
    (weight_pos hh (hσ (v+1)) (u j) (p (v+1))).ne'
  exact ((Complex.ofRealCLM.differentiableAt.comp σ hleft).mul_const (A v i j)).mul
    (Complex.ofRealCLM.differentiableAt.comp σ hright)

omit [DecidableEq ι] in
lemma triangleBlocks_differentiableAt {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : E → Three → Matrix ι ι ℂ} {x : E} (hW : ∀ v, DifferentiableAt ℝ (fun y => W y v) x)
    (v w : Three) : DifferentiableAt ℝ (fun y => triangleBlocks (W y) v w) x := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have he v i j := (differentiableAt_pi.mp (differentiableAt_pi.mp (hW v) i) j)
  fin_cases v <;> fin_cases w <;> simp only [triangleBlocks]
  all_goals first | exact differentiableAt_const _ | exact he _ _ _ | exact (he _ _ _).star

lemma rowStar_differentiableAt {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : E → Three → Matrix ι ι ℂ} {x : E} (hW : ∀ v, DifferentiableAt ℝ (fun y => W y v) x)
    (v : Three) : DifferentiableAt ℝ (fun y => rowStar (W y) v) x := by
  apply differentiableAt_pi.mpr
  intro a
  apply differentiableAt_pi.mpr
  intro b
  simp only [rowStar_apply]
  by_cases ha : a.1 = v
  · simp only [ite_eq_left ha]
    exact differentiableAt_pi.mp (differentiableAt_pi.mp
      (triangleBlocks_differentiableAt hW a.1 b.1) a.2) b.2
  · simp only [ite_eq_right ha]
    exact differentiableAt_const _

lemma heatEnergy_differentiableAt_variances (A : Three → Matrix ι ι ℂ) {h : ℝ}
    (hh : 0 < h) (u : ι → ℝ) (p : Three → ℝ)
    {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    DifferentiableAt ℝ (fun τ => heatEnergy A h u p τ v) σ := by
  have hd := (energyGram_hasFDerivAt (rowStar (heatArray A h u p σ) v)).differentiableAt.comp σ
    (rowStar_differentiableAt (heatArray_differentiableAt_variances A hh u p hσ) v)
  exact hd

lemma heatEnergy_hasDerivAt_time (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {s : ℝ} (hs : 0 < s) (v : Three) :
    HasDerivAt (fun t => heatEnergy A h u p (fun w => α w * t) v)
      (∑ w, α w * heatVariance A h u p (fun w => α w * s) v w) s := by
  apply hasDerivAt_of_coordinates (f := fun τ => heatEnergy A h u p τ v)
    (g := fun t w => α w * t) (g' := α)
    (heatEnergy_differentiableAt_variances A hh u p (fun w => mul_pos (hα w) hs) v)
  · apply hasDerivAt_pi.mpr
    intro w
    convert! (hasDerivAt_id s).const_mul (α w) using 1
    simp only [mul_one]
  · exact fun w => heatEnergy_hasDerivAt_variance A hh u p (fun a => mul_pos (hα a) hs) v w

end
end TriangularHilbert.Heat
end

end OAI
