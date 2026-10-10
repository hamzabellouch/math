import Mathlib
import OAI.Analysis.AffineBernstein.GlobalDetRatio

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section EntireGlobalDet

lemma sectionBalance_tangentShift {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) {ρ : ℝ} (hbal : SectionBalance univ u ρ)
    (a : Space n) (h : ℝ) : SectionBalance univ (tangentShift u a h) ρ := by
  have he (x : Space n) (t : ℝ) : tangentSection univ (tangentShift u a h) x t = tangentSection univ u x t := by
    ext y
    simp only [tangentSection,mem_ofPred_eq,tangentHeight_tangentShift (hu.differentiable (by simp))]
  intro x hx t ht y hy
  rw [he] at hy ⊢
  exact hbal x hx t ht y hy

/-- Once genuine balance is produced, the whole Hessian determinant is
bounded above and below by positive constants. The proof uses only that
balance and the original affine maximal equation. -/
theorem balanced_global_det_bounds {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c ≤ (hessian u x).det ∧ (hessian u x).det ≤ C := by
  let v := tangentShift u 0 0
  have hv : ContDiff ℝ ∞ v := contDiffOn_univ.mp (contDiffOn_tangentShift hu.contDiffOn 0 0)
  have hh (x : Space n) : hessian v x = hessian u x := hessian_tangentShift isOpen_univ hu.contDiffOn 0 0 (mem_univ x)
  have hvp (x : Space n) : (hessian v x).PosDef := hh x ▸ hp x
  have hvm := affineMaximalOn_tangentShift isOpen_univ hu.contDiffOn hm 0 0
  have hv0 : v 0=0 := by simp [v,tangentShift,tangentHeight]
  have hdv0 : fderiv ℝ v 0=0 := by
    dsimp [v]
    rw [fderiv_tangentShift (hu.differentiable (by simp) 0)]
    exact sub_self _
  obtain ⟨c,C,hc,hC,H⟩ := centered_balanced_global_det_ratio hn hv hvp hvm hv0 hdv0 hρ hρ1
    (sectionBalance_tangentShift hu hbal 0 0)
  refine ⟨c*(hessian u 0).det,C*(hessian u 0).det,mul_pos hc (hp 0).det_pos,mul_pos hC (hp 0).det_pos,?_⟩
  intro x
  simpa only [hh] using H x

/-- Further consequence of the unchanged EXACT main hypotheses: the domain
is entire and its Hessian determinant has global positive lower and upper
bounds. Quadratic rigidity is still a separate obligation. -/
theorem affineMaximal_entire_global_det_bounds {n : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hc : EuclideanGraphComplete Ω u) :
    Ω = univ ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, c ≤ (hessian u x).det ∧ (hessian u x).det ≤ C := by
  obtain ⟨hU,ρ,hρ,hρ1,hbal⟩ := affineMaximal_entire_and_balance hn hn9 hΩ hne hcv hu hp hm hc
  refine ⟨hU,?_⟩
  subst Ω
  exact balanced_global_det_bounds (by omega) (contDiffOn_univ.mp hu) (fun x => hp x (mem_univ x)) hm hρ hρ1 hbal

end EntireGlobalDet



end
end AffineBernstein
end

end OAI
