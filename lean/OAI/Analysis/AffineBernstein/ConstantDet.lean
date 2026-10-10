import Mathlib
import OAI.Analysis.AffineBernstein.EntireGlobalDet
import OAI.Analysis.AffineBernstein.BoundedHarmonic

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section ConstantDetProducer

 theorem balanced_bounded_harmonic_constant {n : ℕ} (hn : 1 ≤ n)
    {u F : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ)
    (hF : ContDiff ℝ ∞ F) (hFb : BddBelow (range F)) (hFa : BddAbove (range F))
    (hLF : ∀ x, inverseHessianTrace u F x=0) : ∀ x y, F x=F y := by
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
  apply centered_balanced_bounded_harmonic_constant hn hv hvp hvm hv0 hdv0 hρ hρ1
    (sectionBalance_tangentShift hu hbal 0 0) hF hFb hFa
  intro x
  simpa only [inverseHessianTrace,hh] using hLF x

/-- Constant determinant is *produced* by the original equation and actual
balanced normalization family, rather than inserted as a hypothesis. -/
theorem balanced_affineMaximal_constant_det {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
    ∀ x y, (hessian u x).det=(hessian u y).det := by
  obtain ⟨c,C,hc,hC,Hb⟩ := balanced_global_det_bounds hn hu hp hm hρ hρ1 hbal
  have hw : ContDiff ℝ ∞ (affineWeight u) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact contDiffAt_affineWeight hu.contDiffAt (hp x)
  have hβ : -(((n:ℝ)+1)/((n:ℝ)+2))<0 := neg_neg_of_pos (div_pos (by positivity) (by positivity))
  have hwbelow : BddBelow (range (affineWeight u)) := by
    refine ⟨(C:ℝ)^(-(((n:ℝ)+1)/((n:ℝ)+2))),?_⟩
    rintro y ⟨x,rfl⟩
    exact Real.rpow_le_rpow_of_nonpos (hp x).det_pos (Hb x).2 hβ.le
  have hwupper : BddAbove (range (affineWeight u)) := by
    refine ⟨(c:ℝ)^(-(((n:ℝ)+1)/((n:ℝ)+2))),?_⟩
    rintro y ⟨x,rfl⟩
    exact Real.rpow_le_rpow_of_nonpos hc (Hb x).1 hβ.le
  have H := balanced_bounded_harmonic_constant hn hu hp hm hρ hρ1 hbal hw hwbelow hwupper
    (fun x => affineMaximal_inverseHessianTrace_zero hm (mem_univ x) (hp x))
  intro x y
  exact (Real.rpow_left_inj (hp x).det_pos.le (hp y).det_pos.le hβ.ne).mp (H x y)

/-- Consequence of every unchanged main hypothesis: the domain is all of
space and the full Hessian determinant is one positive constant. The
remaining Jörgens--Calabi--Pogorelov rigidity is not claimed here. -/
theorem affineMaximal_entire_and_constant_det {n : ℕ} (hn : 3 ≤ n) (hn9 : n ≤ 9)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef) (hm : AffineMaximalOn Ω u)
    (hc : EuclideanGraphComplete Ω u) :
    Ω = univ ∧ ∃ D : ℝ, 0 < D ∧ ∀ x, (hessian u x).det=D := by
  obtain ⟨hU,ρ,hρ,hρ1,hbal⟩ := affineMaximal_entire_and_balance hn hn9 hΩ hne hcv hu hp hm hc
  refine ⟨hU,?_⟩
  subst Ω
  refine ⟨(hessian u 0).det,(hp 0 (mem_univ 0)).det_pos,?_⟩
  intro x
  exact balanced_affineMaximal_constant_det (by omega) (contDiffOn_univ.mp hu)
    (fun y => hp y (mem_univ y)) hm hρ hρ1 hbal x 0

end ConstantDetProducer



end
end AffineBernstein
end

end OAI
