import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.CorridorNormalization
import OAI.Probability.CriticalPercolation.Gluing.MoveWitness
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseExit
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseLinear

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def ellipseTime (Psi : V → ℂ) (c d : Circle) (x : V) : ℝ :=
  EllipseLinear.time (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im (Psi x).re (Psi x).im

def ellipseHeight (Psi : V → ℂ) (c d : Circle) (x : V) : ℝ :=
  EllipseLinear.height (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im (Psi x).re (Psi x).im

lemma circle_component_bounds (c : Circle) : |(c : ℂ).re|≤1 ∧ |(c : ℂ).im|≤1 := by
  constructor
  · exact (Complex.abs_re_le_norm _).trans_eq (Circle.norm_coe c)
  · exact (Complex.abs_im_le_norm _).trans_eq (Circle.norm_coe c)

lemma ellipse_coordinates_norm_bound (Psi : V → ℂ) (c d : Circle)
    (hdet : (1 : ℝ)/4≤|EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im|)
    (x : V) : |ellipseTime Psi c d x|≤16*‖Psi x‖ ∧ |ellipseHeight Psi c d x|≤16*‖Psi x‖ := by
  exact EllipseLinear.row_bound (circle_component_bounds c).1 (circle_component_bounds c).2
    (circle_component_bounds d).1 (circle_component_bounds d).2 hdet (Psi x).re (Psi x).im
    ‖Psi x‖ (norm_nonneg _) (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)

lemma ellipse_coordinates_sub (Psi : V → ℂ) (c d : Circle) (x y : V) :
    ellipseTime Psi c d x-ellipseTime Psi c d y=
      ellipseTime (fun v => Psi v-Psi y) c d x ∧
    ellipseHeight Psi c d x-ellipseHeight Psi c d y=
      ellipseHeight (fun v => Psi v-Psi y) c d x := by
  constructor
  · exact EllipseLinear.time_sub _ _ _ _ _ _ _ _
  · exact EllipseLinear.height_sub _ _ _ _ _ _ _ _

lemma ellipse_coordinates_step (Psi : V → ℂ) (c d : Circle)
    (hdet : (1 : ℝ)/4≤|EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im|)
    (D : ℝ) (hPsi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖Psi x-Psi y‖≤D) :
    (∀ ⦃x y⦄, G.fullGraph.Adj x y → |ellipseTime Psi c d x-ellipseTime Psi c d y|≤16*D) ∧
    (∀ ⦃x y⦄, G.fullGraph.Adj x y → |ellipseHeight Psi c d x-ellipseHeight Psi c d y|≤16*D) := by
  constructor
  · intro x y hxy
    rw [(ellipse_coordinates_sub Psi c d x y).1]
    exact (ellipse_coordinates_norm_bound (fun v => Psi v-Psi y) c d hdet x).1.trans (by nlinarith [hPsi hxy])
  · intro x y hxy
    rw [(ellipse_coordinates_sub Psi c d x y).2]
    exact (ellipse_coordinates_norm_bound (fun v => Psi v-Psi y) c d hdet x).2.trans (by nlinarith [hPsi hxy])

theorem ellipseExit_boxMove (Psi Psi' : V → ℂ) (o : V) (m : ℕ) (c d : Circle)
    (hdet : (1 : ℝ)/4≤|EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im|)
    (eps : ℝ) (heps : 0<eps) (heps' : eps<1/10) (ho : Psi o=0)
    (hpert : ∀ x, ‖Psi x-Psi' x‖≤(eps/1000)*‖Psi' x‖) (b : Bool) :
    G.ellipseExit Psi' (G.vertexBall o m) (eps/1000) (if b then c else d) ⊆
      G.boxMove (ellipseTime Psi c d) (ellipseHeight Psi c d) m (eps/8) 30 o (Corridor.sign b) := by
  intro ω hω
  obtain ⟨a,ha,x,w,hw,hx⟩ := (G.ellipseExit_iff _ _ _ _ ω).mp hω
  have hzeta : 0<eps/1000 := by positivity
  have hzeta' : eps/1000<1/10000 := by linarith
  have hdet' : EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im≠0 := by
    intro he
    rw [he,abs_zero] at hdet
    norm_num at hdet
  have hto : ellipseTime Psi c d o=0 := by simp [ellipseTime,ho,EllipseLinear.time]
  have hzo : ellipseHeight Psi c d o=0 := by simp [ellipseHeight,ho,EllipseLinear.height]
  have hpath : ∀ y∈w.support, ‖Psi y‖≤(1+eps/1000)^2 := by
    intro y hy
    have htri : ‖Psi y‖≤‖Psi y-Psi' y‖+‖Psi' y‖ := by
      simpa only [sub_add_cancel] using norm_add_le (Psi y-Psi' y) (Psi' y)
    nlinarith [hpert y,hw y hy]
  have hterminal : ‖Psi x-((if b then c else d) : Circle)‖≤4*(eps/1000) := by
    have htri : ‖Psi x-((if b then c else d) : Circle)‖≤
        ‖Psi x-Psi' x‖+‖Psi' x-((if b then c else d) : Circle)‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (Psi x-Psi' x)
        (Psi' x-((if b then c else d) : Circle))
    nlinarith [hpert x,hw x w.end_mem_support,mul_pos hzeta (by linarith : 0<1-eps/1000)]
  have hcenter : EllipseLinear.time (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im
      (((if b then c else d) : Circle) : ℂ).re (((if b then c else d) : Circle) : ℂ).im=1 ∧
      EllipseLinear.height (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im
      (((if b then c else d) : Circle) : ℂ).re (((if b then c else d) : Circle) : ℂ).im=Corridor.sign b := by
    cases b
    · exact EllipseLinear.center_right _ _ _ _ hdet'
    · exact EllipseLinear.center_left _ _ _ _ hdet'
  have hend := ellipse_coordinates_norm_bound (fun v => Psi v-((if b then c else d) : Circle)) c d hdet x
  have htend : |ellipseTime Psi c d x-1|≤eps/8 := by
    rw [←hcenter.1,ellipseTime,EllipseLinear.time_sub]
    exact hend.1.trans ((mul_le_mul_of_nonneg_left hterminal (by norm_num)).trans
      (EllipseLinear.source_budgets heps heps').1.le)
  have hzend : |ellipseHeight Psi c d x-Corridor.sign b|≤eps/8 := by
    rw [←hcenter.2,ellipseHeight,EllipseLinear.height_sub]
    exact hend.2.trans ((mul_le_mul_of_nonneg_left hterminal (by norm_num)).trans
      (EllipseLinear.source_budgets heps heps').1.le)
  refine ⟨a,ha,x,w,?_,?_,?_⟩
  · intro y hy
    rw [hto,hzo,sub_zero,sub_zero]
    have hnorm := ellipse_coordinates_norm_bound Psi c d hdet y
    have hbudget : 16*‖Psi y‖≤30 := (mul_le_mul_of_nonneg_left (hpath y hy) (by norm_num)).trans
      (EllipseLinear.source_budgets heps heps').2.le
    exact ⟨hnorm.1.trans hbudget,hnorm.2.trans hbudget⟩
  · simpa only [hto,zero_add] using htend
  · simpa only [hzo,zero_add] using hzend

end CriticalPercolation.BondGraph
end
end
end

end OAI
