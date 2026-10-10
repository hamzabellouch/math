import OAI.Probability.SLE.Loewner.SlitChartClosingPath
import OAI.Probability.SLE.Loewner.InverseBoundaryShrink

namespace OAI

/-! Small inverse half-disks for static slit charts, from the closed boundary arcs. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma SimpleSlitChart.inverse_arc_traps_radial_point
    {arc : C(unitInterval,ℂ)} (P : SimpleSlitChart arc)
    (x r ρ θ : ℝ) (hρ : 0<ρ) (hρr : ρ<r) (hθ : θ∈Ioo 0 Real.pi)
    (c : ℝ → ℂ) (hc : Continuous c)
    (he : ∀ a∈Ioo 0 Real.pi, c a=P.inverse ((x:ℂ)+(r:ℂ)*Complex.exp ((a:ℂ)*Complex.I)))
    (hc0 : c 0∉(upperHalfPlane \ range arc)) (hcπ : c Real.pi∉(upperHalfPlane \ range arc))
    (q : Path (c Real.pi) (c 0)) (hq : ∀ u, q u∉(upperHalfPlane \ range arc))
    (w : ℂ) (ε : ℝ) (hε : 0<ε)
    (hcball : ∀ a∈Icc 0 Real.pi, c a∈ball w ε)
    (hqball : ∀ u, q u∈ball w ε) :
    P.inverse ((x:ℂ)+(ρ:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))∈ball w ε := by
  let E := Complex.exp ((θ:ℂ)*Complex.I)
  have hE : 0<E.im := exp_strip_halfplane (x := (θ:ℂ)*Complex.I) (by simpa using hθ)
  obtain ⟨R,hR⟩ := exists_gt (max r ((w.im+ε)/E.im))
  have hrR : r<R := (le_max_left _ _).trans_lt hR
  have hRE : w.im+ε<R*E.im :=
    (div_lt_iff₀ hE).mp ((le_max_right _ _).trans_lt hR)
  have hRH := univalent_polar_point_mem x R θ ((hρ.trans hρr).trans hrR) hθ
  have hRout : P.inverse ((x:ℂ)+(R:ℂ)*E)∉ball w ε := by
    intro hm
    have him : R*E.im≤(P.inverse ((x:ℂ)+(R:ℂ)*E)).im := by
      simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
        zero_mul,add_zero,zero_add] using P.inverse_im_ge hRH
    have hdist : ‖P.inverse ((x:ℂ)+(R:ℂ)*E)-w‖<ε := by
      simpa only [mem_ball,dist_eq_norm] using hm
    have hle := (le_abs_self (P.inverse ((x:ℂ)+(R:ℂ)*E)-w).im).trans
      (Complex.abs_im_le_norm (P.inverse ((x:ℂ)+(R:ℂ)*E)-w))
    rw [Complex.sub_im] at hle
    linarith
  have hi : InjOn (P.inverse) upperHalfPlane := by
    intro a ha b hb hab
    have := congrArg (P.forward) hab
    simpa only [P.right_inverse a ha,P.right_inverse b hb] using this
  exact polar_arc_traps_radial_point P.inverse_differentiable hi P.inverse_mapsTo
    x r ρ R θ hρ hρr hrR hθ c hc he hc0 hcπ q hq w ε hε hcball hqball hRout

lemma SimpleSlitChart.small_boundary_halfdisk
    {arc : C(unitInterval,ℂ)} (P : SimpleSlitChart arc) (x ε : ℝ) (hε : 0<ε) :
    ∃ r : ℝ, 0<r ∧ ∃ z : ℂ, ∀ w∈upperHalfPlane,
      dist w (x:ℂ)<r → dist (P.inverse w) z<ε := by
  obtain ⟨v,c,q,_,hc,he,hcb,hqb,hc0,hcπ,_,_⟩ :=
    P.exists_small_inverse_closing_path x 0 ε hε
  refine ⟨Real.exp v,Real.exp_pos _,c 0,?_⟩
  intro w hwH hwr
  obtain ⟨ρ,θ,hρ,hθ,hρeq,hweq⟩ := polar_representation_upperHalfPlane x hwH
  have hρr : ρ<Real.exp v := by simpa only [hρeq,dist_eq_norm] using hwr
  rw [hweq]
  apply P.inverse_arc_traps_radial_point x (Real.exp v) ρ θ hρ hρr hθ c hc
  · intro a ha
    rw [he a ha,Complex.exp_add]
    rw [←Complex.ofReal_exp]
  · simpa only [P.isOpen_domain.interior_eq] using hc0.2
  · simpa only [P.isOpen_domain.interior_eq] using hcπ.2
  · exact fun u => (hqb u).2
  · exact hε
  · exact hcb
  · exact fun u => (hqb u).1

end SLEExactGauge

end

end OAI
