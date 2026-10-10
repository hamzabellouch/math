import OAI.Probability.SLE.Geometry.PolarBoundarySeparation
import OAI.Probability.SLE.Loewner.InverseBoundaryClosingPath

namespace OAI

/-! Small closed image semicircles force the images of their entire
half-disks to be small. The Loewner height inequality supplies the exterior
endpoint of each radial crossing. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology NNReal

namespace SLEExactGauge

lemma IsCapacityTwoWitness.inverse_im_ge
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) {w : ℂ} (hwH : w∈upperHalfPlane) :
    w.im≤(F t w).im := by
  have hz := hw.2.2.2.2.2.2.1 t hwH
  have h := hw.imag_ge_terminal t (F t w) hz 0 ⟨le_rfl,t.coe_nonneg⟩
  simpa only [Real.toNNReal_zero,hw.2.2.2.2.2.2.2.2.1 t w hwH,hw.initial_value (F t w) hz.1.1] using h

lemma IsCapacityTwoWitness.inverse_arc_traps_radial_point
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0)
    (x r ρ θ : ℝ) (hρ : 0<ρ) (hρr : ρ<r) (hθ : θ∈Ioo 0 Real.pi)
    (c : ℝ → ℂ) (hc : Continuous c)
    (he : ∀ a∈Ioo 0 Real.pi, c a=F t ((x:ℂ)+(r:ℂ)*Complex.exp ((a:ℂ)*Complex.I)))
    (hc0 : c 0∉survivingDomain γ t) (hcπ : c Real.pi∉survivingDomain γ t)
    (q : Path (c Real.pi) (c 0)) (hq : ∀ u, q u∉survivingDomain γ t)
    (w : ℂ) (ε : ℝ) (hε : 0<ε)
    (hcball : ∀ a∈Icc 0 Real.pi, c a∈ball w ε)
    (hqball : ∀ u, q u∈ball w ε) :
    F t ((x:ℂ)+(ρ:ℂ)*Complex.exp ((θ:ℂ)*Complex.I))∈ball w ε := by
  let E := Complex.exp ((θ:ℂ)*Complex.I)
  have hE : 0<E.im := exp_strip_halfplane (x := (θ:ℂ)*Complex.I) (by simpa using hθ)
  obtain ⟨R,hR⟩ := exists_gt (max r ((w.im+ε)/E.im))
  have hrR : r<R := (le_max_left _ _).trans_lt hR
  have hRE : w.im+ε<R*E.im :=
    (div_lt_iff₀ hE).mp ((le_max_right _ _).trans_lt hR)
  have hRH := univalent_polar_point_mem x R θ ((hρ.trans hρr).trans hrR) hθ
  have hRout : F t ((x:ℂ)+(R:ℂ)*E)∉ball w ε := by
    intro hm
    have him : R*E.im≤(F t ((x:ℂ)+(R:ℂ)*E)).im := by
      simpa only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
        zero_mul,add_zero,zero_add] using hw.inverse_im_ge t hRH
    have hdist : ‖F t ((x:ℂ)+(R:ℂ)*E)-w‖<ε := by
      simpa only [mem_ball,dist_eq_norm] using hm
    have hle := (le_abs_self (F t ((x:ℂ)+(R:ℂ)*E)-w).im).trans
      (Complex.abs_im_le_norm (F t ((x:ℂ)+(R:ℂ)*E)-w))
    rw [Complex.sub_im] at hle
    linarith
  have hi : InjOn (F t) upperHalfPlane := by
    intro a ha b hb hab
    have := congrArg (G t) hab
    simpa only [hw.2.2.2.2.2.2.2.2.1 t a ha,hw.2.2.2.2.2.2.2.2.1 t b hb] using this
  exact polar_arc_traps_radial_point (hw.2.2.2.2.1 t) hi (hw.2.2.2.2.2.2.1 t)
    x r ρ R θ hρ hρr hrR hθ c hc he hc0 hcπ q hq w ε hε hcball hqball hRout

lemma polar_representation_upperHalfPlane (x : ℝ) {w : ℂ} (hw : w∈upperHalfPlane) :
    ∃ ρ θ : ℝ, 0<ρ ∧ θ∈Ioo 0 Real.pi ∧ ρ=‖w-(x:ℂ)‖ ∧
      w=(x:ℂ)+(ρ:ℂ)*Complex.exp ((θ:ℂ)*Complex.I) := by
  let z := w-(x:ℂ)
  have him : 0<z.im := by
    change 0<w.im at hw
    simpa [z] using hw
  have hz : z≠0 := by
    intro h
    rw [h] at him
    exact (lt_irrefl 0) him
  have ha0 : 0<z.arg := lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr him.le)
    (fun h => him.ne' (Complex.arg_eq_zero_iff.mp h.symm).2)
  have haπ : z.arg<Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr him.ne')
  refine ⟨‖z‖,z.arg,norm_pos_iff.mpr hz,⟨ha0,haπ⟩,rfl,?_⟩
  rw [Complex.norm_mul_exp_arg_mul_I]
  dsimp [z]
  abel

lemma IsCapacityTwoWitness.small_boundary_halfdisk
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) (x ε : ℝ) (hε : 0<ε) :
    ∃ r : ℝ, 0<r ∧ ∃ z : ℂ, ∀ w∈upperHalfPlane,
      dist w (x:ℂ)<r → dist (F t w) z<ε := by
  obtain ⟨v,c,q,_,hc,he,hcb,hqb,hc0,hcπ,_,_⟩ :=
    hw.exists_small_inverse_closing_path t x 0 ε hε
  refine ⟨Real.exp v,Real.exp_pos _,c 0,?_⟩
  intro w hwH hwr
  obtain ⟨ρ,θ,hρ,hθ,hρeq,hweq⟩ := polar_representation_upperHalfPlane x hwH
  have hρr : ρ<Real.exp v := by simpa only [hρeq,dist_eq_norm] using hwr
  rw [hweq]
  apply hw.inverse_arc_traps_radial_point t x (Real.exp v) ρ θ hρ hρr hθ c hc
  · intro a ha
    rw [he a ha,Complex.exp_add]
    rw [←Complex.ofReal_exp]
  · simpa only [(isOpen_survivingDomain hw.1 t).interior_eq] using hc0.2
  · simpa only [(isOpen_survivingDomain hw.1 t).interior_eq] using hcπ.2
  · exact fun u => (hqb u).2
  · exact hε
  · exact hcb
  · exact fun u => (hqb u).1

end SLEExactGauge

end

end OAI
