import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicSmoothness
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularUniqueness

namespace OAI

/-! A nonzero classical harmonic eigenmode cannot vanish on an origin interval. -/

open Set Filter Topology
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralPhysicalCircularField_regular (νp νm η : ℂ) (m : ℕ)
    (Q : ℂ) (r : ℝ) (Z : E₄) :
    spectralPhysicalCircularField νp νm η m Q r Z=
      spectralRegularField 11 (spectralDiagonalCoefficient m Q) (spectralCrossCoefficient m Q)
        (-Complex.I*νp/2-η/(r : ℂ)^2) (Complex.I*νm/2-η/(r : ℂ)^2) r Z := by
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [spectralPhysicalCircularField,spectralRegularField] <;> ring

theorem spectralPhysicalCircularField_bounded_on (νp νm η : ℂ) (m : ℕ)
    (Q : ℝ → ℂ) (L R : ℝ) (hL : 0 < L) (hQ : ContinuousOn Q (Icc L R)) :
    ∃ C : ℝ, ∀ r ∈ Icc L R, ∀ Z : E₄,
      ‖spectralPhysicalCircularField νp νm η m (Q r) r Z‖ ≤ C*‖Z‖ := by
  have hr : ContinuousOn (fun r : ℝ => (r : ℂ)) (Icc L R) := Complex.continuous_ofReal.continuousOn
  have hn (r : ℝ) (hr : r ∈ Icc L R) : (r : ℂ) ≠ 0 := by exact_mod_cast (hL.trans_le hr.1).ne'
  have hk : ContinuousOn (fun r : ℝ => 11/(r : ℂ)) (Icc L R) := continuousOn_const.div hr hn
  have hi : ContinuousOn (fun r : ℝ => Complex.I*(r : ℂ)/2) (Icc L R) := by fun_prop
  have he : ContinuousOn (fun r : ℝ => η/(r : ℂ)^2) (Icc L R) :=
    continuousOn_const.div (hr.pow 2) (fun r hr => pow_ne_zero _ (hn r hr))
  have hD : ContinuousOn (fun r => spectralDiagonalCoefficient m (Q r)) (Icc L R) := by
    unfold spectralDiagonalCoefficient
    fun_prop
  have hC : ContinuousOn (fun r => spectralCrossCoefficient m (Q r)) (Icc L R) := by
    unfold spectralCrossCoefficient
    fun_prop
  have hb : ContinuousOn (fun r => spectralRegularFieldBound 11
      (spectralDiagonalCoefficient m (Q r)) (spectralCrossCoefficient m (Q r))
      (-Complex.I*νp/2-η/(r : ℂ)^2) (Complex.I*νm/2-η/(r : ℂ)^2) r) (Icc L R) := by
    unfold spectralRegularFieldBound
    exact ((((((continuousOn_const.add (hk.add hi).norm).add (hk.sub hi).norm).add
      hD.norm).add hC.norm).add (continuousOn_const.sub he).norm).add
      (continuousOn_const.sub he).norm)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hb
  refine ⟨C,fun r hr Z => ?_⟩
  rw [spectralPhysicalCircularField_regular]
  apply (spectralRegularField_norm 11 _ _ _ _ r Z).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC r hr)

theorem harmonicRadialState_zero_of_zero (a b : ℝ) (m : ℕ) (Q f g : ℝ → ℂ)
    (η lam : ℂ) (hQ : ContinuousOn Q (Ioi 0)) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q η lam f g)
    (t : ℝ) (ht : 0 < t) (hz : harmonicRadialState f g t=0)
    (r : ℝ) (hr : 0 < r) : harmonicRadialState f g r=0 := by
  let Z := harmonicRadialState f g
  let A := spectralPhysicalCircularField (-2*(a : ℂ)+2*Complex.I*(b : ℂ)-2*lam)
    (-2*(a : ℂ)-2*Complex.I*(b : ℂ)-2*lam) η m
  have hd (x : ℝ) (hx : 0 < x) : HasDerivAt Z (A (Q x) x (Z x)) x :=
    harmonicRadialState_hasDerivAt a b m Q f g η lam hf hg he x hx
  have hc : Continuous Z :=
    (hf.continuous.prodMk (hf.continuous_deriv (by norm_num))).prodMk
      (hg.continuous.prodMk (hg.continuous_deriv (by norm_num)))
  by_cases hrt : r ≤ t
  · obtain ⟨C,hC⟩ := spectralPhysicalCircularField_bounded_on _ _ η m Q r t hr
      (hQ.mono (fun x hx => hr.trans_le hx.1))
    exact spectral_zero_on_annulus Z (fun x => A (Q x) x (Z x)) r t C hc.continuousOn
      (fun x hx => hd x (hr.trans_le hx.1)) (fun x hx => hC x hx (Z x)) hz r ⟨le_rfl,hrt⟩
  · have htr : t ≤ r := le_of_not_ge hrt
    obtain ⟨C,hC⟩ := spectralPhysicalCircularField_bounded_on _ _ η m Q t r ht
      (hQ.mono (fun x hx => ht.trans_le hx.1))
    exact eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hc.continuousOn
      (fun x hx => (hd x (ht.trans_le hx.1)).hasDerivWithinAt) hz
      (fun x hx => hC x ⟨hx.1,hx.2.le⟩ (Z x)) r ⟨htr,le_rfl⟩

theorem harmonicRadialEigenpair_nonzero_on_ball (a b : ℝ) (m : ℕ) (Q f g : ℝ → ℂ)
    (η lam : ℂ) (hQ : ContinuousOn Q (Ioi 0)) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q η lam f g)
    (hne : ∃ r : ℝ, 0 < r ∧ (f r ≠ 0 ∨ g r ≠ 0)) (R : ℝ) (hR : 0 < R) :
    ∃ r ∈ Ioc 0 R, f r ≠ 0 ∨ g r ≠ 0 := by
  by_contra h
  push Not at h
  have hzero (r : ℝ) (hr : r ∈ Ioc 0 R) : f r=0 ∧ g r=0 := by
    have hh := h r hr
    tauto
  let t := R/2
  have ht : t ∈ Ioo 0 R := by dsimp [t]; constructor <;> linarith
  have hfe : f =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact (hzero r ⟨hr.1,hr.2.le⟩).1
  have hge : g =ᶠ[𝓝 t] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact (hzero r ⟨hr.1,hr.2.le⟩).2
  have hz : harmonicRadialState f g t=0 := by
    simp only [harmonicRadialState,hfe.eq_of_nhds,hge.eq_of_nhds,
      hfe.deriv_eq,hge.deriv_eq,deriv_const]
    rfl
  obtain ⟨r,hr,hn⟩ := hne
  have hh := harmonicRadialState_zero_of_zero a b m Q f g η lam hQ hf hg he t ht.1 hz r hr
  rcases hn with hn | hn
  · exact hn (congrArg (fun Z : E₄ => Z.1.1) hh)
  · exact hn (congrArg (fun Z : E₄ => Z.2.1) hh)

theorem harmonicRadialEigenpair_zero_of_ball (a b : ℝ) (m : ℕ) (Q f g : ℝ → ℂ)
    (η lam : ℂ) (hQ : ContinuousOn Q (Ioi 0)) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q η lam f g)
    (R : ℝ) (hR : 0 < R) (hz : ∀ r ∈ Ioc 0 R, f r=0 ∧ g r=0) :
    ∀ r : ℝ, 0 < r → f r=0 ∧ g r=0 := by
  intro r hr
  have hn : ¬(f r ≠ 0 ∨ g r ≠ 0) := by
    intro hn
    obtain ⟨t,ht,htn⟩ := harmonicRadialEigenpair_nonzero_on_ball a b m Q f g η lam
      hQ hf hg he ⟨r,hr,hn⟩ R hR
    rcases htn with htn | htn
    · exact htn (hz t ht).1
    · exact htn (hz t ht).2
  tauto

end DefocusingNLS

end OAI
