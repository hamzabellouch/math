import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinPlane

namespace OAI

/-! Exact passage from the physical two-channel boundary condition to the
profile gauge used by the coercive weak formulation. -/

open Filter Topology
namespace DefocusingNLS

noncomputable def spectralGaugeColumns (q : ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  spectralTwoColumns (q,star q) (Complex.I*q,-Complex.I*star q)

noncomputable def spectralGaugeInverse (q : ℂ) : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  spectralValueInverse (q,star q) (Complex.I*q,-Complex.I*star q)

theorem spectralGaugeColumns_det (q : ℂ) (hq : q ≠ 0) :
    spectralValueDet (q,star q) (Complex.I*q,-Complex.I*star q) ≠ 0 := by
  have hs : star q ≠ 0 := star_ne_zero.mpr hq
  change q*(-Complex.I*star q)-star q*(Complex.I*q) ≠ 0
  rw [show q*(-Complex.I*star q)-star q*(Complex.I*q)=
    (-2*Complex.I)*(q*star q) by ring]
  exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (mul_ne_zero hq hs)

theorem spectralGaugeInverse_columns (q : ℂ) (hq : q ≠ 0) (x : ℂ × ℂ) :
    spectralGaugeInverse q (spectralGaugeColumns q x)=x :=
  spectralValueInverse_apply_columns _ _ x (spectralGaugeColumns_det q hq)

theorem spectralGaugeColumns_inverse (q : ℂ) (hq : q ≠ 0) (x : ℂ × ℂ) :
    spectralGaugeColumns q (spectralGaugeInverse q x)=x :=
  spectralTwoColumns_apply_inverse _ _ x (spectralGaugeColumns_det q hq)

noncomputable def spectralGaugeRobin (q dq : ℂ) (M : ℂ × ℂ →L[ℂ] ℂ × ℂ) :
    ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  (spectralGaugeInverse q).comp (M.comp (spectralGaugeColumns q)-spectralGaugeColumns dq)

theorem spectralGaugeRobin_condition (q dq : ℂ) (hq : q ≠ 0)
    (M : ℂ × ℂ →L[ℂ] ℂ × ℂ) (x dx : ℂ × ℂ) :
    spectralGaugeColumns q dx+spectralGaugeColumns dq x=M (spectralGaugeColumns q x) ↔
      dx=spectralGaugeRobin q dq M x := by
  constructor
  · intro h
    have he := eq_sub_iff_add_eq.mpr h
    calc
      dx = spectralGaugeInverse q (spectralGaugeColumns q dx) :=
        (spectralGaugeInverse_columns q hq dx).symm
      _ = spectralGaugeInverse q (M (spectralGaugeColumns q x)-spectralGaugeColumns dq x) :=
        congrArg (spectralGaugeInverse q) he
      _ = spectralGaugeRobin q dq M x := rfl
  · intro h
    have he : spectralGaugeColumns q dx=M (spectralGaugeColumns q x)-spectralGaugeColumns dq x := by
      rw [h]
      exact spectralGaugeColumns_inverse q hq _
    exact eq_sub_iff_add_eq.mp he

theorem spectralGaugeColumns_tendsto (q : ℕ → ℂ) (q₀ : ℂ)
    (hq : Tendsto q atTop (𝓝 q₀)) :
    Tendsto (fun n => spectralGaugeColumns (q n)) atTop (𝓝 (spectralGaugeColumns q₀)) := by
  have hs := continuous_star.continuousAt.tendsto.comp hq
  exact spectralTwoColumns_tendsto _ _ _ _ (hq.prodMk_nhds hs)
    ((hq.const_mul Complex.I).prodMk_nhds (hs.const_mul (-Complex.I)))

theorem spectralGaugeInverse_tendsto (q : ℕ → ℂ) (q₀ : ℂ)
    (hq : Tendsto q atTop (𝓝 q₀)) (hne : q₀ ≠ 0) :
    Tendsto (fun n => spectralGaugeInverse (q n)) atTop (𝓝 (spectralGaugeInverse q₀)) := by
  have hs := continuous_star.continuousAt.tendsto.comp hq
  exact spectralValueInverse_tendsto _ _ _ _ (hq.prodMk_nhds hs)
    ((hq.const_mul Complex.I).prodMk_nhds (hs.const_mul (-Complex.I)))
    (spectralGaugeColumns_det q₀ hne)

theorem spectralGaugeRobin_tendsto (q dq : ℕ → ℂ) (q₀ dq₀ : ℂ)
    (M : ℕ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (M₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (hq : Tendsto q atTop (𝓝 q₀)) (hdq : Tendsto dq atTop (𝓝 dq₀))
    (hM : Tendsto M atTop (𝓝 M₀)) (hne : q₀ ≠ 0) :
    Tendsto (fun n => spectralGaugeRobin (q n) (dq n) (M n)) atTop
      (𝓝 (spectralGaugeRobin q₀ dq₀ M₀)) := by
  exact spectralComposition_tendsto _ _ _ _ (spectralGaugeInverse_tendsto q q₀ hq hne)
    ((spectralComposition_tendsto _ _ _ _ hM (spectralGaugeColumns_tendsto q q₀ hq)).sub
      (spectralGaugeColumns_tendsto dq dq₀ hdq))

end DefocusingNLS

end OAI
