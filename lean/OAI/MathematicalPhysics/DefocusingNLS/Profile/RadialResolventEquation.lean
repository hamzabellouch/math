import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialGreenResolvent

namespace OAI

/-! The positive resolvent solves the radial boundary value problem. -/

open Set Filter Topology
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialResolvent_pointwise (R : ℝ) (hR : 0 ≤ R) (f u : ℝ →ᵇ ℝ)
    (hu : u=radialGreenOperator R hR f+(1/2 : ℝ) • radialGreenOperator R hR u) (r : ℝ) :
    u r=radialDirichletKernel R (f+(1/2 : ℝ) • u) (radialClamp R r) := by
  have he := congrArg (fun v : ℝ →ᵇ ℝ => v r) hu
  change u r=radialDirichletKernel R f (radialClamp R r)+
    (1/2 : ℝ)*radialDirichletKernel R u (radialClamp R r) at he
  rw [radialDirichletKernel_add R _ f ((1/2 : ℝ) • (u : ℝ → ℝ)) f.continuous
    ((continuous_const.mul u.continuous)),radialDirichletKernel_smul]
  exact he

theorem radialResolvent_boundary (R : ℝ) (hR : 0 ≤ R) (f u : ℝ →ᵇ ℝ)
    (hu : u=radialGreenOperator R hR f+(1/2 : ℝ) • radialGreenOperator R hR u) : u R=0 := by
  rw [radialResolvent_pointwise R hR f u hu R,
    radialClamp_eq R R ⟨hR,le_rfl⟩,radialDirichletKernel_boundary]

theorem radialResolvent_poisson (R : ℝ) (hR : 0 ≤ R) (f u : ℝ →ᵇ ℝ)
    (hu : u=radialGreenOperator R hR f+(1/2 : ℝ) • radialGreenOperator R hR u)
    (r : ℝ) (hr : r ∈ Ioo 0 R) :
    -deriv (deriv u) r-11/r*deriv u r-(1/2 : ℝ)*u r=f r := by
  let g : ℝ → ℝ := fun t => f t+(1/2 : ℝ)*u t
  have hg : Continuous g := f.continuous.add (continuous_const.mul u.continuous)
  have he : (u : ℝ → ℝ) =ᶠ[𝓝 r] radialDirichletKernel R g := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    have he := radialResolvent_pointwise R hR f u hu t
    rw [radialClamp_eq R t ⟨ht.1.le,ht.2.le⟩] at he
    convert! he using 1
  have h := radialDirichletKernel_poisson R g hg r hr.1.ne'
  rw [he.deriv_eq,he.deriv.deriv_eq]
  change -deriv (deriv (radialDirichletKernel R g)) r-
    11/r*deriv (radialDirichletKernel R g) r-(1/2 : ℝ)*u r=f r
  dsimp only [g] at h
  linarith

theorem hasDerivAt_radialResolvent_zero (R : ℝ) (hR : 0 < R) (f u : ℝ →ᵇ ℝ)
    (hu : u=radialGreenOperator R hR.le f+(1/2 : ℝ) • radialGreenOperator R hR.le u) :
    HasDerivAt (u : ℝ → ℝ) 0 0 := by
  let g : ℝ → ℝ := fun t => f t+(1/2 : ℝ)*u t
  have hg : Continuous g := f.continuous.add (continuous_const.mul u.continuous)
  have hzero : u 0=radialDirichletKernel R g 0 := by
    have he := radialResolvent_pointwise R hR.le f u hu 0
    rw [radialClamp_eq R 0 ⟨le_rfl,hR.le⟩] at he
    convert! he using 1
  have hl : HasDerivWithinAt (u : ℝ → ℝ) 0 (Iic 0) 0 := by
    apply (hasDerivAt_const (0 : ℝ) (u 0)).hasDerivWithinAt.congr
    · intro t ht
      rw [hzero,radialResolvent_pointwise R hR.le f u hu t]
      congr 1
      exact max_eq_left (min_le_right R t |>.trans ht)
    · rfl
  have hr : HasDerivWithinAt (u : ℝ → ℝ) 0 (Ici 0) 0 := by
    have hd := (hasDerivAt_radialDirichletKernel R g hg 0).hasDerivWithinAt (s := Ici 0)
    simp only [neg_zero,zero_mul] at hd
    apply hd.congr_of_eventuallyEq _ hzero
    have hRnh : Iio R ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hR
    have hRwithin : ∀ᶠ t in 𝓝[Ici 0] (0 : ℝ), t < R :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hRnh
    filter_upwards [self_mem_nhdsWithin, hRwithin] with t ht htR
    have he := radialResolvent_pointwise R hR.le f u hu t
    rw [radialClamp_eq R t ⟨ht,htR.le⟩] at he
    convert! he using 1
  have h := hl.union hr
  rw [Iic_union_Ici] at h
  exact h.hasDerivAt (by simp)

theorem exists_positive_radial_resolvent (R : ℝ) (hR : 0 < R) (hR2 : R^2 ≤ 11)
    (f : ℝ →ᵇ ℝ) :
    ∃ u : ℝ →ᵇ ℝ, u R=0 ∧ HasDerivAt (u : ℝ → ℝ) 0 0 ∧
      (∀ r ∈ Ioo 0 R, -deriv (deriv u) r-11/r*deriv u r-(1/2 : ℝ)*u r=f r) ∧
      ‖u‖ ≤ (22/37 : ℝ)*‖f‖ ∧
      ((∀ r ∈ Icc 0 R, 0 ≤ f r) → ∀ r, 0 ≤ u r) := by
  obtain ⟨u,hu,hn,hpos⟩ := exists_radialGreenResolvent R hR.le hR2 f
  exact ⟨u,radialResolvent_boundary R hR.le f u hu,
    hasDerivAt_radialResolvent_zero R hR f u hu,
    fun r hr => radialResolvent_poisson R hR.le f u hu r hr,hn,hpos⟩

end DefocusingNLS

end OAI
