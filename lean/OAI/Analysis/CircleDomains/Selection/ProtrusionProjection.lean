import OAI.Analysis.CircleDomains.Selection.ProtrusionGeometry
import OAI.Analysis.CircleDomains.Modulus.RotatedLocalizedPayment

namespace OAI

/-! A nontrivial continuum has positive transverse overlap with any nearby anchor ball after
choosing a suitable direction. -/

open Set Function Filter Metric
open scoped Topology ComplexConjugate

noncomputable section

namespace CircleDomainRigidity

private def unitOfNonzero (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / (‖z‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hz))⟩

private theorem one_add_im_ne_zero (t : ℝ) : (1 + (t : ℂ) * Complex.I : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

private def tiltedUnit (t : ℝ) : Circle :=
  unitOfNonzero (1 + (t : ℂ) * Complex.I) (one_add_im_ne_zero t)

private theorem continuous_tiltedUnit : Continuous (fun t : ℝ => (tiltedUnit t : ℂ)) := by
  change Continuous (fun t : ℝ => (1 + (t : ℂ) * Complex.I) /
    ((‖1 + (t : ℂ) * Complex.I‖ : ℝ) : ℂ))
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    exact_mod_cast norm_ne_zero_iff.mpr (one_add_im_ne_zero t)

private theorem tiltedUnit_zero : (tiltedUnit 0 : ℂ) = 1 := by
  simp [tiltedUnit, unitOfNonzero]

/-- Make the projection of a nonzero displacement nonzero while keeping another displacement's
projection as small as desired. -/
theorem exists_transverse_rotation {v : ℂ} (hv : v ≠ 0) (w : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : Circle, (rotation a v).im ≠ 0 ∧ |(rotation a w).im| < δ := by
  have hbase : ∃ b : Circle, ((b : ℂ) * w).im = 0 := by
    by_cases hw : w = 0
    · exact ⟨1, by simp [hw]⟩
    · refine ⟨unitOfNonzero (conj w) (by
        intro h
        apply hw
        simpa only [map_zero, Complex.conj_conj] using congrArg conj h), ?_⟩
      simp [unitOfNonzero, div_mul_eq_mul_div, Complex.div_im, Complex.mul_im]
      exact Or.inl (by ring)
  obtain ⟨b, hb⟩ := hbase
  let v' := (b : ℂ) * v
  let w' := (b : ℂ) * w
  have hv' : v' ≠ 0 := mul_ne_zero (Circle.coe_ne_zero b) hv
  have hw' : w'.im = 0 := hb
  have hcont : Continuous (fun t : ℝ => |((tiltedUnit t : ℂ) * w').im|) := by
    exact (Complex.continuous_im.comp (continuous_tiltedUnit.mul continuous_const)).abs
  have hsmall : ∀ᶠ t in 𝓝 (0 : ℝ), |((tiltedUnit t : ℂ) * w').im| < δ := by
    apply (isOpen_lt hcont continuous_const).mem_nhds
    change |((tiltedUnit 0 : ℂ) * w').im| < δ
    simpa only [tiltedUnit_zero, one_mul, hw', abs_zero] using hδ
  by_cases him : v'.im = 0
  · have hre : v'.re ≠ 0 := by
      intro h
      apply hv'
      exact Complex.ext (by simpa using h) (by simpa using him)
    obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp hsmall
    let t := ε / 2
    have ht : t ≠ 0 := ne_of_gt (half_pos hε)
    have htm : t ∈ ball (0 : ℝ) ε := by
      simp only [mem_ball, dist_zero_right, Real.norm_eq_abs, t,
        abs_of_pos (half_pos hε)]
      linarith
    refine ⟨tiltedUnit t * b, ?_, ?_⟩
    · change (((tiltedUnit t : ℂ) * (b : ℂ)) * v).im ≠ 0
      rw [mul_assoc]
      change ((tiltedUnit t : ℂ) * v').im ≠ 0
      simp only [tiltedUnit, unitOfNonzero, div_mul_eq_mul_div, Complex.div_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.normSq_ofReal,
        Complex.mul_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
        zero_add, Complex.mul_re, Complex.I_re, Complex.I_im, mul_one, add_zero, him]
      simp only [zero_div, sub_zero]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero ht hre)
        (norm_ne_zero_iff.mpr (one_add_im_ne_zero t)))
        (mul_ne_zero (norm_ne_zero_iff.mpr (one_add_im_ne_zero t))
          (norm_ne_zero_iff.mpr (one_add_im_ne_zero t)))
    · simpa only [rotation_apply, Circle.coe_mul, mul_assoc, w'] using (show |((tiltedUnit t : ℂ) * w').im| < δ from he htm)
  · refine ⟨b, ?_, ?_⟩
    · exact him
    · simpa only [rotation_apply, hb, abs_zero] using hδ

/-- A nontrivial continuum through `x` has a nondegenerate interval of transverse parameters
strictly inside the projection of a prescribed anchor ball. -/
theorem exists_transverse_interval {Q : Set ℂ} (hQ : IsConnected Q) (hnt : Q.Nontrivial)
    {x : ℂ} (hx : x ∈ Q) (c : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (a : Circle) (s t : ℝ), s < t ∧
      Icc s t ⊆ (fun z => (rotation a z).im) '' Q ∩
        Ioo ((rotation a c).im - δ) ((rotation a c).im + δ) := by
  obtain ⟨y, hy, hyx⟩ := hnt.exists_ne x
  obtain ⟨a, hgap, hclose⟩ := exists_transverse_rotation (sub_ne_zero.mpr hyx) (x - c) hδ
  let p : ℂ → ℝ := fun z => (rotation a z).im
  have hp : Continuous p := Complex.continuous_im.comp (rotation a).continuous
  have hpQ := hQ.isPreconnected.image p hp.continuousOn
  have hpx : p x ∈ p '' Q := mem_image_of_mem _ hx
  have hpy : p y ∈ p '' Q := mem_image_of_mem _ hy
  have hne : p y ≠ p x := by
    intro he
    apply hgap
    simpa only [map_sub, Complex.sub_im, sub_eq_zero] using he
  have hxc : p c - δ < p x ∧ p x < p c + δ := by
    change |(rotation a (x - c)).im| < δ at hclose
    rw [map_sub, Complex.sub_im, abs_lt] at hclose
    constructor <;> linarith [hclose.1, hclose.2]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨s, hs, hsx⟩ := exists_between (max_lt hlt hxc.1)
    refine ⟨a, s, p x, hsx, ?_⟩
    intro z hz
    refine ⟨hpQ.Icc_subset hpy hpx ⟨(le_max_left _ _).trans (hs.le.trans hz.1), hz.2⟩, ?_⟩
    exact ⟨lt_of_lt_of_le ((le_max_right _ _).trans_lt hs) hz.1,
      lt_of_le_of_lt hz.2 hxc.2⟩
  · obtain ⟨t, hxt, ht⟩ := exists_between (lt_min hgt hxc.2)
    refine ⟨a, p x, t, hxt, ?_⟩
    intro z hz
    refine ⟨hpQ.Icc_subset hpx hpy ⟨hz.1, hz.2.trans (ht.le.trans (min_le_left _ _))⟩, ?_⟩
    exact ⟨lt_of_lt_of_le hxc.1 hz.1,
      lt_of_le_of_lt hz.2 (ht.trans_le (min_le_right _ _))⟩

end CircleDomainRigidity

end

end OAI
