import OAI.Analysis.CircleDomains.Sobolev.PotentialRectangleSobolev
import OAI.Analysis.CircleDomains.Transfer.PotentialPrescribedChartBound
import OAI.Analysis.CircleDomains.Probability.GlobalSphericalDensity

namespace OAI

/-! The actual bounded first-arrival potential has a local L² weak gradient
on each physical rectangle. No Sobolev regularity is added as an input. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

theorem potential_rectangle_weighted_weak_gradient
    (d : PathCodeData X Sphere) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (hu : ∀x, u x ∈ Icc 0 1)
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Sphere → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    {a b c e : ℝ} (hab : a < b) (hce : c < e)
    (hrect : ∀z ∈ closedComplexRectangle a b c e, (z : Sphere) ∈ d.physicalDomain)
    (L : ℝ≥0) (hL : LipschitzOnWith L ((↑) : ℂ → Sphere)
      (closedComplexRectangle a b c e))
    (C : ℝ) (hLC : ∀z ∈ closedComplexRectangle a b c e,
      (L : ℝ) ≤ C / (1 + ‖z‖ ^ 2)) :
    let f : ℝ × ℝ → ℝ := fun p => v ((⟨p.1, p.2⟩ : ℂ) : Sphere)
    MemLp f 2 (volume.restrict (Icc a b ×ˢ Icc c e)) ∧
    ∃ (Gx Gy : ℝ × ℝ → ℝ), Measurable Gx ∧ Measurable Gy ∧
      MemLp Gx 2 (volume.restrict (Icc a b ×ˢ Icc c e)) ∧
      MemLp Gy 2 (volume.restrict (Icc a b ×ˢ Icc c e)) ∧
      (∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c e),
        |Gx p| ≤ 4 * C * ((g ((⟨p.1, p.2⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨p.1, p.2⟩ : ℂ)‖ ^ 2)) ∧
        |Gy p| ≤ 4 * C * ((g ((⟨p.1, p.2⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨p.1, p.2⟩ : ℂ)‖ ^ 2))) ∧
      ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo a b ×ˢ Ioo c e →
        (∫p in Icc a b ×ˢ Icc c e, f p * (fderiv ℝ φ p) (1, 0)) =
          -(∫p in Icc a b ×ˢ Icc c e, Gx p * φ p) ∧
        (∫p in Icc a b ×ˢ Icc c e, f p * (fderiv ℝ φ p) (0, 1)) =
          -(∫p in Icc a b ×ˢ Icc c e, Gy p * φ p) := by
  let f : ℝ × ℝ → ℝ := fun p => v ((⟨p.1, p.2⟩ : ℂ) : Sphere)
  let : IsFiniteMeasure ((volume : Measure (ℝ × ℝ)).restrict (Icc a b ×ˢ Icc c e)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Icc a b ×ˢ Icc c e)) := by
    rw [← rectangle_restrict_Ioo_eq_Icc]
    exact potential_rectangle_aestronglyMeasurable d hdisj ν N u g hg henergy m hm hpath
      v hv hab hce hrect
  have hfunit : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c e), f p ∈ Icc 0 1 := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    dsimp [f]
    rw [hv _ (hrect _ (mk_mem_closedComplexRectangle hp.1 hp.2))]
    exact hu _
  have hf₂ : MemLp f 2 (volume.restrict (Icc a b ×ˢ Icc c e)) :=
    memLp_of_bounded hfunit hfmeas 2
  obtain ⟨hacx, hacy⟩ := potential_rectangle_ACL d hdisj ν N u g hg henergy m hm hpath
    v hv hab.le hce.le hrect
  obtain ⟨hbx, hby⟩ := potential_rectangle_derivative_bounds_with_constant
    d hdisj ν N u g hg henergy m hm hpath v hv hab.le hce.le hrect L hL
  let ρ : ℝ × ℝ → ℝ := fun p => 4 * C * ((g ((⟨p.1, p.2⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨p.1, p.2⟩ : ℂ)‖ ^ 2))
  have hρ : Measurable ρ := by
    have hmap : Measurable (fun p : ℝ × ℝ => ((⟨p.1, p.2⟩ : ℂ) : Sphere)) :=
      OnePoint.continuous_coe.measurable.comp Complex.measurableEquivRealProd.symm.measurable
    have hc : Continuous (fun p : ℝ × ℝ => 1 + ‖(⟨p.1, p.2⟩ : ℂ)‖ ^ 2) :=
      continuous_const.add ((Complex.equivRealProdCLM.symm.continuous.norm).pow 2)
    exact measurable_const.mul ((hg.comp hmap).ennreal_toReal.div hc.measurable)
  have hρ₂ : MemLp ρ 2 (volume.restrict (Icc a b ×ˢ Icc c e)) :=
    ((global_spherical_weighted_density_memLp_realProd g hg henergy).const_mul
      (4 * C)).restrict _
  have hb (p : ℝ × ℝ) (hp : p ∈ Icc a b ×ˢ Icc c e) :
      4 * ((L : ℝ) * (g ((⟨p.1, p.2⟩ : ℂ) : Sphere)).toReal) ≤ ρ p := by
    have hh := mul_le_mul_of_nonneg_right
      (hLC _ (mk_mem_closedComplexRectangle hp.1 hp.2))
      (ENNReal.toReal_nonneg (a := g ((⟨p.1, p.2⟩ : ℂ) : Sphere)))
    dsimp [ρ]
    calc
      _ ≤ 4 * (C / (1 + ‖(⟨p.1, p.2⟩ : ℂ)‖ ^ 2) *
          (g ((⟨p.1, p.2⟩ : ℂ) : Sphere)).toReal) :=
        mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  have hbx' : ∀ᵐ y ∂volume.restrict (Icc c e), ∀ᵐ x ∂volume.restrict (Icc a b),
      |deriv (fun t => f (t, y)) x| ≤ ρ (x, y) := by
    filter_upwards [hbx, ae_restrict_mem measurableSet_Icc] with y hy hyI
    filter_upwards [hy, ae_restrict_mem measurableSet_Icc] with x hx hxI
    exact hx.trans (hb (x, y) ⟨hxI, hyI⟩)
  have hby' : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c e),
      |deriv (fun t => f (x, t)) y| ≤ ρ (x, y) := by
    filter_upwards [hby, ae_restrict_mem measurableSet_Icc] with x hx hxI
    filter_upwards [hx, ae_restrict_mem measurableSet_Icc] with y hy hyI
    exact hy.trans (hb (x, y) ⟨hxI, hyI⟩)
  obtain ⟨Gx, Gy, hGx, hGy, hx₂, hy₂, hbound, hweak⟩ :=
    exists_rectangle_weak_gradient hab.le hce.le hf₂ hρ hρ₂ hacx hacy hbx' hby'
  exact ⟨hf₂, Gx, Gy, hGx, hGy, hx₂, hy₂, hbound, hweak⟩

end CircleDomainRigidity

end

end OAI
