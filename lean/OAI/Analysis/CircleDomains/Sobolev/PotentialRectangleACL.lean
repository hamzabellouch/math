import OAI.Analysis.CircleDomains.Sobolev.PotentialLineRegularity
import OAI.Analysis.CircleDomains.Sobolev.LocalDensityIntegrability
import OAI.Analysis.CircleDomains.Sobolev.SphereChartLipschitz

namespace OAI

/-! The actual barrier pullback is absolutely continuous on almost every
horizontal and vertical segment in each compact physical chart rectangle. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

def closedComplexRectangle (a b c e : ℝ) : Set ℂ :=
  Complex.equivRealProdCLM.symm '' (Icc a b ×ˢ Icc c e)

theorem isCompact_closedComplexRectangle (a b c e : ℝ) :
    IsCompact (closedComplexRectangle a b c e) :=
  (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous

theorem mk_mem_closedComplexRectangle {a b c e x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc c e) :
    (⟨x, y⟩ : ℂ) ∈ closedComplexRectangle a b c e :=
  ⟨(x, y), ⟨hx, hy⟩, rfl⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

theorem potential_rectangle_ACL
    (d : PathCodeData X Sphere) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (u : X → ℝ) (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (henergy : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (hpath : ∀Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) →
      Γ.1.val ⊥ ∈ d.quotientDomain → Γ.1.val ⊤ ∈ d.quotientDomain →
      ENNReal.ofReal |u (Γ.1.val ⊤) - u (Γ.1.val ⊥)| ≤ 4 * physicalTollCost d g m Γ.1)
    (v : Sphere → ℝ) (hv : ∀y (hy : y ∈ d.physicalDomain),
      v y = u (d.domainEquiv ⟨y, hy⟩).val)
    {a b c e : ℝ} (hab : a ≤ b) (hce : c ≤ e)
    (hrect : ∀z ∈ closedComplexRectangle a b c e, (z : Sphere) ∈ d.physicalDomain) :
    (∀ᵐ y ∂volume.restrict (Icc c e),
      AbsolutelyContinuousOnInterval (fun x => v ((⟨x, y⟩ : ℂ) : Sphere)) a b) ∧
    (∀ᵐ x ∂volume.restrict (Icc a b),
      AbsolutelyContinuousOnInterval (fun y => v ((⟨x, y⟩ : ℂ) : Sphere)) c e) := by
  let K := closedComplexRectangle a b c e
  have hK : IsCompact K := isCompact_closedComplexRectangle a b c e
  obtain ⟨L, hL⟩ := finite_sphere_chart_lipschitz_on_compact hK
  obtain ⟨hh, hvv⟩ := ae_finite_planar_density_slices g hg henergy hK
  constructor
  · filter_upwards [ae_restrict_of_ae hh, ae_restrict_mem measurableSet_Icc] with y hy hyI
    let φ : ℝ → Sphere := fun x => ((⟨x, y⟩ : ℂ) : Sphere)
    have hφ : Measurable φ := by
      have hc : Continuous (fun t : ℝ => (⟨t, y⟩ : ℂ)) :=
        Complex.equivRealProdCLM.symm.continuous.comp (continuous_id.prodMk continuous_const)
      exact (OnePoint.continuous_coe.comp hc).measurable
    have hLip : LipschitzOnWith L φ (Icc a b) := by
      intro x hx x' hx'
      have h := hL (mk_mem_closedComplexRectangle hx hyI) (mk_mem_closedComplexRectangle hx' hyI)
      simpa only [Complex.edist_of_im_eq (show (⟨x, y⟩ : ℂ).im = (⟨x', y⟩ : ℂ).im from rfl)] using h
    have hfin : (∫⁻x in Icc a b, g (φ x)) < ∞ := by
      have he : (∫⁻x in Icc a b, g (φ x)) =
          ∫⁻x in Icc a b, K.indicator (fun z => g (z : Sphere)) ⟨x, y⟩ := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro x hx
        exact (indicator_of_mem (mk_mem_closedComplexRectangle hx hyI)
          (fun z : ℂ => g (z : Sphere))).symm
      rw [he]
      exact (lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans_lt hy
    exact potential_chart_absolutelyContinuousOnInterval d hdisj ν N u g hg m hm hpath
      v hv φ hφ hab hLip (fun x hx => hrect _ (mk_mem_closedComplexRectangle hx hyI)) hfin
  · filter_upwards [ae_restrict_of_ae hvv, ae_restrict_mem measurableSet_Icc] with x hx hxI
    let φ : ℝ → Sphere := fun y => ((⟨x, y⟩ : ℂ) : Sphere)
    have hφ : Measurable φ := by
      have hc : Continuous (fun t : ℝ => (⟨x, t⟩ : ℂ)) :=
        Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)
      exact (OnePoint.continuous_coe.comp hc).measurable
    have hLip : LipschitzOnWith L φ (Icc c e) := by
      intro y hy y' hy'
      have h := hL (mk_mem_closedComplexRectangle hxI hy) (mk_mem_closedComplexRectangle hxI hy')
      simpa only [Complex.edist_of_re_eq (show (⟨x, y⟩ : ℂ).re = (⟨x, y'⟩ : ℂ).re from rfl)] using h
    have hfin : (∫⁻y in Icc c e, g (φ y)) < ∞ := by
      have he : (∫⁻y in Icc c e, g (φ y)) =
          ∫⁻y in Icc c e, K.indicator (fun z => g (z : Sphere)) ⟨x, y⟩ := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro y hy
        exact (indicator_of_mem (mk_mem_closedComplexRectangle hxI hy)
          (fun z : ℂ => g (z : Sphere))).symm
      rw [he]
      exact (lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)).trans_lt hx
    exact potential_chart_absolutelyContinuousOnInterval d hdisj ν N u g hg m hm hpath
      v hv φ hφ hce hLip (fun y hy => hrect _ (mk_mem_closedComplexRectangle hxI hy)) hfin

end CircleDomainRigidity

end

end OAI
