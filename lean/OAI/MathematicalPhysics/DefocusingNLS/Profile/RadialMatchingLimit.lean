import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchingMap

namespace OAI

/-! Uniform nonlinear matching and existence of matching parameters at every large power. -/

open Filter
namespace DefocusingNLS
open ProfileCertificate

private theorem radial_uniform_pair {K E F : Type*} [MetricSpace E] [MetricSpace F]
    (f : ℕ → K → E) (g : K → E) (h : ℕ → K → F) (j : K → F)
    (hf : TendstoUniformly f g atTop) (hh : TendstoUniformly h j atTop) :
    TendstoUniformly (fun n x => (f n x,h n x)) (fun x => (g x,j x)) atTop := by
  rw [Metric.tendstoUniformly_iff] at hf hh ⊢
  intro ε hε
  filter_upwards [hf ε hε,hh ε hε] with n hn hj x
  change max (dist (g x) (f n x)) (dist (j x) (h n x)) < ε
  exact max_lt (hn x) (hj x)

theorem radialMatchingMap_continuous : ∀ᶠ n in atTop, Continuous (radialMatchingMap n) := by
  have hs : Tendsto (fun n : ℕ => n+radialInnerShootingThreshold) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n _) tendsto_id
  filter_upwards [hs.eventually radialShootingExterior_continuous,
    hs.eventually radialShootingExterior_exists] with n hE hX
  apply continuous_iff_continuousAt.mpr
  intro z
  have hI := (continuous_radialShootingInnerBoundary n).comp continuous_profileMatchingParameter
  have hZE : (radialShootingExteriorJet (n+radialInnerShootingThreshold) z).1 ≠ 0 :=
    ((radialExteriorCanonical_spec (hX z)).2.2 (Real.log innerBoundaryRadius) le_rfl).1
  exact (continuousAt_radialMatchingTransform z _ _ _
    (radialShootingInnerBoundary_ne_zero n (profileMatchingParameter z)) hZE).comp
      (f := fun z => (z,1/((n+radialInnerShootingThreshold : ℕ) : ℝ),
        radialShootingInnerBoundary n (profileMatchingParameter z),
        radialShootingExteriorJet (n+radialInnerShootingThreshold) z)) (x := z)
      (continuous_id.prodMk (continuous_const.prodMk (hI.prodMk hE))).continuousAt

theorem radialMatchingMap_limit :
    TendstoUniformly radialMatchingMap
      (fun z => (z.val.1,diskProfile (profileMatchingParameter z))) atTop := by
  let I₀ := fun z : ProfileMatchingBall => radialFreeInnerJet (profileMatchingParameter z) innerBoundaryRadius
  let E₀ := fun z : ProfileMatchingBall => radialFreeSlowJet (radialShootingQ z) (radialShootingM z)
    (Real.log innerBoundaryRadius)
  have hs : Tendsto (fun n : ℕ => n+radialInnerShootingThreshold) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n _) tendsto_id
  have hε : TendstoUniformly
      (fun n (_ : ProfileMatchingBall) => 1/((n+radialInnerShootingThreshold : ℕ) : ℝ))
      (fun _ => (0 : ℝ)) atTop := by
    rw [Metric.tendstoUniformly_iff]
    have ht := (tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1/(n : ℝ)) atTop (nhds 0)).comp hs
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.mp ht) ε hε] with n hn z
    simpa only [Function.comp_def,dist_comm] using hn
  have hI : TendstoUniformly (fun n z => radialShootingInnerBoundary n (profileMatchingParameter z)) I₀ atTop :=
    radialShootingInner_uniform_limit.comp profileMatchingParameter
  have hE : TendstoUniformly (fun n => radialShootingExteriorJet (n+radialInnerShootingThreshold)) E₀ atTop :=
    fun u hu => hs.eventually (radialShootingExterior_limit u hu)
  have hdata := radial_uniform_pair _ _ _ _ hε (radial_uniform_pair _ _ _ _ hI hE)
  have hg : Continuous (fun z : ProfileMatchingBall => ((0 : ℝ),I₀ z,E₀ z)) :=
    continuous_const.prodMk
      ((continuous_radialFreeInner_boundary.comp continuous_profileMatchingParameter).prodMk
        continuous_radialShootingFreeJet)
  have hconv := radial_compact_transform_limit _ _ hg hdata
    (fun t : ProfileMatchingBall × ℝ × (ℂ × ℂ) × (ℂ × ℂ) =>
      radialMatchingTransform t.1 t.2.1 t.2.2.1 t.2.2.2)
    (fun z => continuousAt_radialMatchingTransform z 0 (I₀ z) (E₀ z)
      (radialFreeInner_boundary_ne_zero (profileMatchingParameter z)) (radialShootingFreeJet_ne_zero z))
  simpa only [I₀,E₀,radialMatchingMap,radialMatchingTransform_free] using! hconv

theorem exists_radialMatchingMap_zero :
    ∀ᶠ n in atTop, ∃ z : ProfileMatchingBall, radialMatchingMap n z=0 :=
  zero_of_profile_product_limit radialMatchingMap radialMatchingMap_continuous radialMatchingMap_limit

end DefocusingNLS

end OAI
