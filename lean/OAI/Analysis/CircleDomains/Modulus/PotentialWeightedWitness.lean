import OAI.Analysis.CircleDomains.Sobolev.PotentialWeightedSobolev
import OAI.Analysis.CircleDomains.Sobolev.WeightedSobolevTransport
import OAI.Analysis.CircleDomains.Topology.SphereChartSmallSets

namespace OAI

/-! Actual local Sobolev witnesses with a single decaying global density bound. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

theorem potential_small_rectangle_sobolev_witness
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
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    (hdiam : ∀x ∈ closedComplexRectangle a b c e,
      ∀y ∈ closedComplexRectangle a b c e, dist x y ≤ 1) :
    ∃H : DeGiorgi.MemW1pWitness 2
        ((fun p : ℝ × ℝ => v ((⟨p.1, p.2⟩ : ℂ) : Sphere)) ∘ euclideanPlaneCoordinates)
        (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c e)),
      ∀i : Fin 2, ∀ᵐ x ∂volume.restrict
        (euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c e)),
        |H.weakGrad x i| ≤ 4 * (9 * C) *
          ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2)) := by
  have hconv : Convex ℝ (closedComplexRectangle a b c e) :=
    ((convex_Icc a b).prod (convex_Icc c e)).linear_image
      Complex.equivRealProdCLM.symm.toLinearMap
  have hne : (closedComplexRectangle a b c e).Nonempty :=
    ⟨⟨a, c⟩, mk_mem_closedComplexRectangle ⟨le_rfl, hab.le⟩ ⟨le_rfl, hce.le⟩⟩
  obtain ⟨L, hL, hLC⟩ := finite_sphere_chart_lipschitz_on_small_convex hC hderiv hconv hne hdiam
  obtain ⟨hf, Gx, Gy, _, _, hx, hy, hb, hw⟩ :=
    potential_rectangle_weighted_weak_gradient d hdisj ν N u hu g hg henergy m hm hpath v hv
      hab hce hrect L hL (9 * C) hLC
  obtain ⟨H, hH⟩ := exists_bounded_rectangle_sobolev_witness hf hx hy hb hw
  exact ⟨H, hH⟩

end CircleDomainRigidity

end

end OAI
