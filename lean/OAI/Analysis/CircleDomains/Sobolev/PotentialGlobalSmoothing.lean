import OAI.Analysis.CircleDomains.Modulus.PotentialWeightedWitness
import OAI.Analysis.CircleDomains.Sobolev.PartitionGradientEnergy

namespace OAI

/-! Positive smoothing of the actual barrier with global finite spherical-density energy. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

theorem potential_positive_partition_smoothing_with_energy
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
    {Ω : TopologicalSpace.Opens EuclideanPlane} {ι : Type*} [Countable ι]
    (ρ : OpenPlanePartition Ω ι) (a b c e : ι → ℝ)
    (hab : ∀j, a j < b j) (hce : ∀j, c j < e j)
    (hrect : ∀j z, z ∈ closedComplexRectangle (a j) (b j) (c j) (e j) →
      (z : Sphere) ∈ d.physicalDomain)
    (hsub : ∀j, tsupport (ρ.weight j) ⊆
      euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j)))
    (hdiam : ∀j x, x ∈ closedComplexRectangle (a j) (b j) (c j) (e j) →
      ∀y ∈ closedComplexRectangle (a j) (b j) (c j) (e j), dist x y ≤ 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀z : ℂ,
      ‖fderiv ℝ (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) z‖ ≤
        C / (1 + ‖z‖ ^ 2))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    let f : EuclideanPlane → ℝ :=
      (fun p : ℝ × ℝ => v ((⟨p.1, p.2⟩ : ℂ) : Sphere)) ∘ euclideanPlaneCoordinates
    let W : ι → Set EuclideanPlane := fun j =>
      euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j))
    ∃w : EuclideanPlane → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) w Ω ∧ (∀x ∈ Ω, w x ∈ Icc 0 1) ∧
      (∀x ∈ Ω, ∀r s : ℝ,
        (∀j, ρ.weight j x ≠ 0 → ∀y ∈ W j, f y ∈ Icc r s) → w x ∈ Icc r s) ∧
      ∀i : Fin 2,
        MemLp (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ∧
        eLpNorm (fun x => (fderiv ℝ w x) (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) ≤
          ε + eLpNorm (fun x : EuclideanPlane => (4 * (9 * C)) *
            ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2))) 2 volume := by
  let f : EuclideanPlane → ℝ :=
    (fun p : ℝ × ℝ => v ((⟨p.1, p.2⟩ : ℂ) : Sphere)) ∘ euclideanPlaneCoordinates
  let W : ι → Set EuclideanPlane := fun j =>
    euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (e j))
  have hW (j : ι) : IsOpen (W j) :=
    (isOpen_Ioo.prod isOpen_Ioo).preimage euclideanPlaneCoordinates.continuous
  have hlocal (j : ι) : ∃H : DeGiorgi.MemW1pWitness 2 f (W j),
      ∀i : Fin 2, ∀ᵐ x ∂volume.restrict (W j), |H.weakGrad x i| ≤ 4 * (9 * C) *
        ((g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2)) :=
    potential_small_rectangle_sobolev_witness d hdisj ν N u hu g hg henergy m hm hpath v hv
      (hab j) (hce j) (hrect j) C hC hderiv (hdiam j)
  choose H hH using hlocal
  have hfunit (j : ι) (x : EuclideanPlane) (hx : x ∈ W j) : f x ∈ Icc 0 1 := by
    have hp : euclideanPlaneCoordinates x ∈ Ioo (a j) (b j) ×ˢ Ioo (c j) (e j) := hx
    have hphys := hrect j _ (mk_mem_closedComplexRectangle
      ⟨hp.1.1.le, hp.1.2.le⟩ ⟨hp.2.1.le, hp.2.2.le⟩)
    change v ((⟨(euclideanPlaneCoordinates x).1,
      (euclideanPlaneCoordinates x).2⟩ : ℂ) : Sphere) ∈ Icc 0 1
    rw [hv _ hphys]
    exact hu _
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ι
  obtain ⟨w, hs, hunit, hinterval, herr⟩ :=
    exists_positive_partition_smoothing ρ W hW hsub f H hfunit δ hδ
  refine ⟨w, hs, hunit, hinterval, ?_⟩
  intro i
  have hdensity := (global_spherical_weighted_density_memLp_euclidean g hg henergy).const_mul
    (4 * (9 * C))
  have hEn := partition_smooth_gradient_energy ρ W (fun j => (hW j).measurableSet) hsub
    (fun j x => (H j).weakGrad x i)
    (fun j => (H j).weakGrad_component_memLp i |>.aestronglyMeasurable)
    (hdensity.restrict Ω) (fun j => hH j i) i ((herr i).trans_lt hsum)
  exact ⟨hEn.1, hEn.2.trans (add_le_add le_rfl
    (eLpNorm_mono_measure _ Measure.restrict_le_self))⟩

end CircleDomainRigidity

end

end OAI
