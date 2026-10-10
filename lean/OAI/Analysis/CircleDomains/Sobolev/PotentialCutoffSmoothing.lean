import OAI.Analysis.CircleDomains.Sobolev.PotentialSobolevWitness
import OAI.Analysis.CircleDomains.Sobolev.CompactSobolevCutoff

namespace OAI

/-! Positive smooth approximation of compactly localized pieces of the
actual barrier, with convergence of both weak gradient components. -/

open Set Function Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [MeasurableSpace C(PathTime, X)]

theorem potential_cutoff_positive_approx
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
    (η : EuclideanPlane → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hsη : HasCompactSupport η) (hηunit : ∀x, η x ∈ Icc 0 1)
    (hηsub : tsupport η ⊆ euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c e)) :
    let f : EuclideanPlane → ℝ :=
      (fun p : ℝ × ℝ => v ((⟨p.1, p.2⟩ : ℂ) : Sphere)) ∘ euclideanPlaneCoordinates
    ∃ hw : DeGiorgi.MemW1pWitness 2 (fun x => η x * f x) univ,
      ∃ φ : ℕ → EuclideanPlane → ℝ,
        (∀n, ContDiff ℝ (⊤ : ℕ∞) (φ n) ∧ HasCompactSupport (φ n) ∧
          tsupport (φ n) ⊆ euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c e) ∧
          ∀x, φ n x ∈ Icc 0 1) ∧
        Tendsto (fun n => eLpNorm (fun x => φ n x - η x * f x) 2 volume) atTop (𝓝 0) ∧
        ∀i : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
          (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) 2 volume)
          atTop (𝓝 0) := by
  let f : EuclideanPlane → ℝ :=
    (fun p : ℝ × ℝ => v ((⟨p.1, p.2⟩ : ℂ) : Sphere)) ∘ euclideanPlaneCoordinates
  let Ω := euclideanPlaneCoordinates ⁻¹' (Ioo a b ×ˢ Ioo c e)
  have hΩ : IsOpen Ω := (isOpen_Ioo.prod isOpen_Ioo).preimage euclideanPlaneCoordinates.continuous
  have hSob : DeGiorgi.MemW1p 2 f Ω :=
    potential_rectangle_memW1p d hdisj ν N u hu g hg henergy m hm hpath v hv hab hce hrect
  obtain ⟨hw⟩ := exists_global_compact_cutoff_witness hΩ hSob hη hsη hηsub
  have huf : ∀x ∈ Ω, f x ∈ Icc 0 1 := by
    intro x hx
    have hp : euclideanPlaneCoordinates x ∈ Ioo a b ×ˢ Ioo c e := hx
    have hphys := hrect _ (mk_mem_closedComplexRectangle
      ⟨hp.1.1.le, hp.1.2.le⟩ ⟨hp.2.1.le, hp.2.2.le⟩)
    change v ((⟨(euclideanPlaneCoordinates x).1,
      (euclideanPlaneCoordinates x).2⟩ : ℂ) : Sphere) ∈ Icc 0 1
    rw [hv _ hphys]
    exact hu _
  have hunit : ∀x, η x * f x ∈ Icc 0 1 := compact_cutoff_mem_Icc huf hηunit hηsub
  refine ⟨hw, ?_⟩
  exact exists_positive_smooth_compact_approx hw hsη.mul_right hunit hΩ
    (tsupport_mul_subset_left.trans hηsub)

end CircleDomainRigidity

end

end OAI
