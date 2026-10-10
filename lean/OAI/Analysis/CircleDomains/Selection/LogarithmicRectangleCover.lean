import OAI.Analysis.CircleDomains.Topology.LogarithmicDiskLift
import OAI.Analysis.CircleDomains.Topology.RectangleNeighborhoods
import OAI.Analysis.CircleDomains.Sobolev.PlanarSliceIntegrals
import OAI.Analysis.CircleDomains.Topology.PhysicalPlaneCoordinates
import OAI.Analysis.CircleDomains.Sobolev.LocalSmoothPartition

namespace OAI

/-! Construct the nested rectangular lift charts and subordinate smooth
partition used to smooth the mean index. The logarithmic lifts come from
the actual covering map, not additional hypotheses. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem exists_logarithmic_rectangle_data
    {D : Set ℂ} (hD : IsOpen D) (w : ℂ → ℂ) (hw : ContinuousOn w D)
    (hw0 : ∀ z ∈ D, w z ≠ 0) (hw1 : ∀ z ∈ D, ‖w z‖ ≤ 1)
    {x : ℂ} (hx : x ∈ D) :
    ∃ a₀ a b b₀ c₀ c d d₀ : ℝ, ∃ Ψ : ℂ → ℂ,
      a₀ < a ∧ a < b ∧ b < b₀ ∧ c₀ < c ∧ c < d ∧ d < d₀ ∧
      x ∈ planarSliceBox (Ioo a b) (Ioo c d) ∧
      planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀) ⊆ D ∧
      ContinuousOn Ψ (planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀)) ∧
      (∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀), 0 ≤ (Ψ z).im) ∧
      ∀ z ∈ planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀), diskRayProjection (Ψ z) = w z := by
  obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.mp hD x hx
  obtain ⟨Ψ, hΨ, hpos, hproj⟩ := exists_logarithmic_disk_lift_ball w hr
    (hw.mono hrD) (fun z hz => hw0 z (hrD hz)) (fun z hz => hw1 z (hrD hz))
  have hO : IsOpen (Complex.equivRealProdCLM '' ball x r) :=
    Complex.equivRealProdCLM.toHomeomorph.isOpenMap _ isOpen_ball
  obtain ⟨a₀, b₀, c₀, d₀, hab, hcd, hp, hrect⟩ :=
    exists_closed_rectangle_inside_open hO (mem_image_of_mem _ (mem_ball_self hr))
  change x.re ∈ Ioo a₀ b₀ ∧ x.im ∈ Ioo c₀ d₀ at hp
  have hrect' : planarSliceBox (Icc a₀ b₀) (Icc c₀ d₀) ⊆ ball x r := by
    intro z hz
    have hz' : Complex.equivRealProdCLM z ∈ Icc a₀ b₀ ×ˢ Icc c₀ d₀ := hz
    obtain ⟨y, hy, hyz⟩ := hrect hz'
    exact Complex.equivRealProdCLM.injective hyz ▸ hy
  refine ⟨a₀, (a₀ + x.re) / 2, (x.re + b₀) / 2, b₀,
    c₀, (c₀ + x.im) / 2, (x.im + d₀) / 2, d₀, Ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hrect'.trans hrD, hΨ.mono hrect', ?_, ?_⟩
  · linarith [hp.1.1]
  · linarith
  · linarith [hp.1.2]
  · linarith [hp.2.1]
  · linarith
  · linarith [hp.2.2]
  · exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  · exact fun z hz => hpos z (hrect' hz)
  · exact fun z hz => hproj z (hrect' hz)

 theorem exists_logarithmic_rectangle_partition
    (D : TopologicalSpace.Opens ℂ) (w : ℂ → ℂ) (hw : ContinuousOn w D)
    (hw0 : ∀ z ∈ D, w z ≠ 0) (hw1 : ∀ z ∈ D, ‖w z‖ ≤ 1) :
    let Ω : TopologicalSpace.Opens EuclideanPlane :=
      ⟨complexPlaneCoordinates ⁻¹' D, D.isOpen.preimage complexPlaneCoordinates.continuous⟩
    ∃ (ι : Type) (_ : Countable ι) (ρ : OpenPlanePartition Ω ι)
      (a₀ a b b₀ c₀ c d d₀ : ι → ℝ) (Ψ : ι → ℂ → ℂ),
      (∀ j, a₀ j < a j ∧ a j < b j ∧ b j < b₀ j ∧
        c₀ j < c j ∧ c j < d j ∧ d j < d₀ j) ∧
      (∀ j, planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j)) ⊆ D) ∧
      (∀ j, ContinuousOn (Ψ j) (planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j)))) ∧
      (∀ j z, z ∈ planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j)) → 0 ≤ (Ψ j z).im) ∧
      (∀ j z, z ∈ planarSliceBox (Icc (a₀ j) (b₀ j)) (Icc (c₀ j) (d₀ j)) →
        diskRayProjection (Ψ j z) = w z) ∧
      ∀ j, tsupport (ρ.weight j) ⊆
        euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (d j)) := by
  let Ω : TopologicalSpace.Opens EuclideanPlane :=
    ⟨complexPlaneCoordinates ⁻¹' D, D.isOpen.preimage complexPlaneCoordinates.continuous⟩
  choose a₀ a b b₀ c₀ c d d₀ Ψ ha hab hb hc hcd hd hp hrect hΨ hpos hproj using
    fun x : Ω => exists_logarithmic_rectangle_data D.isOpen w hw hw0 hw1 x.property
  let V : Ω → Set Ω := fun x => (fun y : Ω => euclideanPlaneCoordinates y) ⁻¹'
    (Ioo (a x) (b x) ×ˢ Ioo (c x) (d x))
  have hV (x : Ω) : V x ∈ 𝓝 x := by
    apply IsOpen.mem_nhds
    · exact (isOpen_Ioo.prod isOpen_Ioo).preimage
        (euclideanPlaneCoordinates.continuous.comp continuous_subtype_val)
    · exact hp x
  obtain ⟨ι, hι, ρ, center, hsub⟩ := exists_openPlanePartition Ω V hV
  refine ⟨ι, hι, ρ, a₀ ∘ center, a ∘ center, b ∘ center, b₀ ∘ center,
    c₀ ∘ center, c ∘ center, d ∘ center, d₀ ∘ center, Ψ ∘ center,
    (fun j => ⟨ha (center j), hab (center j), hb (center j),
      hc (center j), hcd (center j), hd (center j)⟩),
    (fun j => hrect (center j)), (fun j => hΨ (center j)),
    (fun j => hpos (center j)), (fun j => hproj (center j)), ?_⟩
  intro j x hx
  obtain ⟨y, hy, rfl⟩ := hsub j hx
  exact hy

end CircleDomainRigidity

end

end OAI
