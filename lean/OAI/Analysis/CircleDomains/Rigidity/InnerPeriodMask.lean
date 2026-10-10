import OAI.Analysis.CircleDomains.Rigidity.InwardMaskSelection
import OAI.Analysis.CircleDomains.Topology.QuotientDiskTopology
import OAI.Analysis.CircleDomains.Rigidity.AssembledMaskedModel

namespace OAI

/-! An integration curve strictly inside the outer collar admits an enclosing closed
period mask still strictly inside that collar. Thus the centered disk coordinate is
needed only on its genuine open disk, while the integration curve lies in the interior
of the physical mask. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem RegularJordanInwardCollar.exists_inner_period_mask
    {G U : Set Sphere} (hG : IsOpen G) (π : Sphere → Sphere)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨
      (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hPU : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H)
    (hboundary : ∀ z ∈ frontier (jordanInterior H), (z : Sphere) ∈ G)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ jordanInterior H) :
    ∃ M : Set Sphere, IsClosed M ∧ frontier M ⊆ U ∧
      π OnePoint.infty ∉ M ∧ M ⊆ π '' (((↑) : ℂ → Sphere) '' jordanInterior H) ∧
      realChartDomain (((↑) : ℂ → Sphere) '' K) ⊆ interior (physicalMask π M) := by
  obtain ⟨t, ht, htw, hKt, hin, hbd, _⟩ := C.select_inner hK hKH
    (hG.preimage OnePoint.continuous_coe) hboundary (by norm_num : (0 : ℝ) < 1)
  let V := π '' (((↑) : ℂ → Sphere) '' jordanInterior (C.disk t))
  have hbdG : ∀ z ∈ frontier (jordanInterior (C.disk t)), (z : Sphere) ∈ G := hbd
  have hVo : IsOpen V := isOpen_image_jordanInterior_of_component_collapse G π hπ hclosed
    hsurj hr (C.disk t) hbdG
  have hsat := preimage_image_jordanInterior_of_component_collapse G π hsurj hr (C.disk t) hbdG
  have hfront : frontier V = π '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (C.disk t))) := by
    change frontier (π '' (((↑) : ℂ → Sphere) '' jordanInterior (C.disk t))) = _
    rw [frontier_image_of_saturated_open π hπ
      (((↑) : ℂ → Sphere) '' jordanInterior (C.disk t))
      (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen _)) hVo
      (hclosed _ isClosed_closure) hsat, frontier_sphere_image_jordanInterior]
  refine ⟨closure V, isClosed_closure, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxV := frontier_closure_subset hx
    rw [hfront] at hxV
    obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hxV
    exact hPU z (hbdG z hz)
  · exact infty_notMem_closure_image_jordanInterior G π hπ hclosed hsurj hr (C.disk t) hbdG
  · change closure (π '' (((↑) : ℂ → Sphere) '' jordanInterior (C.disk t))) ⊆ _
    rw [closure_image_jordanInterior π hπ hclosed]
    exact image_mono (image_mono hin)
  · have hopen : IsOpen (realChartDomain (π ⁻¹' V)) :=
      isOpen_realChartDomain (hVo.preimage hπ)
    have hsub : realChartDomain (π ⁻¹' V) ⊆ physicalMask π (closure V) :=
      preimage_mono (preimage_mono subset_closure)
    intro x hx
    apply (hopen.subset_interior_iff.mpr hsub)
    change π ((Complex.equivRealProdCLM.symm x : ℂ) : Sphere) ∈ V
    change (Complex.equivRealProdCLM.symm x : Sphere) ∈ ((↑) : ℂ → Sphere) '' K at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have heq : z = Complex.equivRealProdCLM.symm x := OnePoint.coe_injective hzx
    exact ⟨(z : Sphere), ⟨z, hKt hz, rfl⟩, by rw [heq]⟩

end CircleDomainRigidity

end

end OAI
