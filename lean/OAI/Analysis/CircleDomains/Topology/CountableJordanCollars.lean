import OAI.Analysis.CircleDomains.Selection.CountableLocalFamily
import OAI.Analysis.CircleDomains.Topology.QuotientCollarJordan
import OAI.Analysis.CircleDomains.Modulus.WeightedCollarNeighborhoods

namespace OAI

/-! A single countable family of genuine Jordan collars is a neighborhood
basis at every finite dust point. Boundaries lie in the quotient domain. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

def quotientJordanDisk (K : ℂ ≃ₜ ℂ) : Set Sphere :=
  ((↑) : ℂ → Sphere) '' jordanInterior K

theorem exists_countable_jordan_collars
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G U B E : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hB : IsClosed B) (hTD : IsTotallyDisconnected B) (hBU : Bᶜ ⊆ U)
    (hdisj : Disjoint U B) (hbad : ∀ x ∈ Gᶜ, π x ∈ B)
    (hE : IsClosed E) (hEU : E ⊆ U) (hinf : π OnePoint.infty ∉ B) :
    ∃ C : Set (ℂ ≃ₜ ℂ), C.Countable ∧
      (∀ K ∈ C, frontier (quotientJordanDisk K) ⊆ U ∧
        π OnePoint.infty ∉ closure (quotientJordanDisk K) ∧
        Disjoint E (quotientJordanDisk K)) ∧
      ∀ p ∈ B \ {OnePoint.infty}, ∀ O : Set Sphere, IsOpen O → p ∈ O →
        ∃ K ∈ C, p ∈ quotientJordanDisk K ∧ quotientJordanDisk K ⊆ O := by
  classical
  let Valid (K : ℂ ≃ₜ ℂ) : Prop := frontier (quotientJordanDisk K) ⊆ U ∧
    π OnePoint.infty ∉ closure (quotientJordanDisk K) ∧ Disjoint E (quotientJordanDisk K)
  have hlocal (p : Sphere) (hp : p ∈ B \ {OnePoint.infty})
      (O : Set Sphere) (hO : IsOpen O) (hpO : p ∈ O) :
      ∃ K : {K : ℂ ≃ₜ ℂ // Valid K},
        p ∈ quotientJordanDisk K.val ∧ quotientJordanDisk K.val ⊆ O := by
    have hpE : p ∉ E := fun he => disjoint_left.mp hdisj (hEU he) hp.1
    have hpi : p ≠ π OnePoint.infty := fun he => hinf (he ▸ hp.1)
    let V := O ∩ Eᶜ ∩ {π OnePoint.infty}ᶜ ∩ {OnePoint.infty}ᶜ
    have hV : IsOpen V := ((hO.inter hE.isOpen_compl).inter
      isClosed_singleton.isOpen_compl).inter isClosed_singleton.isOpen_compl
    have hpV : p ∈ V := ⟨⟨⟨hpO, hpE⟩, hpi⟩, hp.2⟩
    obtain ⟨D, hDV, _⟩ := exists_weighted_collar_in_neighborhood hcoarea hsard hsch
      G π hπ hclosed hsurj hr hB hTD hbad hp.1 hpi hV hpV
      (fun _ => 0) measurable_const (by simp)
    have hDo : IsOpen D.region := D.isOpen_region hπ hclosed hsurj hr
    obtain ⟨K, hK⟩ := exists_jordan_quotient_collar hsch G π hπ hclosed hsurj hr
      D.disk (fun z hz => (D.level_good z (D.frontier_level hz)).1)
      (fun hi => (hDV hi).2 rfl)
    have heq : D.region = quotientJordanDisk K := hK
    have hvalid : Valid K := by
      refine ⟨?_, ?_, ?_⟩
      · rw [← heq]
        intro x hx
        obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := D.frontier_region_subset hπ hDo hx
        exact hBU (D.level_good z hz).2
      · rw [← heq]
        exact fun hi => (hDV hi).1.2 rfl
      · apply disjoint_left.mpr
        intro x hxE hxK
        have hxD : x ∈ D.region := heq ▸ hxK
        exact (hDV (subset_closure hxD)).1.1.2 hxE
    refine ⟨⟨K, hvalid⟩, heq ▸ D.point_mem_region hsurj hpi, ?_⟩
    intro x hx
    exact (hDV (subset_closure (heq ▸ hx))).1.1.1
  obtain ⟨C, hC, hc⟩ := exists_countable_local_family (B \ {OnePoint.infty})
    (fun K : {K : ℂ ≃ₜ ℂ // Valid K} => quotientJordanDisk K.val)
    (fun K => OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen K.val)) hlocal
  refine ⟨Subtype.val '' C, hC.image _, ?_, ?_⟩
  · rintro K ⟨k, hk, rfl⟩
    exact k.property
  · intro p hp O hO hpO
    obtain ⟨K, hKC, hpK, hKO⟩ := hc p hp O hO hpO
    exact ⟨K.val, mem_image_of_mem _ hKC, hpK, hKO⟩

end CircleDomainRigidity

end

end OAI
