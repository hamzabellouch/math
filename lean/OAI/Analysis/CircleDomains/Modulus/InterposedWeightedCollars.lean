import OAI.Analysis.CircleDomains.Modulus.WeightedIntermediateCollar
import OAI.Analysis.CircleDomains.Modulus.WeightedCollarTopology

namespace OAI

/-! Interpose weighted collars between successive pairs of prescribed
collars. All joining levels miss every prescribed boundary. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_interposed_weighted_collars
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hbad : ∀x ∈ Gᶜ, π x ∈ B)
    {p : Sphere} {g₀ : ℂ → ℝ≥0∞} (D : ℕ → WeightedCollar G π B p g₀)
    (hnest : ∀n, closure (D (n+1)).region ⊆ (D n).region)
    (hshrink : ∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (D n).region ⊆ V)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ E : ℕ → WeightedCollar G π B p g,
      closure (E 0).region ⊆ (D 0).region ∧
      (∀n, closure (E (n+1)).region ⊆ (E n).region) ∧
      (∀n, {z | (E (n+1)).function z = (E (n+1)).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (E n).region) ∧
      (∀V ∈ 𝓝 p, ∃k : ℕ, ∀n ≥ k, closure (E n).region ⊆ V) ∧
      (∀n z, (E n).function z = (E n).level → ∀j, π (z : Sphere) ∉ frontier (D j).region) ∧
      (∀n, {z | (E n).function z = (E n).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (D 0).region) := by
  have ha : Antitone (fun n => (D n).region) :=
    antitone_nat_of_succ_le (fun n => subset_closure.trans (hnest n))
  have hq : Continuous (fun z : ℂ => π (z : Sphere)) := hπ.comp OnePoint.continuous_coe
  have hphysical (n : ℕ) : closure (jordanInterior (D (2*n+1)).disk) ⊆
      (fun z : ℂ => π (z : Sphere)) ⁻¹' (D (2*n)).region := by
    intro z hz
    have hm := (image_closure_subset_closure_image hq) ⟨z, hz, rfl⟩
    have heq : (fun z : ℂ => π (z : Sphere)) '' jordanInterior (D (2*n+1)).disk =
        (D (2*n+1)).region := by
      simp only [WeightedCollar.region, image_image]
    rw [heq] at hm
    exact hnest (2*n) hm
  have hex (n : ℕ) := exists_weighted_intermediate_collar hcoarea hsard hsch
    G π hπ hclosed hsurj hr hB hbad (D (2*n+1))
    ((D (2*n)).isOpen_region hπ hclosed hsurj hr) ((D (2*n)).isConnected_compl_region hπ hsurj hr)
    ((D (2*n)).infty_notMem_closure_region hπ hsurj hr)
    (hphysical n) g hg hg2
  choose E hEin hEout hElev using hex
  have hstep (n : ℕ) : (D (2*(n+1))).region ⊆ (E n).region :=
    (ha (by omega : 2*n+1 ≤ 2*(n+1))).trans (subset_closure.trans (hEin n))
  refine ⟨E, hEout 0, fun n => (hEout (n+1)).trans (hstep n), ?_, ?_, ?_, ?_⟩
  · intro n z hz
    exact hstep n (hElev (n+1) hz).1
  · intro V hV
    obtain ⟨k, hk⟩ := hshrink V hV
    refine ⟨k, fun n hn => (hEout n).trans ?_⟩
    exact (subset_closure.trans (hk (2*n) (by omega)))
  · intro n z hz j hj
    have hloc := hElev n hz
    by_cases hle : j ≤ 2*n
    · have hm := ha hle hloc.1
      have ho := (D j).isOpen_region hπ hclosed hsurj hr
      exact (ho.frontier_eq ▸ hj).2 hm
    · have hle' : 2*n+1 ≤ j := by omega
      exact hloc.2 (closure_mono (ha hle') (frontier_subset_closure hj))

  · intro n z hz
    exact ha (Nat.zero_le _) (hElev n hz).1

end CircleDomainRigidity

end

end OAI
