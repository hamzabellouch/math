import OAI.MeasureTheory.Falconer.Incidence.RegularCoarsePencils
import OAI.MeasureTheory.Falconer.Estimates.IncidentCoarseRounding

namespace OAI

/-! Actual coarse pencils incident to a cell center, with original fine
incidence weights and a common separated line grid. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem incident_regular_coarse_pencil {δ Δ s K : ℝ}
    (hδ : 0 ≤ δ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1/2) (hδΔ : δ ≤ Δ)
    (hs : 0 ≤ s) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (c : Space 2) (hc0 : |c 0| ≤ 1/4) (hc1 : |c 1| ≤ 1/4)
    (hcell : ∀ x ∈ P, dist x c ≤ Δ)
    (hT : ∀ x ∈ P, (T x).Nonempty ∧
      NormalizedFiniteBallBound δ s K (T x) ∧
      ∀ l ∈ T x, |l 0| ≤ 1/2 ∧ TubeIncident δ x l) :
    let W := ∑ x ∈ P, (T x).card
    let J := Nat.log 2 W+1
    let q := fun l : Space 2 => roundedIncidentLine Δ c (l 0)
    ∃ A ⊆ (P.biUnion T).image q, A.Nonempty ∧ InBoundedLineChart A ∧
      FiniteSeparatedAt Δ A ∧ NormalizedFiniteBallBound Δ s (2*(K*(7:ℝ)^s)*(J:ℝ)) A ∧
      ∀ a ∈ A, TubeIncident Δ c a ∧
        (W:ℝ) ≤ 2*(J:ℝ)*(A.card:ℝ)*(coarsePencilWeight P T q a:ℝ) := by
  let q := fun l : Space 2 => roundedIncidentLine Δ c (l 0)
  have hc : |c 0| ≤ 1 := hc0.trans (by norm_num)
  have hnear : ∀ x ∈ P, ∀ l ∈ T x, dist l (q l) ≤ 6*Δ := by
    intro x hx l hl
    have ht := (hT x hx).2.2 l hl
    exact rounded_incident_near_line hΔ c l hc (moved_point_residual hδ hΔ hδΔ
      x c l (hcell x hx) (ht.1.trans (by norm_num)) ht.2)
  obtain ⟨A,hAV,hA,hreg,hweight⟩ := regular_coarse_pencil_mul hΔ hδΔ hs hK
    (C := 6) (by norm_num) P T hP (fun x hx => (hT x hx).1) q hnear
    (fun x hx => (hT x hx).2.1)
  refine ⟨A,hAV,hA,?_,?_,by simpa only [show (6:ℝ)+1=7 by norm_num] using hreg,?_⟩
  · intro a ha
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp (hAV ha)
    obtain ⟨x,hx,hl⟩ := Finset.mem_biUnion.mp hl
    exact roundedIncidentLine_in_chart hΔ hΔ1 c hc0 hc1 (l 0) ((hT x hx).2.2 l hl).1
  · exact finiteSeparatedAt_subset hAV (roundedIncidentLine_family_separated hΔ c
      (fun l : Space 2 => l 0) (P.biUnion T))
  · intro a ha
    obtain ⟨l,_,he⟩ := Finset.mem_image.mp (hAV ha)
    exact ⟨he ▸ roundedIncidentLine_incident hΔ c (l 0),hweight a ha⟩

end Falconer

end OAI
