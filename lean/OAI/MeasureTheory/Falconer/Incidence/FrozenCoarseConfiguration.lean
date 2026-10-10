import OAI.MeasureTheory.Falconer.Incidence.FrozenPacketRegularity

namespace OAI

/-! The packet-size freezing step as an actual retained coarse configuration.
Its point set, pencils, fine-packet band and total fine count are explicit. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem frozen_coarse_configuration {δ s t K m M : ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K) (hm : 0 < m) (hM : 0 < M)
    (P : Finset (Space 2)) (T G : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt δ (T x) ∧
      NormalizedFiniteBallBound δ s K (T x) ∧ ∀ l ∈ T x, TubeIncident δ x l)
    (D : ℕ) (hG : ∀ a ∈ P.biUnion T, (G a).Nonempty ∧ (G a).card ≤ D) :
    let J := Nat.log 2 D+1
    let F := 2*(J:ℝ)*M/m
    ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ F*(R.card:ℝ) ∧
      NormalizedFiniteBallBound δ t (K*F) R ∧
      ∃ U : Space 2 → Finset (Space 2),
        (∀ x ∈ R, U x ⊆ T x ∧ (U x).Nonempty ∧
          m/(2*(J:ℝ)) ≤ ((U x).card:ℝ) ∧ ((U x).card:ℝ) ≤ M ∧
          InBoundedLineChart (U x) ∧ FiniteSeparatedAt δ (U x) ∧
          NormalizedFiniteBallBound δ s (K*F) (U x) ∧ ∀ l ∈ U x, TubeIncident δ x l) ∧
        R.biUnion U ⊆ P.biUnion T ∧
        (∑ a ∈ R.biUnion U, ((G a).card:ℝ)) ≤ ∑ a ∈ P.biUnion T, ((G a).card:ℝ) ∧
        ∃ k : ℕ, ∀ a ∈ R.biUnion U, 2^k ≤ (G a).card ∧ (G a).card < 2^(k+1) := by
  obtain ⟨k,B,hBU,_,hband,R,hRP,hR,hsize,hRball,hU⟩ := freeze_regular_packets
    hδ hK hm hM P T hP hPball hT (fun a => (G a).card) D
    (fun a ha => ⟨(hG a ha).1.card_pos,(hG a ha).2⟩)
  let U := fun x => T x ∩ B
  have hcover : R.biUnion U ⊆ P.biUnion T := by
    intro a ha
    obtain ⟨x,hx,ha⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨x,hRP hx,(Finset.mem_inter.mp ha).1⟩
  refine ⟨R,hRP,hR,hsize,hRball,U,?_,hcover,?_,k,?_⟩
  · intro x hx
    obtain ⟨hne,hlo,hchart,hsep,hball,hinc⟩ := hU x hx
    exact ⟨Finset.inter_subset_left,hne,hlo,
      (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)).trans (hT x (hRP hx)).2.1,
      hchart,hsep,hball,hinc⟩
  · exact Finset.sum_le_sum_of_subset_of_nonneg hcover (fun a _ _ => Nat.cast_nonneg _)
  · intro a ha
    obtain ⟨x,_,ha⟩ := Finset.mem_biUnion.mp ha
    exact hband a (Finset.mem_inter.mp ha).2

end Falconer

end OAI
