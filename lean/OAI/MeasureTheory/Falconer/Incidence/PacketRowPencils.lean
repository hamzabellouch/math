import OAI.MeasureTheory.Falconer.Estimates.TubePacketDilation

namespace OAI

/-! Lift actual projected row points back to their original fine-scale
pencils inside a coarse packet. Dilation preserves each pencil cardinality
and the whole new union is contained in the dilation of the original union. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem packet_row_pencil_lift {Δ s K m M : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (P S : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hrep : ∀ x ∈ P, ∃ p ∈ S, p 1 = Δ*x 1 ∧ |p 0-x 0| ≤ Δ)
    (hT : ∀ p ∈ S, FiniteSeparatedAt (Δ^2) (T p) ∧
      NormalizedFiniteBallBound (Δ^2) s K (T p) ∧
      m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      ∀ l ∈ T p, |l 0| ≤ Δ ∧ |l 1| ≤ Δ ∧ TubeIncident (Δ^2) p l) :
    ∃ U : Space 2 → Finset (Space 2),
      P.biUnion U ⊆ (S.biUnion T).image (packetLineDilate Δ) ∧
      ((P.biUnion U).card:ℝ) ≤ ((S.biUnion T).card:ℝ) ∧
      ∀ x ∈ P, InBoundedLineChart (U x) ∧ FiniteSeparatedAt Δ (U x) ∧
        NormalizedFiniteBallBound Δ s (K*Δ^s) (U x) ∧
        m ≤ ((U x).card:ℝ) ∧ ((U x).card:ℝ) ≤ M ∧
        (∀ l ∈ U x, TubeIncident (3*Δ) x l) ∧
        ∃ p ∈ S, p 1 = Δ*x 1 ∧ |p 0-x 0| ≤ Δ ∧
          U x = (T p).image (packetLineDilate Δ) := by
  let rep : {x // x ∈ P} → Space 2 := fun x => Classical.choose (hrep x.val x.property)
  have hrep' (x : Space 2) (hx : x ∈ P) :
      rep ⟨x,hx⟩ ∈ S ∧ (rep ⟨x,hx⟩) 1 = Δ*x 1 ∧
        |(rep ⟨x,hx⟩) 0-x 0| ≤ Δ := Classical.choose_spec (hrep x hx)
  let U : Space 2 → Finset (Space 2) := fun x =>
    if hx : x ∈ P then (T (rep ⟨x,hx⟩)).image (packetLineDilate Δ) else ∅
  have hU (x : Space 2) (hx : x ∈ P) :
      U x = (T (rep ⟨x,hx⟩)).image (packetLineDilate Δ) := dite_eq_left hx
  have hsub : P.biUnion U ⊆ (S.biUnion T).image (packetLineDilate Δ) := by
    intro l hl
    obtain ⟨x,hx,hl⟩ := Finset.mem_biUnion.mp hl
    rw [hU x hx] at hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_image.mpr ⟨a,
      Finset.mem_biUnion.mpr ⟨rep ⟨x,hx⟩,(hrep' x hx).1,ha⟩,rfl⟩
  refine ⟨U,hsub,?_,?_⟩
  · have hc := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
    rwa [packetLineDilate_card hΔ] at hc
  · intro x hx
    let p := rep ⟨x,hx⟩
    have hp := hrep' x hx
    obtain ⟨hsep,hreg,hlo,hup,hgeom⟩ := hT p hp.1
    have hscale : Δ^2/Δ = Δ := by field_simp
    have hxrow : rowPoint (x 0) (p 1/Δ) = x := by
      ext i
      fin_cases i
      · rfl
      · change p 1/Δ = x 1
        rw [hp.2.1]
        field_simp
    rw [hU x hx]
    refine ⟨packetLineDilate_chart hΔ (T p) (fun l hl =>
      ⟨(hgeom l hl).1,(hgeom l hl).2.1⟩),?_,?_,?_,?_,?_,p,hp.1,hp.2.1,hp.2.2,rfl⟩
    · simpa only [hscale] using packetLineDilate_separated hΔ (T p) hsep
    · simpa only [hscale] using packetLineDilate_regular (sq_pos_of_pos hΔ)
        hΔ hΔ1 (T p) hreg
    · simpa only [packetLineDilate_card hΔ] using hlo
    · simpa only [packetLineDilate_card hΔ] using hup
    · intro l hl
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
      have hh := packet_common_row_square_scale hΔ hΔ1 p a
        (hgeom a ha).1 hp.2.2 (hgeom a ha).2.2
      rwa [hxrow] at hh

end Falconer

end OAI
