import OAI.MeasureTheory.Falconer.Estimates.PacketCentering
import OAI.MeasureTheory.Falconer.Incidence.PacketRowPencils

namespace OAI

/-! Raw residual form of the packet row lift. This is stable under the
actual affine centering, whose residual identity is exact. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem packet_raw_common_row {Δ y : ℝ} (hΔ : 0 < Δ)
    (p l : Space 2) (hslope : |l 0| ≤ Δ) (hrow : |p 0-y| ≤ Δ)
    (hres : |p 1-l 0*p 0-l 1| ≤ 2*Δ^2) :
    TubeIncident (3*Δ) (rowPoint y (p 1/Δ)) (packetLineDilate Δ l) := by
  have hprod : |l 0*(p 0-y)| ≤ Δ^2 := by
    rw [abs_mul]
    have hh := mul_le_mul hslope hrow (abs_nonneg _) hΔ.le
    nlinarith only [hh]
  have hnum : |p 1-l 0*y-l 1| ≤ 3*Δ^2 := by
    have he : p 1-l 0*y-l 1 = (p 1-l 0*p 0-l 1)+l 0*(p 0-y) := by ring
    rw [he]
    have hh := (abs_add_le (p 1-l 0*p 0-l 1) (l 0*(p 0-y))).trans (add_le_add hres hprod)
    nlinarith only [hh]
  have he : rowPoint y (p 1/Δ) 1-packetLineDilate Δ l 0*rowPoint y (p 1/Δ) 0-
      packetLineDilate Δ l 1 = (p 1-l 0*y-l 1)/Δ := by
    simp only [rowPoint_zero,rowPoint_one,packetLineDilate_apply]
    ring
  have hden : 1 ≤ Real.sqrt (1+(packetLineDilate Δ l 0)^2) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith only [sq_nonneg (packetLineDilate Δ l 0)]
  have hdiv : |p 1-l 0*y-l 1|/Δ ≤ 3*Δ :=
    (div_le_iff₀ hΔ).2 (by nlinarith only [hnum])
  unfold TubeIncident
  rw [he,abs_div,abs_of_pos hΔ]
  apply (div_le_iff₀ (zero_lt_one.trans_le hden)).2
  exact hdiv.trans (le_mul_of_one_le_right (by positivity) hden)

theorem packet_row_pencil_lift_residual {Δ s K m M : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (P S : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hrep : ∀ x ∈ P, ∃ p ∈ S, p 1 = Δ*x 1 ∧ |p 0-x 0| ≤ Δ)
    (hT : ∀ p ∈ S, FiniteSeparatedAt (Δ^2) (T p) ∧
      NormalizedFiniteBallBound (Δ^2) s K (T p) ∧
      m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      ∀ l ∈ T p, |l 0| ≤ Δ ∧ |l 1| ≤ Δ ∧ |p 1-l 0*p 0-l 1| ≤ 2*Δ^2) :
    ∃ U : Space 2 → Finset (Space 2),
      P.biUnion U ⊆ (S.biUnion T).image (packetLineDilate Δ) ∧
      ((P.biUnion U).card:ℝ) ≤ ((S.biUnion T).card:ℝ) ∧
      ∀ x ∈ P, InBoundedLineChart (U x) ∧ FiniteSeparatedAt Δ (U x) ∧
        NormalizedFiniteBallBound Δ s (K*Δ^s) (U x) ∧
        m ≤ ((U x).card:ℝ) ∧ ((U x).card:ℝ) ≤ M ∧
        ∀ l ∈ U x, TubeIncident (3*Δ) x l := by
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
      ⟨(hgeom l hl).1,(hgeom l hl).2.1⟩),?_,?_,?_,?_,?_⟩
    · simpa only [hscale] using packetLineDilate_separated hΔ (T p) hsep
    · simpa only [hscale] using packetLineDilate_regular (sq_pos_of_pos hΔ)
        hΔ hΔ1 (T p) hreg
    · simpa only [packetLineDilate_card hΔ] using hlo
    · simpa only [packetLineDilate_card hΔ] using hup
    · intro l hl
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
      have hh := packet_raw_common_row hΔ p a (hgeom a ha).1 hp.2.2 (hgeom a ha).2.2
      rwa [hxrow] at hh

end Falconer

end OAI
