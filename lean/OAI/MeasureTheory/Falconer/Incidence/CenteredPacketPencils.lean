import OAI.MeasureTheory.Falconer.Estimates.PacketResidualRows

namespace OAI

/-! Lift projected rows directly from an arbitrary original coarse packet.
Affine centering and dilation preserve the original union cardinality. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem centered_packet_pencil_lift {Δ s K m M c b : ℝ}
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (P S : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hrep : ∀ x ∈ P, ∃ p ∈ S, p 1+c*p 0-b = Δ*x 1 ∧ |p 0-x 0| ≤ Δ)
    (hT : ∀ p ∈ S, FiniteSeparatedAt (Δ^2) (T p) ∧
      NormalizedFiniteBallBound (Δ^2) s K (T p) ∧
      m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      ∀ l ∈ T p, |l 0| ≤ 1 ∧ |l 0+c| ≤ Δ ∧ |l 1-b| ≤ Δ ∧ TubeIncident (Δ^2) p l) :
    ∃ U : Space 2 → Finset (Space 2),
      ((P.biUnion U).card:ℝ) ≤ ((S.biUnion T).card:ℝ) ∧
      ∀ x ∈ P, InBoundedLineChart (U x) ∧ FiniteSeparatedAt Δ (U x) ∧
        NormalizedFiniteBallBound Δ s (K*Δ^s) (U x) ∧
        m ≤ ((U x).card:ℝ) ∧ ((U x).card:ℝ) ≤ M ∧
        ∀ l ∈ U x, TubeIncident (3*Δ) x l := by
  let S' := S.image (packetCenterPoint c b)
  let T' := fun p => (T (packetCenterPoint (-c) (-b) p)).image (packetCenterLine c b)
  have hrep' : ∀ x ∈ P, ∃ p ∈ S', p 1 = Δ*x 1 ∧ |p 0-x 0| ≤ Δ := by
    intro x hx
    obtain ⟨p,hp,h1,h0⟩ := hrep x hx
    exact ⟨packetCenterPoint c b p,Finset.mem_image.mpr ⟨p,hp,rfl⟩,h1,h0⟩
  have hT' : ∀ p ∈ S', FiniteSeparatedAt (Δ^2) (T' p) ∧
      NormalizedFiniteBallBound (Δ^2) s K (T' p) ∧
      m ≤ ((T' p).card:ℝ) ∧ ((T' p).card:ℝ) ≤ M ∧
      ∀ l ∈ T' p, |l 0| ≤ Δ ∧ |l 1| ≤ Δ ∧ |p 1-l 0*p 0-l 1| ≤ 2*Δ^2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hsep,hreg,hlo,hup,hgeom⟩ := hT q hq
    simp only [T',packetCenterPoint_inverse]
    refine ⟨packetCenterLine_separated (T q) hsep,
      packetCenterLine_regular (T q) hreg,?_,?_,?_⟩
    · simpa only [packetCenterLine_card] using hlo
    · simpa only [packetCenterLine_card] using hup
    · intro l hl
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨(hgeom k hk).2.1,(hgeom k hk).2.2.1,
        packetCenter_residual_le (sq_nonneg Δ) q k (hgeom k hk).1 (hgeom k hk).2.2.2⟩
  obtain ⟨U,_,hcard,hU⟩ := packet_row_pencil_lift_residual hΔ hΔ1 P S' T' hrep' hT'
  have hunion : S'.biUnion T' = (S.biUnion T).image (packetCenterLine c b) := by
    simp only [S',T',Finset.image_biUnion,packetCenterPoint_inverse,Finset.biUnion_image]
  rw [hunion,packetCenterLine_card] at hcard
  exact ⟨U,hcard,hU⟩

end Falconer

end OAI
