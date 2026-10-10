import OAI.Analysis.LipschitzHilbert.Packets.PacketDataRecenteredBoundedSize
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataModelConfig

namespace OAI

/-! The bounded-input constant is chosen before the packet lattice, its
translation, and its finite collection. Its remaining dependence is explicit. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_uniform_bounded_unsigned_size (cStar cEta CEta cb : ℝ)
    (hcEta : 0<cEta) (hcb : 0≤cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (initial : Finset P.PacketIndex)
      (d : OrdinaryModelConfig P initial),
      d.cStar=cStar → d.cEta=cEta → d.CEta=CEta → d.cb=cb →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ) (G : ℝ),
      0≤G → Measurable g → (∀ z, ‖g z‖≤G) →
    ∀ T : SlopeBox, T.width=P.width → T.length≤d.tau →
      P.unsignedSizeTestEnergy d.w d.cb d.cell d.grid (P.ordinaryCoefficient g) initial T≤
        (1+((3*d.M:ℕ):ℝ)*C*P.referenceEnvelopeConstant^2)*G^2*T.area := by
  obtain ⟨C,hC,hBound⟩ := exists_recentered_bounded_size cStar cEta CEta cb hcEta hcb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P initial d heq₁ heq₂ heq₃ heq₄
  rw [←heq₁,←heq₂,←heq₃,←heq₄] at hBound
  let B := ((3*d.M:ℕ):ℝ)*C*P.referenceEnvelopeConstant^2
  have hB : 0≤B := by dsimp only [B]; positivity
  intro g G hG hg hgG T hwidth htime
  let Q := initial.filter fun q => P.length q.1≤T.length ∧
    (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2) ∧
    T.slope∈scaledAngularCell (d.w/P.topLength) d.grid q.1.val (d.cell q.1 q.2.1) ∧
    d.cb*d.w/P.length q.1≤|T.slope-P.rowSlope q.1 q.2.1|
  have hmem (q : P.PacketIndex) (hq : q∈Q) := Finset.mem_filter.mp hq
  have hX (q : P.PacketIndex) (hq : q∈Q) :
      |P.actualX q.1 q.2.1 q.2.2-T.x|≤T.length := by
    have h := (P.selected_top_centers T (1/2) q hwidth (hmem q hq).2.2.1).1
    nlinarith [T.length_pos]
  have hZ (q : P.PacketIndex) (hq : q∈Q) :
      |P.actualZ q.1 q.2.1 q.2.2-T.slope*P.actualX q.1 q.2.1 q.2.2-
        (T.y-T.slope*T.x)|≤P.width := by
    have h := (P.selected_top_centers T (1/2) q hwidth (hmem q hq).2.2.1).2
    nlinarith [P.width_pos]
  have hcone (q : P.PacketIndex) (hq : q∈Q) :
      d.cb*d.w/P.length q.1≤|P.rowSlope q.1 q.2.1-T.slope| ∧
      |P.rowSlope q.1 q.2.1-T.slope|≤d.w/P.length q.1 := by
    refine ⟨?_,P.selected_top_cone d.w d.hw d.cell d.grid q T (hmem q hq).2.1
      (d.hrow q (hmem q hq).1) (hmem q hq).2.2.2.1⟩
    simpa only [abs_sub_comm] using (hmem q hq).2.2.2.2
  have h := hBound N κ Label Item P d.M Q T.slope T.x (T.y-T.slope*T.x) T.length d.w d.F G
    T.length_pos d.hw d.hW d.hF hG d.hfreq d.hlocal (fun q hq => (hmem q hq).2.1)
    hX hZ hcone (fun q _ k xi eta hn => d.spectrum q.1 q.2.1 q.2.2 k xi eta hn) g hg hgG
  have he : P.unsignedSizeTestEnergy d.w d.cb d.cell d.grid (P.ordinaryCoefficient g) initial T=
      ∑ q∈Q, P.length q.1*P.width*‖P.ordinaryCoefficient g q.1 q.2.1 q.2.2‖^2 := by
    dsimp only [Q,unsignedSizeTestEnergy]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _
    split_ifs <;> ring
  rw [he]
  calc
    _ ≤ B*G^2*T.area := by
      convert h using 1
      dsimp only [B,SlopeBox.area]
      rw [hwidth]
    _ ≤ (1+B)*G^2*T.area := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : B≤1+B) (sq_nonneg G)) T.area_pos.le

end LipschitzHilbert.PacketLatticeData

end

end OAI
