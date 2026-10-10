import OAI.Analysis.LipschitzHilbert.Packets.PacketDataVectorEnvelope
import OAI.Analysis.LipschitzHilbert.Trees.SourceWeightedPairing

namespace OAI

/-! The packed short packets can be paired with a weighted long-tree
maximum. This is the analytic estimate for the distant-scale Gram sum. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem packed_short_packet_pairing_sq
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S : Finset P.PacketIndex) (a b L t sigma K E : ℝ)
    (hL : 0<L)
    (hc : ∀ q∈S, ‖c q.1 q.2.1 q.2.2‖≤sigma)
    (hclose : ∀ q∈S, |(P.rowSlope q.1 q.2.1-t)*P.length q.1/P.width|≤1)
    (hlen : ∀ q∈S, P.length q.1≤L)
    (hcount : ∀ z : ℝ×ℝ, ((S.filter fun q =>
      |z.1-P.actualX q.1 q.2.1 q.2.2|≤P.length q.1 ∧
      |(z.2-P.actualZ q.1 q.2.1 q.2.2)-t*(z.1-P.actualX q.1 q.2.1 q.2.2)|≤P.width).card:ℝ)≤K)
    (U : (ℝ×ℝ) → ℝ) (hUm : Measurable U) (hU : ∀ z, 0≤U z)
    (hUi : Integrable (fun z => (treeProductPolynomial a (b-t*a) L P.width t z*U z)^2)
      (volume.prod volume))
    (hUb : (∫ z, (treeProductPolynomial a (b-t*a) L P.width t z*U z)^2
      ∂volume.prod volume)≤E) :
    Integrable (fun z => (∑ q∈S, ‖P.packetVector c q z‖)*U z) (volume.prod volume) ∧
      (∫ z, (∑ q∈S, ‖P.packetVector c q z‖)*U z ∂volume.prod volume)^2≤
        (4*P.profileBound*sigma)^2*256*(82944*K)^2*1296*Real.pi^2*L*P.width*E := by
  let B := fun z => ∑ q∈S, shearedTileEnvelope (P.actualX q.1 q.2.1 q.2.2)
    (P.actualZ q.1 q.2.1 q.2.2) (P.length q.1) P.width t 2 z
  let V := fun z => ∑ q∈S, ‖P.packetVector c q z‖
  let C := 4*P.profileBound*sigma
  have hBm : Measurable B := by
    apply Finset.measurable_sum
    intro q _
    unfold shearedTileEnvelope
    exact (tileEnvelope_measurable _ _ _ _ _).comp (by fun_prop)
  have hB0 (z) : 0≤B z := Finset.sum_nonneg fun q _ => tileEnvelope_nonneg _ _ _ _ _ _
  have hVm : Measurable V := by
    apply Finset.measurable_sum
    intro q _
    apply Continuous.measurable
    apply Continuous.norm
    unfold packetVector
    apply (PiLp.continuous_toLp 2 _).comp
    exact continuous_pi fun k => continuous_const.mul (P.physicalPacket 0 q.1 q.2.1 q.2.2 k).continuous
  have hV0 (z) : 0≤V z := Finset.sum_nonneg fun q _ => norm_nonneg _
  have hv (z) : V z≤C*B z := by
    dsimp [V,B,C]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun q hq => P.packetVector_reference_envelope c t sigma q
      (hc q hq) (hclose q hq) z
  have hpack := sheared_packed_envelope_energy S
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.actualZ q.1 q.2.1 q.2.2)
    (fun q => P.length q.1) a b L P.width t K hL P.width_pos
    (fun q _ => P.length_pos q.1) hlen hcount
  have hDBm : Measurable (fun z => shearedTopReciprocal a b L P.width t z*B z) := by
    apply Measurable.mul _ hBm
    unfold shearedTopReciprocal
    exact (topReciprocalWeight_measurable _ _ _ _).comp (by fun_prop)
  have hPUm : Measurable (fun z => treeProductPolynomial a (b-t*a) L P.width t z*U z) := by
    apply Measurable.mul _ hUm
    unfold treeProductPolynomial polynomialWeight
    fun_prop
  have hDB : MemLp (fun z => shearedTopReciprocal a b L P.width t z*B z) 2
      (volume.prod volume) := (memLp_two_iff_integrable_sq hDBm.aestronglyMeasurable).mpr hpack.1
  have hPU : MemLp (fun z => treeProductPolynomial a (b-t*a) L P.width t z*U z) 2
      (volume.prod volume) := (memLp_two_iff_integrable_sq hPUm.aestronglyMeasurable).mpr hUi
  obtain ⟨hpairI,hpair⟩ := short_long_weighted_pairing_sq B U a b L P.width t hL P.width_pos
    hBm.aestronglyMeasurable hUm.aestronglyMeasurable hB0 hU hDB hPU
  have hpoint (z) : V z*U z≤C*(B z*U z) := by
    have hh := mul_le_mul_of_nonneg_right (hv z) (hU z)
    simpa only [mul_assoc] using hh
  have hVI : Integrable (fun z => V z*U z) (volume.prod volume) :=
    (hpairI.const_mul C).mono' (hVm.mul hUm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hV0 z) (hU z))]
        exact hpoint z)
  have hInt : (∫ z, V z*U z ∂volume.prod volume)≤C*(∫ z, B z*U z ∂volume.prod volume) := by
    rw [←integral_const_mul]
    exact integral_mono hVI (hpairI.const_mul C) hpoint
  have hSquare := pow_le_pow_left₀ (integral_nonneg fun z => mul_nonneg (hV0 z) (hU z)) hInt 2
  rw [mul_pow] at hSquare
  have hW := P.width_pos
  have hBoth := mul_le_mul hpack.2 hUb (integral_nonneg fun z => sq_nonneg _)
    (by positivity : 0≤(82944*K)^2*1296*Real.pi^2*L*P.width)
  change (∫ z, (shearedTopReciprocal a b L P.width t z*B z)^2 ∂volume.prod volume)*
    (∫ z, (treeProductPolynomial a (b-t*a) L P.width t z*U z)^2 ∂volume.prod volume)≤
      (82944*K)^2*1296*Real.pi^2*L*P.width*E at hBoth
  have h256 := mul_le_mul_of_nonneg_left hBoth (by norm_num : (0:ℝ)≤256)
  have hpairBound : (∫ z, B z*U z ∂volume.prod volume)^2≤
      256*((82944*K)^2*1296*Real.pi^2*L*P.width*E) :=
    hpair.trans (by convert h256 using 1; ring)
  have htotal := hSquare.trans (mul_le_mul_of_nonneg_left hpairBound (sq_nonneg C))
  refine ⟨hVI,?_⟩
  convert htotal using 1
  dsimp [C]
  ring

end LipschitzHilbert.PacketLatticeData

end

end OAI
