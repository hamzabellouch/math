import OAI.Analysis.LipschitzHilbert.Trees.SourceSelectedPrefix
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledComparableEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceFiberGram
import OAI.Analysis.LipschitzHilbert.Trees.SourceL2Sums
import OAI.Analysis.LipschitzHilbert.Geometry.SourceFarGramReduction

namespace OAI

/-! Comparable-scale Gram control for an arbitrary selected packet
set, using its actual masked coefficients. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable Classical.decEq
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem packet_scale_sum_eq (S : Finset P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (j : Fin N) (z : ℝ×ℝ) :
    (∑ q∈S.filter (fun q => q.1=j), P.packetVector c q z)=
      ∑ l : P.labels j, planarFixedSynthesis (P.onPackets S c j l) (P.physicalPacket 0 j l) z := by
  have he : (∑ q∈S.filter (fun q => q.1=j), P.packetVector c q z)=
      ∑ q : P.PacketIndex, if q.1=j then P.packetVector (P.onPackets S c) q z else 0 := by
    simp_rw [P.packetVector_onPackets]
    calc
      _ = ∑ q : P.PacketIndex, if q∈S.filter (fun q => q.1=j) then P.packetVector c q z else 0 := by
        symm
        rw [←Finset.sum_filter]
        congr 1
        ext q
        simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases hs : q∈S <;> by_cases hj : q.1=j <;> simp only [Finset.mem_filter,hs,hj,
          and_true,and_false,ite_true,ite_false]
  rw [he]
  have hh (i : Fin N) :
      (∑ l : P.labels i, ∑ u, if i=j then
        P.packetVector (P.onPackets S c) ⟨i,⟨l,u⟩⟩ z else 0)=
      if i=j then ∑ l : P.labels i, ∑ u,
        P.packetVector (P.onPackets S c) ⟨i,⟨l,u⟩⟩ z else 0 := by
    by_cases hij : i=j <;> simp only [hij,ite_true,ite_false,Finset.sum_const_zero]
  simp only [Fintype.sum_sigma,hh,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ext k
  simp only [WithLp.ofLp_sum,Finset.sum_apply,packetVector,planarFixedSynthesis]

/-- The L2 packet vector, with its coefficient already included. -/
def packetL2 (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (q : P.PacketIndex) : Lp (EuclideanSpace ℂ κ) 2 ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
  (P.packetVector_memLp c q).toLp (P.packetVector c q)

theorem packetL2_inner (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (q r : P.PacketIndex) : inner ℂ (P.packetL2 c q) (P.packetL2 c r)=
      ∫ z, inner ℂ (P.packetVector c q z) (P.packetVector c r z) ∂volume.prod volume :=
  memLp_inner_integral _ _ _ _ _

theorem selected_comparable_gram_energy
    (S : Finset P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (gap : ℕ) (w cStar cEta CEta : ℝ) (hw : 0<w) (hcEta : 0<cEta)
    (M Q : ℕ) (hQ : 2*cStar/cEta≤Q)
    (hmultiplicity : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (hspectrum : ∀ j l u k xi eta,
      planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) :
    (∑ q∈S, ∑ r∈S, if |(q.1.val:ℤ)-(r.1.val:ℤ)|≤(gap:ℤ) then
      (∫ z, inner ℂ (P.packetVector c q z) (P.packetVector c r z)
        ∂volume.prod volume).re else 0)≤
      ((2*gap+1:ℕ):ℝ)*(((2*Q+1)*M:ℕ):ℝ)*
        ((4*Real.pi)^2*P.profileBound^2*Real.pi^2)*
          ∑ q∈S, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
  let V := fun j : Fin N => ∑ q∈S.filter (fun q => q.1=j), P.packetL2 c q
  have hnear := gram_group_by_level S (fun q => q.1) (P.packetL2 c)
    (fun i j => |(i.val:ℤ)-(j.val:ℤ)|≤(gap:ℤ))
  have hn := comparable_scale_gram_energy V gap
  dsimp only [V] at hn
  rw [hnear] at hn
  simp_rw [P.packetL2_inner] at hn
  have henergy (j : Fin N) : ‖V j‖^2≤
      (((2*Q+1)*M:ℕ):ℝ)*((4*Real.pi)^2*P.profileBound^2*Real.pi^2)*
        ∑ l : P.labels j, ∑ u, ‖P.onPackets S c j l u‖^2*P.length j*P.width := by
    dsimp [V,packetL2]
    rw [finite_L2_sum_norm_sq]
    simp_rw [P.packet_scale_sum_eq S c j]
    exact P.physicalPacket_local_label_scale_energy j (P.onPackets S c j)
      w cStar cEta CEta hw hcEta M Q hQ (hmultiplicity j) (hspectrum j)
  apply hn.trans
  calc
    _ ≤ ((2*gap+1:ℕ):ℝ)*∑ j,
        (((2*Q+1)*M:ℕ):ℝ)*((4*Real.pi)^2*P.profileBound^2*Real.pi^2)*
          ∑ l : P.labels j, ∑ u, ‖P.onPackets S c j l u‖^2*P.length j*P.width :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => henergy j) (Nat.cast_nonneg _)
    _ = _ := by rw [←Finset.mul_sum,P.onPackets_energy_sum]; ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
