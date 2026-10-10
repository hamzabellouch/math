import OAI.Analysis.LipschitzHilbert.Geometry.SourceFarGramReduction

namespace OAI

/-! Coordinatewise Gram identities relate the Hilbert-valued coefficient
packets to the original scalar Fourier geometry. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem packetVector_inner_integrable
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (s q : P.PacketIndex) :
    Integrable (fun z => inner ℂ (P.packetVector c s z) (P.packetVector c q z))
      (volume.prod volume) := by
  have hf := P.packetVector_memLp c s
  have hg := P.packetVector_memLp c q
  exact (hf.norm.integrable_mul hg.norm).mono'
    (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => norm_inner_le_norm (𝕜 := ℂ) _ _)

theorem packetVector_gram_eq
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (s q : P.PacketIndex) :
    (∫ z, inner ℂ (P.packetVector c s z) (P.packetVector c q z) ∂volume.prod volume)=
      ∑ k, (star (c s.1 s.2.1 s.2.2 k)*c q.1 q.2.1 q.2.2 k)*
        ∫ z, inner ℂ (P.physicalPacket 0 s.1 s.2.1 s.2.2 k z)
          (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z) ∂volume.prod volume := by
  have he (z : ℝ×ℝ) : inner ℂ (P.packetVector c s z) (P.packetVector c q z)=
      ∑ k, (star (c s.1 s.2.1 s.2.2 k)*c q.1 q.2.1 q.2.2 k)*
        inner ℂ (P.physicalPacket 0 s.1 s.2.1 s.2.2 k z)
          (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro k _
    change inner ℂ (c s.1 s.2.1 s.2.2 k • P.physicalPacket 0 s.1 s.2.1 s.2.2 k z)
      (c q.1 q.2.1 q.2.2 k • P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)=_
    rw [inner_smul_left,inner_smul_right]
    simp only [starRingEnd_apply]
    ring
  have hi (k : κ) : Integrable (fun z => inner ℂ
      (P.physicalPacket 0 s.1 s.2.1 s.2.2 k z)
      (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z)) (volume.prod volume) := by
    have hf := (P.physicalPacket 0 s.1 s.2.1 s.2.2 k).memLp 2 (volume.prod volume)
    have hg := (P.physicalPacket 0 q.1 q.2.1 q.2.2 k).memLp 2 (volume.prod volume)
    exact (hf.norm.integrable_mul hg.norm).mono'
      (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => norm_inner_le_norm (𝕜 := ℂ) _ _)
  simp_rw [he]
  rw [integral_finsetSum _ (fun k _ => (hi k).const_mul _)]
  simp only [integral_const_mul]

theorem packetVector_gram_eq_zero
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (s q : P.PacketIndex)
    (hzero : ∀ k, (∫ z, inner ℂ (P.physicalPacket 0 s.1 s.2.1 s.2.2 k z)
      (P.physicalPacket 0 q.1 q.2.1 q.2.2 k z) ∂volume.prod volume)=0) :
    (∫ z, inner ℂ (P.packetVector c s z) (P.packetVector c q z) ∂volume.prod volume)=0 := by
  rw [P.packetVector_gram_eq]
  simp only [hzero,mul_zero,Finset.sum_const_zero]

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
