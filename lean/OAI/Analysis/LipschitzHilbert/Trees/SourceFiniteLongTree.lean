import OAI.Analysis.LipschitzHilbert.Trees.SourceWeightedTreeMajorant
import OAI.Analysis.LipschitzHilbert.Packets.SourceFrozenDensitySum

namespace OAI

/-! The finite frozen long-tree estimate. The transversely weighted tree
energy is the only analytic estimate remaining at this interface; all
maximal, spectral, partition, mass and summation steps are proved. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem finite_frozen_long_tree_bound
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S : Finset (ℤ×ℤ)) (T : Finset ℤ) (a b eta E0 : ℝ) (hE0 : 0≤E0)
    (hcenter : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (hWhitney : ∀ p∈S, Whitney (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) p.1 p.2)
    (hscale : ∀ p∈S, DyadicLineGrid.scale p.1≤P.topLength)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (Omega : ℤ×ℤ → Set ℝ)
    (hOmega : ∀ p∈S, MeasurableSet (Omega p))
    (hmass : ∀ p∈S×ˢT, (volume.prod volume).real
      (partitionCell b P.width p∩(E∩u ⁻¹' Omega p.1))≤
      32*(2:ℝ)^203*eta*(1+|(p.2:ℝ)|)^203*DyadicLineGrid.scale p.1.1*P.width)
    (cStar cEta CEta Cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hCb : 0≤Cb)
    (hspectrum : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |ξ+P.rowSlope j l*η|≤cStar/P.length j ∧ cEta≤P.width*η ∧ P.width*η≤CEta)
    (hselector : ∀ j l, |P.rowSlope j l|≤Cb*P.width/P.length j)
    (Kx Ky : SchwartzMap ℝ ℂ)
    (hKx : ∀ ξ, |ξ|≤(CEta*Cb+cStar)/(4*Real.pi) → 𝓕 Kx ξ=1)
    (hKy : ∀ η, |η|≤CEta/(4*Real.pi) → 𝓕 Ky η=1)
    (hI : Integrable (fun z : ℝ×ℝ =>
      polynomialWeight b (2*P.width) 103 z.2^2*
        P.physicalTreeMaximal 0 c z^2) (volume.prod volume))
    (hEnergy : (∫ z : ℝ×ℝ,
      polynomialWeight b (2*P.width) 103 z.2^2*
        P.physicalTreeMaximal 0 c z^2 ∂volume.prod volume)≤E0) :
    (∑ p∈S×ˢT, ∫ z in partitionCell b P.width p,
      ‖(E∩u ⁻¹' Omega p.1).indicator
        (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) P.width (u z) c z) z‖
      ∂volume.prod volume)^2≤
      (32*(2:ℝ)^203*eta)^2*
        (32^206*(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*1296*E0)*
        (9*P.topLength*P.width*transverseTailConstant) := by
  let U := P.transverseTreeMajorant b 103 c
  have hUI : Integrable (fun z => U z^2) (volume.prod volume) := by
    simpa only [U,transverseTreeMajorant,mul_pow] using hI
  have hU2 : (∫ z, U z^2 ∂volume.prod volume)≤E0 := by
    simpa only [U,transverseTreeMajorant,mul_pow] using hEnergy
  have hUmem : MemLp U 2 (volume.prod volume) :=
    (memLp_two_iff_integrable_sq
      (P.transverseTreeMajorant_continuous b 103 c).aestronglyMeasurable).mpr hUI
  obtain ⟨B,hB,hBound⟩ := P.transverseTreeMajorant_bounded b 103 c
  have he := P.finite_long_cell_energy c (S×ˢT) b 103
    (fun p hp => hWhitney p.1 (Finset.mem_product.mp hp).1)
    cStar cEta CEta Cb hcStar hcEta hCEta hCb hspectrum hselector Kx Ky hKx hKy
    U (P.transverseTreeMajorant_continuous b 103 c).measurable hUmem B hB
    (P.transverseTreeMajorant_nonneg b 103 c) hBound (fun _ => le_rfl)
  let C := (32:ℝ)^206*(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*1296
  have hC : 0≤C :=
    mul_nonneg (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤32) 206) (sq_nonneg _))
      (by norm_num)
  have he' : (∑ p∈S×ˢT, (1+|(p.2:ℝ)|)^412*(P.longCellSup c b p)^2*
      (DyadicLineGrid.scale p.1.1*P.width))≤C*E0 := by
    have heq : (4*(103:ℕ))=412 := rfl
    have heq' : (2*(103:ℕ))=206 := rfl
    simp only [heq,heq'] at he
    apply he.trans
    simpa only [C,mul_assoc] using mul_le_mul_of_nonneg_left hU2 hC
  exact (P.finite_frozen_density_integral c S T a b eta (C*E0) (mul_nonneg hC hE0)
    hcenter hWhitney hscale E hE u hu Omega hOmega hmass he').2

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
