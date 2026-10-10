import OAI.Analysis.LipschitzHilbert.Packets.SourceFrozenWhitneyLocal

namespace OAI

/-! Countable integration of the frozen long-tree term. The actual
Whitney and transverse partitions remove all finite-cell cutoffs. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def frozenTreeValue (hne : Nonempty P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (Omega : P.DensityWhitneyCell → Set ℝ) :
    ℝ×ℝ → EuclideanSpace ℂ κ :=
  paste (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    (by obtain ⟨q⟩ := hne; exact ⟨q,Finset.mem_univ q⟩)
    (fun q _ => P.length_pos q.1) (P.frozenWhitneyLocal c E u Omega)

theorem frozen_tree_integrable_bound (hne : Nonempty P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (a b eta E0 : ℝ) (hE0 : 0≤E0)
    (hcenter : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (Omega : P.DensityWhitneyCell → Set ℝ)
    (hOmega : ∀ i, MeasurableSet (Omega i))
    (hEmpty : ∀ i, ¬P.HasLongPacket i → Omega i=∅)
    (hmass : ∀ i n, (volume.prod volume).real
      (partitionCell b P.width (i.val,n)∩(E∩u ⁻¹' Omega i))≤
      32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale i.val.1*P.width)
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
    Integrable (P.frozenTreeValue hne c E u Omega) (volume.prod volume) ∧
    (∫ z, ‖P.frozenTreeValue hne c E u Omega z‖ ∂volume.prod volume)≤
      Real.sqrt ((32*(2:ℝ)^203*eta)^2*
        (32^206*(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*1296*E0)*
        (9*P.topLength*P.width*transverseTailConstant)) := by
  classical
  let tiles := (Finset.univ : Finset P.PacketIndex)
  let X := fun q : P.PacketIndex => P.actualX q.1 q.2.1 q.2.2
  let ell := fun q : P.PacketIndex => P.length q.1
  let F := P.frozenWhitneyLocal c E u Omega
  let J := fun (i : P.DensityWhitneyCell) (n : ℤ) =>
    ∫ z in partitionCell b P.width (i.val,n), ‖F i z‖ ∂volume.prod volume
  have hzero (i : P.DensityWhitneyCell) (hi : ¬P.HasLongPacket i) (n : ℤ) : J i n=0 := by
    dsimp [J,F,frozenWhitneyLocal]
    rw [hEmpty i hi,preimage_empty,inter_empty]
    simp only [indicator_empty,norm_zero,integral_zero]
  apply product_paste_integrable_bound tiles X ell
    (by obtain ⟨q⟩ := hne; exact ⟨q,Finset.mem_univ q⟩)
    (fun q _ => P.length_pos q.1) b P.width P.width_pos F
    (fun i => P.frozenWhitneyLocal_integrable c E hE u hu Omega hOmega b i.1 i.2)
  intro S T
  let SL := S.filter P.HasLongPacket
  have heq : (∑ j∈S×ˢT, J j.1 j.2)=(∑ j∈SL×ˢT, J j.1 j.2) := by
    simp only [Finset.sum_product,SL,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : P.HasLongPacket i
    · simp only [hi,ite_true]
    · simp only [hi,ite_false]
      exact Finset.sum_eq_zero (fun n _ => hzero i hi n)
  change (∑ j∈S×ˢT, J j.1 j.2)≤_
  rw [heq]
  apply Real.le_sqrt_of_sq_le
  exact P.finite_frozenWhitney_bound c SL T a b eta E0 hE0 hcenter
    (fun i hi => (Finset.mem_filter.mp hi).2) E hE u hu Omega hOmega hmass
    cStar cEta CEta Cb hcStar hcEta hCEta hCb hspectrum hselector Kx Ky hKx hKy hI hEnergy

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
