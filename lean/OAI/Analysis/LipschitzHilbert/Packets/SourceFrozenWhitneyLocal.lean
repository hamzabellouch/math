import OAI.Analysis.LipschitzHilbert.Trees.SourceFiniteLongTree
import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeCellGluing

namespace OAI

/-! The frozen local function on the actual typed Whitney partition,
and transport of the finite long-tree estimate to those indices. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
open SourceWhitney
attribute [local instance] Classical.propDecidable

def frozenWhitneyLocal
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (Omega : P.DensityWhitneyCell → Set ℝ)
    (i : P.DensityWhitneyCell) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  (E∩u ⁻¹' Omega i).indicator
    (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale i.val.1) P.width (u z) c z) z

def extendWhitneyMask (Omega : P.DensityWhitneyCell → Set ℝ) (p : ℤ×ℤ) : Set ℝ :=
  if hp : Whitney (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) p.1 p.2
  then Omega ⟨p,hp⟩ else ∅

@[simp] theorem extendWhitneyMask_val (Omega : P.DensityWhitneyCell → Set ℝ)
    (i : P.DensityWhitneyCell) : P.extendWhitneyMask Omega i.val=Omega i := by
  simp only [extendWhitneyMask,dite_eq_left i.property]

theorem frozenWhitneyLocal_integrable
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (Omega : P.DensityWhitneyCell → Set ℝ) (hOmega : ∀ i, MeasurableSet (Omega i))
    (b : ℝ) (i : P.DensityWhitneyCell) (n : ℤ) :
    IntegrableOn (P.frozenWhitneyLocal c E u Omega i)
      (partitionCell b P.width (i.val,n)) (volume.prod volume) :=
  (P.frozen_cell_integral P.width P.width_pos.le c u hu b (i.val,n)
    (E∩u ⁻¹' Omega i) (hE.inter ((hOmega i).preimage hu))).1

private theorem sum_subtype_product {α β : Type*} [DecidableEq α] {p : α → Prop}
    (S : Finset {a // p a}) (T : Finset β) (f : α×β → ℝ) :
    (∑ j∈S.image Subtype.val×ˢT, f j)=(∑ j∈S×ˢT, f (j.1.val,j.2)) := by
  classical
  rw [Finset.sum_product,Finset.sum_product,Finset.sum_image]
  intro i _ j _ h
  exact Subtype.ext h

theorem finite_frozenWhitney_bound
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (S : Finset P.DensityWhitneyCell) (T : Finset ℤ) (a b eta E0 : ℝ) (hE0 : 0≤E0)
    (hcenter : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (hLong : ∀ i∈S, P.HasLongPacket i)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (Omega : P.DensityWhitneyCell → Set ℝ)
    (hOmega : ∀ i, MeasurableSet (Omega i))
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
    (∑ j∈S×ˢT, ∫ z in partitionCell b P.width (j.1.val,j.2),
      ‖P.frozenWhitneyLocal c E u Omega j.1 z‖ ∂volume.prod volume)^2≤
      (32*(2:ℝ)^203*eta)^2*
        (32^206*(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*1296*E0)*
        (9*P.topLength*P.width*transverseTailConstant) := by
  classical
  let raw := S.image Subtype.val
  let O := P.extendWhitneyMask Omega
  have hW : ∀ p∈raw, Whitney (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) p.1 p.2 := by
    intro p hp
    obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hp
    exact i.property
  have hscale : ∀ p∈raw, DyadicLineGrid.scale p.1≤P.topLength := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact P.long_cell_scale_le_top i (hLong i hi)
  have hO : ∀ p∈raw, MeasurableSet (O p) := by
    intro p hp
    obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hp
    simpa only [O,extendWhitneyMask_val] using hOmega i
  have hm : ∀ p∈raw×ˢT, (volume.prod volume).real
      (partitionCell b P.width p∩(E∩u ⁻¹' O p.1))≤
      32*(2:ℝ)^203*eta*(1+|(p.2:ℝ)|)^203*DyadicLineGrid.scale p.1.1*P.width := by
    intro p hp
    obtain ⟨i,_hi,heq⟩ := Finset.mem_image.mp (Finset.mem_product.mp hp).1
    rcases p with ⟨p,n⟩
    dsimp at heq
    subst p
    simpa only [O,extendWhitneyMask_val] using hmass i n
  have h := P.finite_frozen_long_tree_bound c raw T a b eta E0 hE0 hcenter hW hscale
    E hE u hu O hO hm cStar cEta CEta Cb hcStar hcEta hCEta hCb hspectrum hselector
    Kx Ky hKx hKy hI hEnergy
  rw [sum_subtype_product] at h
  simpa only [O,extendWhitneyMask_val,frozenWhitneyLocal] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
