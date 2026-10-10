import OAI.Analysis.LipschitzHilbert.Trees.SourceDemodulatedCellEnergy
import OAI.Analysis.LipschitzHilbert.Packets.SourceFrozenTreeGlobal

namespace OAI

/-! The frozen long-tree integration keeps angular and spatial widths
separate. Carrier removal supplies uniform reproduction on spatial cells. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem finite_angular_frozen_density_integral
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (angularWidth : ℝ) (hangularWidth : 0≤angularWidth)
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
    (henergy : (∑ p∈S×ˢT, (1+|(p.2:ℝ)|)^412*(P.longCellSup c b p)^2*
      (DyadicLineGrid.scale p.1.1*P.width))≤E0) :
    (∀ p∈S×ˢT, IntegrableOn
      ((E∩u ⁻¹' Omega p.1).indicator
        (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) angularWidth (u z) c z))
      (partitionCell b P.width p) (volume.prod volume)) ∧
    (∑ p∈S×ˢT, ∫ z in partitionCell b P.width p,
      ‖(E∩u ⁻¹' Omega p.1).indicator
        (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) angularWidth (u z) c z) z‖
      ∂volume.prod volume)^2≤
      (32*(2:ℝ)^203*eta)^2*E0*(9*P.topLength*P.width*transverseTailConstant) := by
  let mask := fun p : (ℤ×ℤ)×ℤ => E∩u ⁻¹' Omega p.1
  let m := fun p : (ℤ×ℤ)×ℤ => DyadicLineGrid.scale p.1.1*P.width
  let d := fun p : (ℤ×ℤ)×ℤ => (volume.prod volume).real (partitionCell b P.width p∩mask p)
  let w := fun p : (ℤ×ℤ)×ℤ => 1+|(p.2:ℝ)|
  have hlocal (p : (ℤ×ℤ)×ℤ) (hp : p∈S×ˢT) :=
    P.frozen_cell_integral angularWidth hangularWidth c u hu b p (mask p)
      (hE.inter ((hOmega p.1 (Finset.mem_product.mp hp).1).preimage hu))
  refine ⟨fun p hp => (hlocal p hp).1,?_⟩
  have hsum : (∑ p∈S×ˢT, ∫ z in partitionCell b P.width p,
      ‖(mask p).indicator
        (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) angularWidth (u z) c z) z‖
      ∂volume.prod volume)≤∑ p∈S×ˢT, P.longCellSup c b p*d p :=
    Finset.sum_le_sum (fun p hp => (hlocal p hp).2)
  have hene : (∑ p∈S×ˢT, (P.longCellSup c b p)^2*m p*(w p)^412)≤E0 := by
    convert henergy using 1
    apply Finset.sum_congr rfl
    intro p _
    dsimp [m,w]
    ac_rfl
  have hvol : (∑ p∈S×ˢT, m p/(w p)^6)≤9*P.topLength*P.width*transverseTailConstant :=
    finite_whitney_transverse_budget (Finset.univ : Finset P.PacketIndex)
      (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1) a P.topLength P.width
      P.topLength_pos.le P.width_pos.le (fun q _ => hcenter q) S T hWhitney hscale
  have hb := finite_density_supremum_sum (S×ˢT) (P.longCellSup c b) d m w
    (32*(2:ℝ)^203*eta) E0 (9*P.topLength*P.width*transverseTailConstant)
    (fun p _ => P.longCellSup_nonneg c b p) (fun _ _ => measureReal_nonneg)
    (fun p _ => mul_nonneg (DyadicLineGrid.scale_pos _).le P.width_pos.le)
    (fun p _ => by dsimp [w]; positivity) hE0 (by
      intro p hp
      convert hmass p hp using 1
      dsimp [m,w,d,mask]
      simp only [mul_assoc]) hene hvol
  apply le_trans _ hb
  apply pow_le_pow_left₀ _ hsum 2
  exact Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))


theorem finite_angular_frozen_long_tree_bound
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
    (w cStar CEta Cb Cv : ℝ) (nu : κ → ℝ) (hw : 0<w)
    (hcStar : 0≤cStar) (hCEta : 0≤CEta) (hCb : 0≤Cb)
    (hspectrum : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |ξ+P.rowSlope j l*η|≤cStar/P.length j ∧ |η|≤CEta/w)
    (hselector : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j)
    (hbin : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |η-nu k|≤Cv/P.width)
    (Kx Ky : SchwartzMap ℝ ℂ)
    (hKx : ∀ ξ, |ξ|≤(cStar+Cb*CEta)/(4*Real.pi) → 𝓕 Kx ξ=1)
    (hKy : ∀ η, |η|≤Cv/(4*Real.pi) → 𝓕 Ky η=1)
    (hI : Integrable (fun z : ℝ×ℝ =>
      polynomialWeight b (2*P.width) 103 z.2^2*
        P.physicalTreeMaximal 0 c z^2) (volume.prod volume))
    (hEnergy : (∫ z : ℝ×ℝ,
      polynomialWeight b (2*P.width) 103 z.2^2*
        P.physicalTreeMaximal 0 c z^2 ∂volume.prod volume)≤E0) :
    (∑ p∈S×ˢT, ∫ z in partitionCell b P.width p,
      ‖(E∩u ⁻¹' Omega p.1).indicator
        (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) w (u z) c z) z‖
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
  have he := P.finite_demodulated_long_cell_energy c (S×ˢT) b 103
    (fun p hp => hWhitney p.1 (Finset.mem_product.mp hp).1)
    w cStar CEta Cb Cv nu hw hcStar hCEta hCb hspectrum hselector hbin Kx Ky hKx hKy
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
  exact (P.finite_angular_frozen_density_integral c w hw.le S T a b eta (C*E0) (mul_nonneg hC hE0)
    hcenter hWhitney hscale E hE u hu Omega hOmega hmass he').2


def frozenWhitneyLocalAtWidth (w : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (Omega : P.DensityWhitneyCell → Set ℝ)
    (i : P.DensityWhitneyCell) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  (E∩u ⁻¹' Omega i).indicator
    (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale i.val.1) w (u z) c z) z

theorem frozenWhitneyLocalAtWidth_integrable (w : ℝ) (hw : 0≤w)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (Omega : P.DensityWhitneyCell → Set ℝ) (hOmega : ∀ i, MeasurableSet (Omega i))
    (b : ℝ) (i : P.DensityWhitneyCell) (n : ℤ) :
    IntegrableOn (P.frozenWhitneyLocalAtWidth w c E u Omega i)
      (partitionCell b P.width (i.val,n)) (volume.prod volume) :=
  (P.frozen_cell_integral w hw c u hu b (i.val,n)
    (E∩u ⁻¹' Omega i) (hE.inter ((hOmega i).preimage hu))).1

private theorem angular_sum_subtype_product {α β : Type*} [DecidableEq α] {p : α → Prop}
    (S : Finset {a // p a}) (T : Finset β) (f : α×β → ℝ) :
    (∑ j∈S.image Subtype.val×ˢT, f j)=(∑ j∈S×ˢT, f (j.1.val,j.2)) := by
  classical
  rw [Finset.sum_product,Finset.sum_product,Finset.sum_image]
  intro i _ j _ h
  exact Subtype.ext h

theorem finite_angular_frozenWhitney_bound
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
    (w cStar CEta Cb Cv : ℝ) (nu : κ → ℝ) (hw : 0<w)
    (hcStar : 0≤cStar) (hCEta : 0≤CEta) (hCb : 0≤Cb)
    (hspectrum : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |ξ+P.rowSlope j l*η|≤cStar/P.length j ∧ |η|≤CEta/w)
    (hselector : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j)
    (hbin : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |η-nu k|≤Cv/P.width)
    (Kx Ky : SchwartzMap ℝ ℂ)
    (hKx : ∀ ξ, |ξ|≤(cStar+Cb*CEta)/(4*Real.pi) → 𝓕 Kx ξ=1)
    (hKy : ∀ η, |η|≤Cv/(4*Real.pi) → 𝓕 Ky η=1)
    (hI : Integrable (fun z : ℝ×ℝ =>
      polynomialWeight b (2*P.width) 103 z.2^2*
        P.physicalTreeMaximal 0 c z^2) (volume.prod volume))
    (hEnergy : (∫ z : ℝ×ℝ,
      polynomialWeight b (2*P.width) 103 z.2^2*
        P.physicalTreeMaximal 0 c z^2 ∂volume.prod volume)≤E0) :
    (∑ j∈S×ˢT, ∫ z in partitionCell b P.width (j.1.val,j.2),
      ‖P.frozenWhitneyLocalAtWidth w c E u Omega j.1 z‖ ∂volume.prod volume)^2≤
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
  have h := P.finite_angular_frozen_long_tree_bound c raw T a b eta E0 hE0 hcenter hW hscale
    E hE u hu O hO hm w cStar CEta Cb Cv nu hw hcStar hCEta hCb hspectrum hselector hbin
    Kx Ky hKx hKy hI hEnergy
  rw [angular_sum_subtype_product] at h
  simpa only [O,extendWhitneyMask_val,frozenWhitneyLocalAtWidth] using h


def frozenTreeValueAtWidth (w : ℝ) (hne : Nonempty P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (Omega : P.DensityWhitneyCell → Set ℝ) :
    ℝ×ℝ → EuclideanSpace ℂ κ :=
  paste (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    (by obtain ⟨q⟩ := hne; exact ⟨q,Finset.mem_univ q⟩)
    (fun q _ => P.length_pos q.1) (P.frozenWhitneyLocalAtWidth w c E u Omega)

theorem angular_frozen_tree_integrable_bound (hne : Nonempty P.PacketIndex)
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
    (w cStar CEta Cb Cv : ℝ) (nu : κ → ℝ) (hw : 0<w)
    (hcStar : 0≤cStar) (hCEta : 0≤CEta) (hCb : 0≤Cb)
    (hspectrum : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |ξ+P.rowSlope j l*η|≤cStar/P.length j ∧ |η|≤CEta/w)
    (hselector : ∀ j l, |P.rowSlope j l|≤Cb*w/P.length j)
    (hbin : ∀ j l v k ξ η, planarAngularFourier (P.physicalPacket 0 j l v k) (ξ,η)≠0 →
      |η-nu k|≤Cv/P.width)
    (Kx Ky : SchwartzMap ℝ ℂ)
    (hKx : ∀ ξ, |ξ|≤(cStar+Cb*CEta)/(4*Real.pi) → 𝓕 Kx ξ=1)
    (hKy : ∀ η, |η|≤Cv/(4*Real.pi) → 𝓕 Ky η=1)
    (hI : Integrable (fun z : ℝ×ℝ =>
      polynomialWeight b (2*P.width) 103 z.2^2*
        P.physicalTreeMaximal 0 c z^2) (volume.prod volume))
    (hEnergy : (∫ z : ℝ×ℝ,
      polynomialWeight b (2*P.width) 103 z.2^2*
        P.physicalTreeMaximal 0 c z^2 ∂volume.prod volume)≤E0) :
    Integrable (P.frozenTreeValueAtWidth w hne c E u Omega) (volume.prod volume) ∧
    (∫ z, ‖P.frozenTreeValueAtWidth w hne c E u Omega z‖ ∂volume.prod volume)≤
      Real.sqrt ((32*(2:ℝ)^203*eta)^2*
        (32^206*(147456*schwartzEnvelopeConstant Kx 1*schwartzEnvelopeConstant Ky 1)^2*1296*E0)*
        (9*P.topLength*P.width*transverseTailConstant)) := by
  classical
  let tiles := (Finset.univ : Finset P.PacketIndex)
  let X := fun q : P.PacketIndex => P.actualX q.1 q.2.1 q.2.2
  let ell := fun q : P.PacketIndex => P.length q.1
  let F := P.frozenWhitneyLocalAtWidth w c E u Omega
  let J := fun (i : P.DensityWhitneyCell) (n : ℤ) =>
    ∫ z in partitionCell b P.width (i.val,n), ‖F i z‖ ∂volume.prod volume
  have hzero (i : P.DensityWhitneyCell) (hi : ¬P.HasLongPacket i) (n : ℤ) : J i n=0 := by
    dsimp [J,F,frozenWhitneyLocalAtWidth]
    rw [hEmpty i hi,preimage_empty,inter_empty]
    simp only [indicator_empty,norm_zero,integral_zero]
  apply product_paste_integrable_bound tiles X ell
    (by obtain ⟨q⟩ := hne; exact ⟨q,Finset.mem_univ q⟩)
    (fun q _ => P.length_pos q.1) b P.width P.width_pos F
    (fun i => P.frozenWhitneyLocalAtWidth_integrable w hw.le c E hE u hu Omega hOmega b i.1 i.2)
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
  exact P.finite_angular_frozenWhitney_bound c SL T a b eta E0 hE0 hcenter
    (fun i hi => (Finset.mem_filter.mp hi).2) E hE u hu Omega hOmega hmass
    w cStar CEta Cb Cv nu hw hcStar hCEta hCb hspectrum hselector hbin Kx Ky hKx hKy hI hEnergy


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
