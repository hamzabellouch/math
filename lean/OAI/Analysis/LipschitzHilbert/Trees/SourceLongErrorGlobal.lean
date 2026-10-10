import OAI.Analysis.LipschitzHilbert.Trees.SourceLongTreeSplit

namespace OAI

/-! The full long selector error, integrated over the same masks as
the frozen term. The estimate is uniform in the finite tree depth. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def longErrorTreeValue (hne : Nonempty P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (Omega : P.DensityWhitneyCell → Set ℝ) :
    ℝ×ℝ → EuclideanSpace ℂ κ :=
  paste (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    (by obtain ⟨q⟩ := hne; exact ⟨q,Finset.mem_univ q⟩)
    (fun q _ => P.length_pos q.1)
    (fun i => (E∩u ⁻¹' Omega i).indicator (P.longErrorLocal c selector u i))

theorem long_error_integrable_bound (hne : Nonempty P.PacketIndex)
    (K B : ℕ) (horder : 107≤P.order) (hcard : ∀ j, (P.labels j).card≤B)
    (a b radius Cb M Lip sigma eta : ℝ)
    (hM : 0≤M) (hLip : 0≤Lip) (hsigma : 0≤sigma) (heta : 0≤eta)
    (hwide : 1≤radius+Cb) (hK : radius+Cb≤(2:ℝ)^K)
    (hX : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (hY : ∀ j l v, |P.actualZ j l v-b|≤P.width)
    (hslope : ∀ j l, |P.rowSlope j l|≤Cb*(P.width/P.length j))
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (hc : ∀ j l v, ‖c j l v‖≤sigma)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hselector : ∀ j l k, Measurable (selector j l k))
    (hbound : ∀ j l k s, ‖selector j l k s‖≤M)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      |s-P.rowSlope j l|≤radius*(P.width/P.length j))
    (hnear : ∀ j l k s, |s|≤P.width/P.length j →
      ‖selector j l k s-selector j l k 0‖≤Lip*(|s|/(P.width/P.length j)))
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (Omega : P.DensityWhitneyCell → Set ℝ) (hOmega : ∀ i, MeasurableSet (Omega i))
    (hEmpty : ∀ i, ¬P.HasLongPacket i → Omega i=∅)
    (hmass : ∀ i n, (volume.prod volume).real
      (partitionCell b P.width (i.val,n)∩(E∩u ⁻¹' Omega i))≤
      32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale i.val.1*P.width) :
    Integrable (P.longErrorTreeValue hne c selector E u Omega) (volume.prod volume) ∧
    (∫ z, ‖P.longErrorTreeValue hne c selector E u Omega z‖ ∂volume.prod volume)≤
      (32^106*((B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4))*
        (32*(2:ℝ)^203*eta))*(9*P.topLength*P.width*transverseTailConstant) := by
  have hD : 0≤(B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg B) P.absoluteConstant_pos.le) hsigma)
      (by linarith)) (pow_nonneg (by norm_num) 53)) (sq_nonneg _)) (by positivity)
  exact P.tree_error_integrable_bound hne (P.longErrorLocal c selector u)
    (fun i => (P.longErrorLocal_measurable c selector hselector u hu i).aestronglyMeasurable)
    a b _ eta hD heta hX
    (P.longErrorLocal_bound K B horder hcard b radius Cb M Lip sigma
      hM hLip hsigma hwide hK hY hslope c hc selector hbound hsupport hnear u)
    E hE u hu Omega hOmega hEmpty hmass

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
