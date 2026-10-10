import OAI.Analysis.LipschitzHilbert.Phase.SourceAngularFrozenIntegration
import OAI.Analysis.LipschitzHilbert.Trees.SourceLongErrorGlobal

namespace OAI

/-! The exact short/frozen/error identity with an independent angular
cutoff, and the corresponding integrated selector error. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

def longErrorLocalAtWidth (w : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (i : P.DensityWhitneyCell) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  P.longOriginalLocal c selector u i z-
    P.frozenLongValue 0 (DyadicLineGrid.scale i.val.1) w (u z)
      (P.frozenSelectorCoefficient c selector) z


theorem frozenLongValue_eq_selector_at_width (w r s : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (z : ℝ×ℝ) :
    P.frozenLongValue 0 r w s (P.frozenSelectorCoefficient c selector) z=
      P.physicalTreeSelectorValue 0 (P.longCoefficient r c)
        (fun j l k => if |s-0|≤w/P.length j then selector j l k 0 else 0) z := by
  ext k
  simp only [frozenLongValue,physicalTreeSelectorValue,WithLp.ofLp_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : 32*r<P.length j <;> by_cases hs : |s-0|≤w/P.length j <;>
    simp only [hj,hs,and_true,and_false,ite_true,ite_false,planarFixedSynthesis,
      WithLp.ofLp_toLp,Fintype.sum_sigma,longCoefficient,frozenSelectorCoefficient,
      WithLp.ofLp_zero,Pi.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero]


theorem longErrorLocalAtWidth_measurable (w : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hselector : ∀ j l k, Measurable (selector j l k))
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (i : P.DensityWhitneyCell) :
    Measurable (P.longErrorLocalAtWidth w c selector u i) := by
  exact (P.physicalTreeSelectorValue_measurable
    (P.longCoefficient (DyadicLineGrid.scale i.val.1) c)
    (fun j l k z => selector j l k (u z)) (fun j l k => (hselector j l k).comp hu)).sub
    (P.frozenLongValue_measurable 0 (DyadicLineGrid.scale i.val.1) w
      (P.frozenSelectorCoefficient c selector) u hu)

/-- The dyadic selector-error estimate applies to the exact long
restriction without paying for the number of scales. -/
theorem longErrorLocalAtWidth_bound (w : ℝ) (hw : 0<w) (K B : ℕ) (horder : 107≤P.order)
    (hcard : ∀ j, (P.labels j).card≤B) (b radius Cb M Lip sigma : ℝ)
    (hM : 0≤M) (hLip : 0≤Lip) (hsigma : 0≤sigma)
    (hwide : 1≤radius+Cb) (hK : radius+Cb≤(2:ℝ)^K)
    (hcenter : ∀ j l v, |P.actualZ j l v-b|≤P.width)
    (hslope : ∀ j l, |P.rowSlope j l|≤Cb*(w/P.length j))
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (hc : ∀ j l v, ‖c j l v‖≤sigma)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hbound : ∀ j l k s, ‖selector j l k s‖≤M)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      |s-P.rowSlope j l|≤radius*(w/P.length j))
    (hnear : ∀ j l k s, |s|≤w/P.length j →
      ‖selector j l k s-selector j l k 0‖≤Lip*(|s|/(w/P.length j)))
    (u : ℝ×ℝ → ℝ) (i : P.DensityWhitneyCell) (z : ℝ×ℝ) :
    polynomialWeight b (2*P.width) 53 z.2^2*‖P.longErrorLocalAtWidth w c selector u i z‖≤
      (B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4) := by
  have h := P.physical_tree_freezing_error 53 K B horder hcard w b 0 radius Cb M Lip sigma
    hw hM hLip hsigma hwide hK hcenter hslope
    (P.longCoefficient (DyadicLineGrid.scale i.val.1) c)
    (P.longCoefficient_norm_le _ c sigma hsigma hc) selector hbound
    (by simpa only [zero_add] using hsupport) (by simpa only [sub_zero] using hnear)
    Set.univ (u z) z
  simpa only [longErrorLocalAtWidth,longOriginalLocal,P.frozenLongValue_eq_selector_at_width,
    Set.mem_univ,ite_true,zero_mul,sub_zero] using h


/-- Only the original selector support is used to insert the common mask. -/
theorem longOriginalLocal_mask_at_width (w : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l))
    (Omega : P.DensityWhitneyCell → Set ℝ)
    (hcontains : ∀ i (q : P.PacketIndex), 32*DyadicLineGrid.scale i.val.1<P.length q.1 →
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)⊆Omega i)
    (E : Set (ℝ×ℝ)) (i : P.DensityWhitneyCell) (z : ℝ×ℝ) :
    E.indicator (P.longOriginalLocal c selector u i) z=
      (E∩u ⁻¹' Omega i).indicator (P.longOriginalLocal c selector u i) z := by
  classical
  by_cases hz : z∈E
  · by_cases hu : u z∈Omega i
    · simp only [indicator_of_mem hz,indicator_of_mem (show z∈E∩u ⁻¹' Omega i from ⟨hz,hu⟩)]
    · rw [indicator_of_mem hz,indicator_of_notMem (show z∉E∩u ⁻¹' Omega i from fun h => hu h.2)]
      rw [P.longOriginalLocal_eq_sum]
      apply Finset.sum_eq_zero
      intro q _
      by_cases hq : 32*DyadicLineGrid.scale i.val.1<P.length q.1
      · simp only [ite_eq_left hq]
        have hb (k : κ) : selector q.1 q.2.1 k (u z)=0 := by
          by_contra hk
          exact hu (hcontains i q hq (hsupport q.1 q.2.1 k (u z) hk))
        simp only [ordinaryPacketValue,hb,mul_zero,zero_mul]
        rfl
      · exact ite_eq_right hq
  · rw [indicator_of_notMem hz,indicator_of_notMem (show z∉E∩u ⁻¹' Omega i from fun h => hz h.1)]

def longErrorTreeValueAtWidth (w : ℝ) (hne : Nonempty P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (E : Set (ℝ×ℝ)) (u : ℝ×ℝ → ℝ) (Omega : P.DensityWhitneyCell → Set ℝ) :
    ℝ×ℝ → EuclideanSpace ℂ κ :=
  paste (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    (by obtain ⟨q⟩ := hne; exact ⟨q,Finset.mem_univ q⟩)
    (fun q _ => P.length_pos q.1)
    (fun i => (E∩u ⁻¹' Omega i).indicator (P.longErrorLocalAtWidth w c selector u i))

theorem angular_long_error_integrable_bound (w : ℝ) (hw : 0<w) (hne : Nonempty P.PacketIndex)
    (K B : ℕ) (horder : 107≤P.order) (hcard : ∀ j, (P.labels j).card≤B)
    (a b radius Cb M Lip sigma eta : ℝ)
    (hM : 0≤M) (hLip : 0≤Lip) (hsigma : 0≤sigma) (heta : 0≤eta)
    (hwide : 1≤radius+Cb) (hK : radius+Cb≤(2:ℝ)^K)
    (hX : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (hY : ∀ j l v, |P.actualZ j l v-b|≤P.width)
    (hslope : ∀ j l, |P.rowSlope j l|≤Cb*(w/P.length j))
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (hc : ∀ j l v, ‖c j l v‖≤sigma)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hselector : ∀ j l k, Measurable (selector j l k))
    (hbound : ∀ j l k s, ‖selector j l k s‖≤M)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      |s-P.rowSlope j l|≤radius*(w/P.length j))
    (hnear : ∀ j l k s, |s|≤w/P.length j →
      ‖selector j l k s-selector j l k 0‖≤Lip*(|s|/(w/P.length j)))
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (Omega : P.DensityWhitneyCell → Set ℝ) (hOmega : ∀ i, MeasurableSet (Omega i))
    (hEmpty : ∀ i, ¬P.HasLongPacket i → Omega i=∅)
    (hmass : ∀ i n, (volume.prod volume).real
      (partitionCell b P.width (i.val,n)∩(E∩u ⁻¹' Omega i))≤
      32*(2:ℝ)^203*eta*(1+|(n:ℝ)|)^203*DyadicLineGrid.scale i.val.1*P.width) :
    Integrable (P.longErrorTreeValueAtWidth w hne c selector E u Omega) (volume.prod volume) ∧
    (∫ z, ‖P.longErrorTreeValueAtWidth w hne c selector E u Omega z‖ ∂volume.prod volume)≤
      (32^106*((B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4))*
        (32*(2:ℝ)^203*eta))*(9*P.topLength*P.width*transverseTailConstant) := by
  have hD : 0≤(B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg B) P.absoluteConstant_pos.le) hsigma)
      (by linarith)) (pow_nonneg (by norm_num) 53)) (sq_nonneg _)) (by positivity)
  exact P.tree_error_integrable_bound hne (P.longErrorLocalAtWidth w c selector u)
    (fun i => (P.longErrorLocalAtWidth_measurable w c selector hselector u hu i).aestronglyMeasurable)
    a b _ eta hD heta hX
    (P.longErrorLocalAtWidth_bound w hw K B horder hcard b radius Cb M Lip sigma
      hM hLip hsigma hwide hK hY hslope c hc selector hbound hsupport hnear u)
    E hE u hu Omega hOmega hEmpty hmass

theorem angular_ordinary_tree_split_identity (w : ℝ) (hne : Nonempty P.PacketIndex)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l))
    (Omega : P.DensityWhitneyCell → Set ℝ)
    (hcontains : ∀ i (q : P.PacketIndex), 32*DyadicLineGrid.scale i.val.1<P.length q.1 →
      scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)⊆Omega i)
    (E : Set (ℝ×ℝ)) :
    E.indicator (fun z => P.physicalTreeSelectorValue 0 c (fun j l k => selector j l k (u z)) z)=
      fun z => E.indicator
        (P.shortTreeValue hne 0 32 (fun q => c q.1 q.2.1 q.2.2) selector u) z+
        P.frozenTreeValueAtWidth w hne (P.frozenSelectorCoefficient c selector) E u Omega z+
        P.longErrorTreeValueAtWidth w hne c selector E u Omega z := by
  classical
  funext z
  let i : P.DensityWhitneyCell := indexAt (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    (P.packet_univ_nonempty hne) (fun q _ => P.length_pos q.1) z.1
  have hs := P.ordinaryTreeLocal_split c selector u i z
  have hm := P.longOriginalLocal_mask_at_width w c selector u cell grid hsupport Omega hcontains E i z
  simp only [Set.indicator_apply,shortTreeValue,frozenTreeValueAtWidth,frozenWhitneyLocalAtWidth,
    longErrorTreeValueAtWidth,paste]
  change (if z∈E then P.physicalTreeSelectorValue 0 c (fun j l k => selector j l k (u z)) z else 0)=
    (if z∈E then P.shortLocalValue 0 32 (fun q => c q.1 q.2.1 q.2.2) selector u i z else 0)+
    (if z∈E∩u ⁻¹' Omega i then P.frozenLongValue 0 (DyadicLineGrid.scale i.val.1) w
      (u z) (P.frozenSelectorCoefficient c selector) z else 0)+
    (if z∈E∩u ⁻¹' Omega i then P.longErrorLocalAtWidth w c selector u i z else 0)
  by_cases hz : z∈E
  · by_cases hu : u z∈Omega i
    · have ha : z∈E∩u ⁻¹' Omega i := ⟨hz,hu⟩
      simp only [ite_eq_left hz,ite_eq_left ha,longErrorLocalAtWidth]
      rw [hs]
      abel
    · have ha : z∉E∩u ⁻¹' Omega i := fun h => hu h.2
      simp only [indicator_of_mem hz,indicator_of_notMem ha] at hm
      simp only [ite_eq_left hz,ite_eq_right ha,add_zero]
      rw [hs,hm,add_zero]
  · have ha : z∉E∩u ⁻¹' Omega i := fun h => hz h.1
    simp only [ite_eq_right hz,ite_eq_right ha,zero_add]


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
