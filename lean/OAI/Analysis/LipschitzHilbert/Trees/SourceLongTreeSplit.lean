import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeSelectorError
import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeErrorIntegral
import OAI.Analysis.LipschitzHilbert.Trees.SourceShortTreeGlobal

namespace OAI

/-! The original long sum, its frozen coefficients, and the literal
selector error. No support property is imposed on the frozen sum. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

def longCoefficient (r : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (j : Fin N) (l : P.labels j) (v : Item j l) : EuclideanSpace ℂ κ :=
  if 32*r<P.length j then c j l v else 0

def frozenSelectorCoefficient
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (j : Fin N) (l : P.labels j) (v : Item j l) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => c j l v k*selector j l k 0)

def longOriginalLocal
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (i : P.DensityWhitneyCell) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  P.physicalTreeSelectorValue 0 (P.longCoefficient (DyadicLineGrid.scale i.val.1) c)
    (fun j l k => selector j l k (u z)) z

def longErrorLocal
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (i : P.DensityWhitneyCell) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  P.longOriginalLocal c selector u i z-
    P.frozenLongValue 0 (DyadicLineGrid.scale i.val.1) P.width (u z)
      (P.frozenSelectorCoefficient c selector) z

theorem longCoefficient_norm_le (r : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (sigma : ℝ) (hsigma : 0≤sigma) (hc : ∀ j l v, ‖c j l v‖≤sigma)
    (j : Fin N) (l : P.labels j) (v : Item j l) :
    ‖P.longCoefficient r c j l v‖≤sigma := by
  by_cases hj : 32*r<P.length j
  · simpa only [longCoefficient,ite_eq_left hj] using hc j l v
  · simpa only [longCoefficient,ite_eq_right hj,norm_zero] using hsigma

theorem frozenLongValue_eq_selector (r s : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (z : ℝ×ℝ) :
    P.frozenLongValue 0 r P.width s (P.frozenSelectorCoefficient c selector) z=
      P.physicalTreeSelectorValue 0 (P.longCoefficient r c)
        (fun j l k => if |s-0|≤P.width/P.length j then selector j l k 0 else 0) z := by
  ext k
  simp only [frozenLongValue,physicalTreeSelectorValue,WithLp.ofLp_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : 32*r<P.length j <;> by_cases hs : |s-0|≤P.width/P.length j <;>
    simp only [hj,hs,and_true,and_false,ite_true,ite_false,planarFixedSynthesis,
      WithLp.ofLp_toLp,Fintype.sum_sigma,longCoefficient,frozenSelectorCoefficient,
      WithLp.ofLp_zero,Pi.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero]

theorem physicalTreeSelectorValue_measurable
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (beta : ∀ j, P.labels j → κ → (ℝ×ℝ) → ℂ)
    (hbeta : ∀ j l k, Measurable (beta j l k)) :
    Measurable (fun z => P.physicalTreeSelectorValue 0 c (fun j l k => beta j l k z) z) := by
  unfold physicalTreeSelectorValue
  apply Finset.measurable_sum
  intro j _
  apply Finset.measurable_sum
  intro l _
  apply Finset.measurable_sum
  intro v _
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_iff.mpr
  intro k
  exact (measurable_const.mul (hbeta j l k)).mul
    (P.physicalPacket 0 j l v k).continuous.measurable

theorem longErrorLocal_measurable
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hselector : ∀ j l k, Measurable (selector j l k))
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (i : P.DensityWhitneyCell) :
    Measurable (P.longErrorLocal c selector u i) := by
  exact (P.physicalTreeSelectorValue_measurable
    (P.longCoefficient (DyadicLineGrid.scale i.val.1) c)
    (fun j l k z => selector j l k (u z)) (fun j l k => (hselector j l k).comp hu)).sub
    (P.frozenLongValue_measurable 0 (DyadicLineGrid.scale i.val.1) P.width
      (P.frozenSelectorCoefficient c selector) u hu)

/-- The dyadic selector-error estimate applies to the exact long
restriction without paying for the number of scales. -/
theorem longErrorLocal_bound (K B : ℕ) (horder : 107≤P.order)
    (hcard : ∀ j, (P.labels j).card≤B) (b radius Cb M Lip sigma : ℝ)
    (hM : 0≤M) (hLip : 0≤Lip) (hsigma : 0≤sigma)
    (hwide : 1≤radius+Cb) (hK : radius+Cb≤(2:ℝ)^K)
    (hcenter : ∀ j l v, |P.actualZ j l v-b|≤P.width)
    (hslope : ∀ j l, |P.rowSlope j l|≤Cb*(P.width/P.length j))
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (hc : ∀ j l v, ‖c j l v‖≤sigma)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hbound : ∀ j l k s, ‖selector j l k s‖≤M)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      |s-P.rowSlope j l|≤radius*(P.width/P.length j))
    (hnear : ∀ j l k s, |s|≤P.width/P.length j →
      ‖selector j l k s-selector j l k 0‖≤Lip*(|s|/(P.width/P.length j)))
    (u : ℝ×ℝ → ℝ) (i : P.DensityWhitneyCell) (z : ℝ×ℝ) :
    polynomialWeight b (2*P.width) 53 z.2^2*‖P.longErrorLocal c selector u i z‖≤
      (B:ℝ)*P.absoluteConstant*sigma*(2*M+Lip)*16^53*(4*Real.pi)^2*((K+1:ℕ)+4) := by
  have h := P.physical_tree_freezing_error 53 K B horder hcard P.width b 0 radius Cb M Lip sigma
    P.width_pos hM hLip hsigma hwide hK hcenter hslope
    (P.longCoefficient (DyadicLineGrid.scale i.val.1) c)
    (P.longCoefficient_norm_le _ c sigma hsigma hc) selector hbound
    (by simpa only [zero_add] using hsupport) (by simpa only [sub_zero] using hnear)
    Set.univ (u z) z
  simpa only [longErrorLocal,longOriginalLocal,P.frozenLongValue_eq_selector,
    Set.mem_univ,ite_true,zero_mul,sub_zero] using h

/-- Coordinate multipliers of norm at most one do not enlarge the
coefficient size used by the frozen tree estimate. -/
theorem frozenSelectorCoefficient_norm_le
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hb : ∀ j l k, ‖selector j l k 0‖≤1)
    (j : Fin N) (l : P.labels j) (v : Item j l) :
    ‖P.frozenSelectorCoefficient c selector j l v‖≤‖c j l v‖ := by
  simpa only [frozenSelectorCoefficient,one_mul] using
    diagonal_packet_norm (c j l v) (fun k => selector j l k 0) (by norm_num : (0:ℝ)≤1) (hb j l)

theorem physicalTreeSelectorValue_eq_sum
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ) (z : ℝ×ℝ) :
    P.physicalTreeSelectorValue 0 c (fun j l k => selector j l k (u z)) z=
      ∑ q : P.PacketIndex, P.ordinaryPacketValue 0
        (fun q => c q.1 q.2.1 q.2.2) selector u q z := by
  simp only [physicalTreeSelectorValue,ordinaryPacketValue,Fintype.sum_sigma]

theorem longOriginalLocal_eq_sum
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (i : P.DensityWhitneyCell) (z : ℝ×ℝ) :
    P.longOriginalLocal c selector u i z=
      ∑ q : P.PacketIndex, if 32*DyadicLineGrid.scale i.val.1<P.length q.1 then
        P.ordinaryPacketValue 0 (fun q => c q.1 q.2.1 q.2.2) selector u q z else 0 := by
  rw [longOriginalLocal,P.physicalTreeSelectorValue_eq_sum]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : 32*DyadicLineGrid.scale i.val.1<P.length q.1
  · simp only [ordinaryPacketValue,longCoefficient,ite_eq_left hq]
  · simp only [ordinaryPacketValue,longCoefficient,ite_eq_right hq,
      WithLp.ofLp_zero,Pi.zero_apply,zero_mul]
    rfl

theorem ordinaryTreeLocal_split
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (i : P.DensityWhitneyCell) (z : ℝ×ℝ) :
    P.physicalTreeSelectorValue 0 c (fun j l k => selector j l k (u z)) z=
      P.shortLocalValue 0 32 (fun q => c q.1 q.2.1 q.2.2) selector u i z+
        P.longOriginalLocal c selector u i z := by
  rw [P.physicalTreeSelectorValue_eq_sum,P.longOriginalLocal_eq_sum,shortLocalValue,
    ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : P.length q.1≤32*DyadicLineGrid.scale i.val.1
  · simp only [ite_eq_left hq,ite_eq_right (not_lt.mpr hq),add_zero]
  · simp only [ite_eq_right hq,ite_eq_left (lt_of_not_ge hq),zero_add]

/-- Only the original selector support is used to insert the common mask. -/
theorem longOriginalLocal_mask
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (hsupport : ∀ j l k s, selector j l k s≠0 →
      s∈scaledAngularCell (P.width/P.topLength) grid j.val (cell j l))
    (Omega : P.DensityWhitneyCell → Set ℝ)
    (hcontains : ∀ i (q : P.PacketIndex), 32*DyadicLineGrid.scale i.val.1<P.length q.1 →
      scaledAngularCell (P.width/P.topLength) grid q.1.val (cell q.1 q.2.1)⊆Omega i)
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

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
