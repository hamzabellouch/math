import OAI.Analysis.LipschitzHilbert.Trees.SourceShortTreeIntegral
import OAI.Analysis.LipschitzHilbert.Trees.SourceWhitneyGluing

namespace OAI

/-! The original short-tree sum on the full Whitney partition, with
integrability and a uniform size-density-area bound. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
open SourceWhitney DyadicLineGrid
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

abbrev WhitneyCell (P : SourceLabeledLattice N κ Label Item) :=
  CellIndex (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)

def shortLocalValue (P : SourceLabeledLattice N κ Label Item) (oldSlope CW : ℝ)
    (coefficient : P.PacketIndex → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (i : P.WhitneyCell) (z : ℝ×ℝ) : EuclideanSpace ℂ κ :=
  ∑ q : P.PacketIndex, if P.length q.1≤CW*DyadicLineGrid.scale i.val.1 then
    P.ordinaryPacketValue oldSlope coefficient selector u q z else 0

theorem packet_univ_nonempty (P : SourceLabeledLattice N κ Label Item)
    (hne : Nonempty P.PacketIndex) : (Finset.univ : Finset P.PacketIndex).Nonempty := by
  obtain ⟨q⟩ := hne
  exact ⟨q,Finset.mem_univ q⟩

def shortTreeValue (P : SourceLabeledLattice N κ Label Item) (hne : Nonempty P.PacketIndex)
    (oldSlope CW : ℝ) (coefficient : P.PacketIndex → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ) : ℝ×ℝ → EuclideanSpace ℂ κ :=
  paste (Finset.univ : Finset P.PacketIndex)
    (fun q => P.actualX q.1 q.2.1 q.2.2) (fun q => P.length q.1)
    (P.packet_univ_nonempty hne) (fun q _ => P.length_pos q.1)
    (P.shortLocalValue oldSlope CW coefficient selector u)

theorem ordinaryPacketValue_measurable (P : SourceLabeledLattice N κ Label Item)
    (oldSlope : ℝ) (coefficient : P.PacketIndex → EuclideanSpace ℂ κ)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hselector : ∀ j l a, Measurable (selector j l a))
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (q : P.PacketIndex) :
    Measurable (P.ordinaryPacketValue oldSlope coefficient selector u q) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_iff.mpr
  intro a
  exact (measurable_const.mul ((hselector q.1 q.2.1 a).comp hu)).mul
    (P.physicalPacket oldSlope q.1 q.2.1 q.2.2 a).continuous.measurable

private theorem finite_cutoff_integral {Q V : Type*} [Fintype Q] [NormedAddCommGroup V]
    (E : Set (ℝ×ℝ)) (F : Q → ℝ×ℝ → V) (keep : Q → Prop) [DecidablePred keep]
    (hF : ∀ q, IntegrableOn (F q) E (volume.prod volume)) :
    IntegrableOn (fun z => ∑ q, if keep q then F q z else 0) E (volume.prod volume) ∧
    (∫ z in E, ‖∑ q, if keep q then F q z else 0‖ ∂volume.prod volume) ≤
      ∑ q, if keep q then (∫ z in E, ‖F q z‖ ∂volume.prod volume) else 0 := by
  have hi (q : Q) : IntegrableOn (fun z => if keep q then F q z else 0) E (volume.prod volume) := by
    by_cases h : keep q
    · simpa only [ite_eq_left h] using hF q
    · simp only [ite_eq_right h]
      exact integrableOn_zero
  have hs := integrable_finsetSum Finset.univ (fun q _ => hi q)
  refine ⟨hs,?_⟩
  calc
    _ ≤ ∫ z in E, ∑ q, ‖if keep q then F q z else 0‖ ∂volume.prod volume :=
      integral_mono hs.norm (integrable_finsetSum Finset.univ (fun q _ => (hi q).norm))
        (fun z => norm_sum_le _ _)
    _ = ∑ q, ∫ z in E, ‖if keep q then F q z else 0‖ ∂volume.prod volume :=
      integral_finsetSum _ (fun q _ => (hi q).norm)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      by_cases h : keep q <;> simp only [h,ite_true,ite_false,norm_zero,integral_zero]

/-- The original short-tree sum is integrable on the full Whitney partition. -/
theorem short_tree_integrable_bound (P : SourceLabeledLattice N κ Label Item)
    (hne : Nonempty P.PacketIndex) (B : ℕ) (hcard : ∀ j, (P.labels j).card≤B)
    (oldSlope : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (w tau : ℝ)
    (htime : P.topLength≤tau)
    (hslope : ∀ j l, oldSlope+P.rowSlope j l ∈
      scaledAngularCell (w/P.topLength) grid j.val (cell j l))
    (horder : 205≤2*P.order) (M sigma eta : ℝ)
    (hM : 0≤M) (hsigma : 0≤sigma) (heta : 0≤eta)
    (coefficient : P.PacketIndex → EuclideanSpace ℂ κ)
    (hcoefficient : ∀ q, ‖coefficient q‖≤sigma)
    (selector : ∀ j, P.labels j → κ → ℝ → ℂ)
    (hselector : ∀ j l a, Measurable (selector j l a))
    (hbound : ∀ j l a s, ‖selector j l a s‖≤M)
    (hsupport : ∀ j l a s, selector j l a s≠0 →
      s∈scaledAngularCell (w/P.topLength) grid j.val (cell j l))
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (hdensity : ∀ q, P.ordinaryDensity oldSlope cell grid w tau E u q≤eta)
    (x y CW : ℝ) (hCW : 1≤CW)
    (hX : ∀ q : P.PacketIndex, |P.actualX q.1 q.2.1 q.2.2-x|≤P.topLength/2)
    (hY : ∀ j l v, |P.actualZ j l v-y|≤P.width)
 :
    IntegrableOn (P.shortTreeValue hne oldSlope CW coefficient selector u) E (volume.prod volume) ∧
    (∫ z in E, ‖P.shortTreeValue hne oldSlope CW coefficient selector u z‖ ∂volume.prod volume) ≤
      (27*288*(4*Real.pi)^2*(B:ℝ)*CW*(3:ℝ)^203*P.profileBound*M)*
        sigma*eta*P.topLength*P.width := by
  classical
  let tiles := (Finset.univ : Finset P.PacketIndex)
  let X := fun q : P.PacketIndex => P.actualX q.1 q.2.1 q.2.2
  let ell := fun q : P.PacketIndex => P.length q.1
  let F := P.shortLocalValue oldSlope CW coefficient selector u
  have hlen (j : Fin N) : P.length j≤tau :=
    (div_le_self P.topLength_pos.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))).trans htime
  have hpiece (i : P.WhitneyCell) (q : P.PacketIndex) :
      IntegrableOn (P.ordinaryPacketValue oldSlope coefficient selector u q)
        (strip tiles X ell E i) (volume.prod volume) := by
    have h := P.own_packet_whitney_density_bound oldSlope cell grid w tau q
      (hlen q.1) (hslope q.1 q.2.1) horder M sigma eta hM hsigma
      (coefficient q) (hcoefficient q) (selector q.1 q.2.1)
      (hselector q.1 q.2.1) (hbound q.1 q.2.1) (hsupport q.1 q.2.1)
      u hu E hE (hdensity q) i.val.1 i.val.2
    exact (integrable_norm_iff
      (P.ordinaryPacketValue_measurable oldSlope coefficient selector hselector u hu q).aestronglyMeasurable).mp h.1
  have hlocal (i : P.WhitneyCell) :
      IntegrableOn (F i) (strip tiles X ell E i) (volume.prod volume) ∧
      (∫ z in strip tiles X ell E i, ‖F i z‖ ∂volume.prod volume) ≤
        ∑ q : P.PacketIndex, if P.length q.1≤CW*DyadicLineGrid.scale i.val.1 then
          (∫ z in strip tiles X ell E i,
            ‖P.ordinaryPacketValue oldSlope coefficient selector u q z‖ ∂volume.prod volume) else 0 :=
    finite_cutoff_integral (strip tiles X ell E i)
      (P.ordinaryPacketValue oldSlope coefficient selector u)
      (fun q => P.length q.1≤CW*DyadicLineGrid.scale i.val.1) (hpiece i)
  apply paste_integrable_bound tiles X ell (P.packet_univ_nonempty hne)
    (fun q _ => P.length_pos q.1) E hE F (fun i => (hlocal i).1)
  intro S
  have hs := P.short_tree_finite_strip_bound B hcard oldSlope cell grid w tau htime hslope
    horder M sigma eta hM hsigma heta coefficient hcoefficient selector hselector hbound hsupport
    u hu E hE hdensity x y CW hCW hX hY (S.image Subtype.val)
    (by intro p hp; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp; exact i.property)
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)] at hs
  apply le_trans (Finset.sum_le_sum (fun i _ => (hlocal i).2))
  exact hs

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
