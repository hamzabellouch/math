import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedTreeMaximal
import OAI.Analysis.LipschitzHilbert.Trees.SourceWeightedTreeMaximal

namespace OAI

/-! Product-weighted maximal control only needs tree geometry and
separation on packets with nonzero coefficients. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

theorem exists_supported_weighted_tree_maximal (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card≤B) → ∀ (t w a b r : ℝ), 0<w → 0<r →
    ∀ c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ,
      (∀ j l v, c j l v≠0 → P.length j≤r) →
      (∀ j l v, c j l v≠0 → |P.actualX j l v-a|≤r) →
      (∀ j l v, c j l v≠0 → |P.actualZ j l v-b|≤P.width) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket t j l v k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j l)*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j l v, c j l v≠0 → cb*w/P.length j≤|P.rowSlope j l| ∧
        |P.rowSlope j l|≤Cb*w/P.length j) →
      let E := fun z => treeProductPolynomial a b r P.width t z^2*
        P.physicalTreeMaximal t c z^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume)≤(B:ℝ)*C*P.absoluteConstant^2*
        ∑ j, ∑ l : P.labels j, ∑ v : Item j l, ‖c j l v‖^2*P.length j*P.width := by
  obtain ⟨C,hC,hmax⟩ := exists_weighted_labeled_tree_maximal hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P B hcard t w a b r hw hr c hlen hX hZ hspectrum hselector
  let Q := Finset.univ.filter (fun q : P.PacketIndex => c q.1 q.2.1 q.2.2≠0)
  let R := P.restrictPackets Q
  let d := fun j (l : R.labels j) (v : P.RestrictedPacketItem Q j l) => c j l v.val
  have hnz (j : Fin N) (l : R.labels j) (v : P.RestrictedPacketItem Q j l) : c j l v.val≠0 := by
    have hm := (P.restrictedPacketEquiv Q ⟨j,⟨l,v⟩⟩).property
    exact (Finset.mem_filter.mp hm).2
  have hz (q : P.PacketIndex) (hq : q∉Q) : c q.1 q.2.1 q.2.2=0 := by
    simpa only [Q,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hq
  obtain ⟨hi,hb⟩ := hmax N κ Label (P.RestrictedPacketItem Q) R B hcard t w a b r hw hr d
    (fun j l v => hlen j l v.val (hnz j l v))
    (fun j l v => hX j l v.val (hnz j l v))
    (fun j l v => hZ j l v.val (hnz j l v)) (fun j l v k ξ η => hspectrum j l v.val k ξ η)
    (fun j l v => hselector j l v.val (hnz j l v))
  have heq (z : ℝ×ℝ) : R.physicalTreeMaximal t d z=P.physicalTreeMaximal t c z := by
    unfold physicalTreeMaximal
    congr 1
    funext n
    exact P.restrict_nonzero_partial Q t c hz n z
  have hmass : (∑ j, ∑ l : R.labels j, ∑ v : P.RestrictedPacketItem Q j l,
      ‖d j l v‖^2*R.length j*R.width)=
      ∑ j, ∑ l : P.labels j, ∑ v : Item j l, ‖c j l v‖^2*P.length j*P.width := by
    have hsum := P.sum_restrictPackets Q
      (fun q => ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width)
    calc
      _ = ∑ q∈Q, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
        change (∑ j, ∑ l : P.labels j, ∑ v : P.RestrictedPacketItem Q j l,
          ‖c j l v.val‖^2*P.length j*P.width)=_
        simp only [Fintype.sum_sigma] at hsum
        convert hsum using 1
        congr 1
      _ = ∑ q : P.PacketIndex, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
        apply Finset.sum_subset (Finset.subset_univ Q)
        intro q _ hq
        rw [hz q hq]
        simp only [norm_zero,zero_pow (by decide : 2≠0),zero_mul]
      _ = _ := by simp only [Fintype.sum_sigma]
  simp only [heq] at hi hb
  rw [hmass] at hb
  exact ⟨hi,hb⟩


end LipschitzHilbert.SourceLabeledLattice

end

end OAI
