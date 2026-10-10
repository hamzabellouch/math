import OAI.Analysis.LipschitzHilbert.Geometry.SourceTransverseTreeMaximal
import OAI.Analysis.LipschitzHilbert.Packets.SourceLabeledPacketRestriction

namespace OAI

/-! Transverse maximal energy needs separation only on packets whose
coefficients are nonzero. Restriction retains the original partial sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

private theorem partial_as_index_sum (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (n : ℕ) (z : ℝ×ℝ) :
    P.physicalTreePartial t c n z=∑ q : P.PacketIndex,
      if q.1.val<n then WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2 k*
        P.physicalPacket t q.1 q.2.1 q.2.2 k z) else 0 := by
  ext k
  simp only [physicalTreePartial,packetPartialSum,WithLp.ofLp_sum,Finset.sum_apply,
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val<n
  · simp only [hj,ite_true,planarFixedSynthesis,WithLp.ofLp_toLp,Fintype.sum_sigma]
  · simp only [hj,ite_false,WithLp.ofLp_zero,Pi.zero_apply,Finset.sum_const_zero]

/-- Removing zero coefficients leaves every actual partial sum unchanged. -/
theorem restrict_nonzero_partial
    (Q : Finset P.PacketIndex) (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (hc : ∀ q : P.PacketIndex, q∉Q → c q.1 q.2.1 q.2.2=0)
    (n : ℕ) (z : ℝ×ℝ) :
    (P.restrictPackets Q).physicalTreePartial t (fun j l v => c j l v.val) n z=
      P.physicalTreePartial t c n z := by
  rw [partial_as_index_sum,partial_as_index_sum]
  change (∑ q : (P.restrictPackets Q).PacketIndex,
    if q.1.val<n then WithLp.toLp 2 (fun k => c q.1 q.2.1 q.2.2.val k*
      P.physicalPacket t q.1 q.2.1 q.2.2.val k z) else 0)=_
  rw [P.sum_restrictPackets Q (fun q => if q.1.val<n then WithLp.toLp 2
    (fun k => c q.1 q.2.1 q.2.2 k*P.physicalPacket t q.1 q.2.1 q.2.2 k z) else 0)]
  apply Finset.sum_subset (Finset.subset_univ Q)
  intro q _ hq
  rw [hc q hq]
  simp only [WithLp.ofLp_zero,Pi.zero_apply,zero_mul]
  split_ifs <;> rfl

theorem exists_supported_transverse_tree_maximal (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (B : ℕ),
      (∀ j, (P.labels j).card≤B) → ∀ (t w b : ℝ), 0<w → 207≤P.order →
    ∀ c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ,
      (∀ j l v, |P.actualZ j l v-b|≤P.width) →
      (∀ j l v k ξ η, planarAngularFourier (P.physicalPacket t j l v k) (ξ,η)≠0 →
        |ξ+(t+P.rowSlope j l)*η|≤cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta) →
      (∀ j l v, c j l v≠0 → cb*w/P.length j≤|P.rowSlope j l| ∧
        |P.rowSlope j l|≤Cb*w/P.length j) →
      let E := fun z => polynomialWeight b (2*P.width) 103 (z.2-t*z.1)^2*
        P.physicalTreeMaximal t c z^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume)≤(B:ℝ)*C*P.absoluteConstant^2*
        ∑ j, ∑ l : P.labels j, ∑ v : Item j l, ‖c j l v‖^2*P.length j*P.width := by
  obtain ⟨C,hC,hmax⟩ := exists_transverse_labeled_tree_maximal hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P B hcard t w b hw horder c hZ hspectrum hselector
  let Q := Finset.univ.filter (fun q : P.PacketIndex => c q.1 q.2.1 q.2.2≠0)
  let R := P.restrictPackets Q
  let d := fun j (l : R.labels j) (v : P.RestrictedPacketItem Q j l) => c j l v.val
  have hnz (j : Fin N) (l : R.labels j) (v : P.RestrictedPacketItem Q j l) : c j l v.val≠0 := by
    have hm := (P.restrictedPacketEquiv Q ⟨j,⟨l,v⟩⟩).property
    exact (Finset.mem_filter.mp hm).2
  have hz (q : P.PacketIndex) (hq : q∉Q) : c q.1 q.2.1 q.2.2=0 := by
    simpa only [Q,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hq
  obtain ⟨hi,hb⟩ := hmax N κ Label (P.RestrictedPacketItem Q) R B hcard t w b hw horder d
    (fun j l v => hZ j l v.val) (fun j l v k ξ η => hspectrum j l v.val k ξ η)
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
