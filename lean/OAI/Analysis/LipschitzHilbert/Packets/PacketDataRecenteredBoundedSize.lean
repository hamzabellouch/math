import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundedTreeSize
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedDuality
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedSum

namespace OAI

/-! Bounded inputs control the original analyzing coefficients in an
arbitrary reference tree, using only the occupied angular rows. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData

theorem exists_recentered_bounded_size (cStar cEta CEta cb : ℝ)
    (hcEta : 0<cEta) (hcb : 0≤cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item) (M : ℕ) (Q : Finset P.PacketIndex)
      (t a b r w F G : ℝ), 0<r → 0<w → w≤P.width → 0≤F → 0≤G →
      (∀ k, |P.frequency k|≤F/w) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
      (∀ q∈Q, P.length q.1≤r) →
      (∀ q∈Q, |P.actualX q.1 q.2.1 q.2.2-a|≤r) →
      (∀ q∈Q, |P.actualZ q.1 q.2.1 q.2.2-t*P.actualX q.1 q.2.1 q.2.2-b|≤P.width) →
      (∀ q∈Q, cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| ∧
        |P.rowSlope q.1 q.2.1-t|≤w/P.length q.1) →
      (∀ q∈Q, ∀ k xi eta, planarAngularFourier (P.physicalPacket 0 q.1 q.2.1 q.2.2 k) (xi,eta)≠0 →
        |xi+P.rowSlope q.1 q.2.1*eta|≤cStar/P.length q.1 ∧ cEta≤w*eta ∧ w*eta≤CEta) →
    ∀ (g : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable g → (∀ z, ‖g z‖≤G) →
      (∑ q∈Q, P.length q.1*P.width*‖P.ordinaryCoefficient g q.1 q.2.1 q.2.2‖^2)≤
        ((3*M:ℕ):ℝ)*C*P.referenceEnvelopeConstant^2*G^2*(r*P.width) := by
  obtain ⟨C,hC,hBound⟩ := SourceLabeledLattice.exists_physical_bounded_tree_size cStar cEta CEta cb 1
    hcEta hcb (by norm_num) hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M Q t a b r w F G hr hw hW hF hG hfreq hlocal hlen hX hZ hcone hspectrum g hg hgG
  have hnear : ∀ q ∈ Q, |P.rowSlope q.1 q.2.1-t| ≤ 1*w/P.length q.1 := by
    intro q hq
    simpa only [one_mul] using (hcone q hq).2
  have hwide : 1*w ≤ P.width := by simpa only [one_mul] using hW
  let T := P.selectedReference Q t 1 w F hw zero_le_one hF hwide hfreq hnear
  have hcard (j : Fin N) : (T.labels j).card ≤ 3*M := by
    simpa only [show (2*1+1:ℕ)=3 by norm_num] using
      P.selectedReference_card Q t 1 w F hw zero_le_one hF hwide hfreq hnear M 1
        (by norm_num) hlocal j
  have hpacket (j : Fin N) (l : T.labels j) (v : P.SelectedItem Q j l) (k : κ) :
      (T.physicalPacket t j l v k : ℝ×ℝ → ℂ)=
        P.physicalPacket 0 j (P.selectedOriginalLabel Q j l) v.val k := by
    funext z
    exact congrArg (fun f : SchwartzMap (ℝ×ℝ) ℂ => f z)
      (P.selectedReference_physicalPacket Q t 1 w F hw zero_le_one hF hwide hfreq hnear j l v k)
  have h := hBound N κ Label (P.SelectedItem Q) T (3*M) hcard t w a b r hw hr
    (fun _ _ => 1) g G hG (by intro q k; simp) hg hgG
    (fun j l v => hlen ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ (P.selectedItem_mem Q j l v))
    (fun j l v => hX ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ (P.selectedItem_mem Q j l v))
    (by
      intro j l v
      have he := P.selectedReference_actualZ Q t 1 w F hw zero_le_one hF hwide hfreq hnear j l v
      have ha := congrArg (fun x : ℝ => |x-b|) he
      exact ha.le.trans (hZ ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ (P.selectedItem_mem Q j l v)))
    (by
      intro j l v k xi eta hn
      rw [hpacket] at hn
      have hp := hspectrum ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩
        (P.selectedItem_mem Q j l v) k xi eta hn
      change |xi+(t+(P.rowSlope j (P.selectedOriginalLabel Q j l)-t))*eta|≤cStar/P.length j ∧
        cEta≤w*eta ∧ w*eta≤CEta
      simpa only [add_sub_cancel] using hp)
    (by
      intro j l v
      have hp := hcone ⟨j,⟨P.selectedOriginalLabel Q j l,v.val⟩⟩ (P.selectedItem_mem Q j l v)
      change cb*w/P.length j≤|P.rowSlope j (P.selectedOriginalLabel Q j l)-t| ∧
        |P.rowSlope j (P.selectedOriginalLabel Q j l)-t|≤1*w/P.length j
      simpa only [one_mul] using hp)
  have hc (q : T.PacketIndex) : T.physicalFrozenCoefficient t (fun _ _ => 1) g q=
      P.ordinaryCoefficient g q.1 (P.selectedOriginalLabel Q q.1 q.2.1) q.2.2.val := by
    apply WithLp.ofLp_injective
    funext k
    simp only [SourceLabeledLattice.physicalFrozenCoefficient,ordinaryCoefficient,analyzingCoefficient,
      WithLp.ofLp_toLp,one_mul,hpacket]
    rfl
  simp_rw [hc] at h
  have hs := P.selectedReference_sum Q t 1 w F hw zero_le_one hF hwide hfreq hnear (fun q =>
    P.length q.1*P.width*‖P.ordinaryCoefficient g q.1 q.2.1 q.2.2‖^2)
  exact hs.symm.le.trans h

end LipschitzHilbert.PacketLatticeData

end

end OAI
