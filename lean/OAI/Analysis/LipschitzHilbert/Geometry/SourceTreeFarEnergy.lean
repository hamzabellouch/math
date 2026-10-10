import OAI.Analysis.LipschitzHilbert.Geometry.SourceFarGramReduction
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceWeightedMaximal

namespace OAI

/-! The analytic distant-scale bound for a selected long tree and a
packed short family, conditional only on the published Lépingle input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem exists_tree_far_gram_bound (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (M Q : ℕ), Cb≤Q →
      ∀ (t w a b L F sigma K : ℝ), 0<w → 0<L → 0≤F → Cb*w≤P.width →
      (∀ k, |P.frequency k|≤F/w) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
    ∀ (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
      (S T : Finset P.PacketIndex) (gap : ℕ),
      (∀ q∈T, P.length q.1≤L) →
      (∀ q∈T, |P.actualX q.1 q.2.1 q.2.2-a|≤L) →
      (∀ q∈T, |(P.actualZ q.1 q.2.1 q.2.2-b)-t*(P.actualX q.1 q.2.1 q.2.2-a)|≤P.width) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) →
      (∀ q∈T, cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| ∧
        |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1) →
      (∀ q∈S, ‖c q.1 q.2.1 q.2.2‖≤sigma) →
      (∀ q∈S, |(P.rowSlope q.1 q.2.1-t)*P.length q.1/P.width|≤1) →
      (∀ q∈S, P.length q.1≤L) →
      (∀ z : ℝ×ℝ, ((S.filter fun q => |z.1-P.actualX q.1 q.2.1 q.2.2|≤P.length q.1 ∧
        |(z.2-P.actualZ q.1 q.2.1 q.2.2)-t*(z.1-P.actualX q.1 q.2.1 q.2.2)|≤P.width).card:ℝ)≤K) →
      ‖∑ q∈S, ∫ z, inner ℂ (P.packetVector c q z) (P.longPacketSum c T gap q.1 z)
        ∂volume.prod volume‖^2≤
        (4*P.profileBound*sigma)^2*256*(82944*K)^2*1296*Real.pi^2*L*P.width*
          ((((2*Q+1)*M:ℕ):ℝ)*C*P.absoluteConstant^2*
            ∑ q∈T, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width) := by
  obtain ⟨C,hC,hmax⟩ := exists_reference_weighted_tree_maximal hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M Q hQ t w a b L F sigma K hw hLen hF hwide hfreq hlocal
    c S T gap hTlen hTX hTZ hspec hsep hScoeff hSclose hSlen hpack
  let d := P.onPackets T c
  have hmem (j : Fin N) (l : P.labels j) (u : Item j l) (h : d j l u≠0) :
      (⟨j,⟨l,u⟩⟩ : P.PacketIndex)∈T := P.onPackets_nonzero T c j l u h
  obtain ⟨hi,hb⟩ := hmax N κ Label Item P M Q hQ t w a b L F hw hLen hF hwide hfreq hlocal d
    (fun j l u hn => hTlen ⟨j,⟨l,u⟩⟩ (hmem j l u hn))
    (fun j l u hn => hTX ⟨j,⟨l,u⟩⟩ (hmem j l u hn))
    (fun j l u hn => hTZ ⟨j,⟨l,u⟩⟩ (hmem j l u hn))
    hspec (fun j l u hn => hsep ⟨j,⟨l,u⟩⟩ (hmem j l u hn))
  have hm := P.onPackets_energy_sum T c
  change (∑ j, ∑ l : P.labels j, ∑ u, ‖d j l u‖^2*P.length j*P.width)=_ at hm
  rw [hm] at hb
  let U := P.physicalTreeMaximal 0 d
  have hUi : Integrable (fun z => (treeProductPolynomial a (b-t*a) L P.width t z*U z)^2)
      (volume.prod volume) := by simpa only [mul_pow] using hi
  have hUb : (∫ z, (treeProductPolynomial a (b-t*a) L P.width t z*U z)^2 ∂volume.prod volume)≤
      (((2*Q+1)*M:ℕ):ℝ)*C*P.absoluteConstant^2*
        ∑ q∈T, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
    simpa only [mul_pow] using hb
  have hp := P.packed_short_packet_pairing_sq c S a b L t sigma K _ hLen hScoeff hSclose hSlen hpack
    U (P.physicalTreeMaximal_continuous 0 d).measurable
    (fun z => intervalOscillation_nonneg _ _ _ _) hUi hUb
  have hf := P.far_gram_le_maximal_pairing c S T gap hp.1
  exact (pow_le_pow_left₀ (norm_nonneg _) hf 2).trans hp.2

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
