import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedWeightedMaximal
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceLabelCount
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceSelectorGeometry

namespace OAI

/-! Weighted long-tree control in the original physical coordinates.
The reference cone is an actual restriction of the original labels. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
attribute [local instance] Classical.propDecidable

theorem exists_reference_weighted_tree_maximal (hL : LepingleInput)
    (cStar cEta CEta cb Cb : ℝ) (hcStar : 0≤cStar) (hcEta : 0<cEta)
    (hCEta : 0≤CEta) (hcb : 0≤cb) (hCb : 0≤Cb) (hgap : cStar<cEta*cb) :
    ∃ C : ℝ, 0<C ∧ ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type)
      (Item : ∀ j, Label j → Type) [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (M Q : ℕ), Cb≤Q →
      ∀ (t w a b r F : ℝ), 0<w → 0<r → 0≤F → Cb*w≤P.width →
      (∀ k, |P.frequency k|≤F/w) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ (P.rowSlope j) (w/P.length j) M) →
    ∀ c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ,
      (∀ j l u, c j l u≠0 → P.length j≤r) →
      (∀ j l u, c j l u≠0 → |P.actualX j l u-a|≤r) →
      (∀ j l u, c j l u≠0 → |(P.actualZ j l u-b)-t*(P.actualX j l u-a)|≤P.width) →
      (∀ j l u k xi eta, planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) →
      (∀ j l u, c j l u≠0 → cb*w/P.length j≤|P.rowSlope j l-t| ∧
        |P.rowSlope j l-t|≤Cb*w/P.length j) →
      let E := fun z => treeProductPolynomial a (b-t*a) r P.width t z^2*
        P.physicalTreeMaximal 0 c z^2
      Integrable E (volume.prod volume) ∧
      (∫ z, E z ∂volume.prod volume)≤(((2*Q+1)*M:ℕ):ℝ)*C*P.absoluteConstant^2*
        ∑ j, ∑ l : P.labels j, ∑ u : Item j l, ‖c j l u‖^2*P.length j*P.width := by
  obtain ⟨C,hC,hmax⟩ := exists_supported_weighted_tree_maximal hL
    cStar cEta CEta cb Cb hcStar hcEta hCEta hcb hCb hgap
  refine ⟨C,hC,?_⟩
  intro N κ Label Item _ _ P M Q hQ t w a b r F hw hr hF hwide hfrequency hlocal
    c hlen hX hZ hspectrum hselector
  let R := P.referenceFamily 0 t r Cb w F hw hCb hF hwide hfrequency
  let orig := P.referenceOriginalLabel 0 t r Cb w
  let d := fun j (l : R.labels j) (u : Item j l) => c j (orig j l) u
  have houtside (j : Fin N) (l : P.labels j)
      (hout : ¬P.referenceCondition 0 t r Cb w j l) (u : Item j l) : c j l u=0 := by
    by_contra hn
    apply hout
    exact ⟨hlen j l u hn,by simpa only [zero_add] using (hselector j l u hn).2⟩
  have hcard (j : Fin N) : (R.labels j).card≤(2*Q+1)*M :=
    P.referenceLabels_card_le_local 0 t r Cb w hw M Q hQ j
      (by simpa only [zero_add] using hlocal j)
  have hspec : ∀ j l u k xi eta, planarAngularFourier (R.physicalPacket t j l u k) (xi,eta)≠0 →
      |xi+(t+R.rowSlope j l)*eta|≤cStar/R.length j ∧ cEta≤w*eta ∧ w*eta≤CEta :=
    P.referenceFamily_spectrum 0 t r Cb w F hw hCb hF hwide hfrequency
      cStar cEta CEta (by simpa only [zero_add] using hspectrum)
  obtain ⟨hInt,hBound⟩ := hmax N κ Label Item R ((2*Q+1)*M) hcard t w a (b-t*a) r hw hr d
    (fun j l u hn => hlen j (orig j l) u hn)
    (fun j l u hn => hX j (orig j l) u hn)
    (fun j l u hn => by
      have hz := hZ j (orig j l) u hn
      change |(P.referenceFamily 0 t r Cb w F hw hCb hF hwide hfrequency).actualZ j l u-
        (b-t*a)|≤P.width
      rw [P.referenceFamily_actualZ 0 t r Cb w F hw hCb hF hwide hfrequency j l u]
      have he : P.actualZ j (orig j l) u+(0-t)*P.actualX j (orig j l) u-(b-t*a)=
          (P.actualZ j (orig j l) u-b)-t*(P.actualX j (orig j l) u-a) := by ring
      change |P.actualZ j (orig j l) u+(0-t)*P.actualX j (orig j l) u-(b-t*a)|≤P.width
      rw [he]
      exact hz)
    hspec
    (fun j l u hn => by
      have hs := hselector j (orig j l) u hn
      change cb*w/P.length j≤|P.rowSlope j (orig j l)+(0-t)| ∧
        |P.rowSlope j (orig j l)+(0-t)|≤Cb*w/P.length j
      simpa only [zero_sub,zero_add,sub_eq_add_neg] using hs)
  have hpartial (n : ℕ) (z : ℝ×ℝ) : R.physicalTreePartial t d n z=P.physicalTreePartial 0 c n z := by
    unfold physicalTreePartial packetPartialSum
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val<n
    · simp only [hj,ite_true]
      ext k
      simp only [planarFixedSynthesis,WithLp.ofLp_toLp,Fintype.sum_sigma]
      have hp (l : R.labels j) (u : Item j l) : R.physicalPacket t j l u k=
          P.physicalPacket 0 j (orig j l) u k :=
        P.referenceFamily_physicalPacket 0 t r Cb w F hw hCb hF hwide hfrequency j l u k
      change (∑ l : R.labels j, ∑ u : Item j l, d j l u k*R.physicalPacket t j l u k z)=_
      simp_rw [hp]
      exact P.sum_referenceLabels_of_zero 0 t r Cb w j
        (fun l u => c j l u k*P.physicalPacket 0 j l u k z)
        (fun l hl u => by rw [houtside j l hl u]; simp)
    · simp only [hj,ite_false]
  have heq (z : ℝ×ℝ) : R.physicalTreeMaximal t d z=P.physicalTreeMaximal 0 c z := by
    unfold physicalTreeMaximal
    congr 1
    funext n
    exact hpartial n z
  have hmass : (∑ j, ∑ l : R.labels j, ∑ u : Item j l,
      ‖d j l u‖^2*R.length j*R.width)=
      ∑ j, ∑ l : P.labels j, ∑ u : Item j l, ‖c j l u‖^2*P.length j*P.width := by
    apply Finset.sum_congr rfl
    intro j _
    exact P.sum_referenceLabels_of_zero 0 t r Cb w j
      (fun l u => ‖c j l u‖^2*P.length j*P.width)
      (fun l hl u => by rw [houtside j l hl u]; simp)
  simp only [heq] at hInt hBound
  rw [hmass] at hBound
  exact ⟨hInt,hBound⟩

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
