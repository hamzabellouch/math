import OAI.Analysis.LipschitzHilbert.Packets.PacketDataAssignedMaskSums
import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskIntegral

namespace OAI

/-! Mask removal for the literal assigned original packet sum. The
per-top raw concentration bound is used with the unchanged original
analyzing coefficients, after exact finite regrouping. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem source_assigned_mask_removal (hLL : LaceyLiInput) (C H a aw s d : ℝ)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (haw : 0 ≤ aw) (hs : 0 ≤ s) (hd : 4 ≤ d) :
    ∃ A L0 : ℝ, a < A ∧ 2 < A ∧ 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
      (N : ℕ) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [∀ j l, Fintype (Item j l)] (P : PacketLatticeData N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w Freq : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hFreq : 0 ≤ Freq) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ Freq/w)
      (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
      (f : ℝ×ℝ → EuclideanSpace ℂ κ),
      (∀ q ∈ packets, P.referenceCondition oldSlope (T (assigned q)).slope
        (R (assigned q)) cone w q.1 q.2.1) →
    ∀ l r : ℝ, (∀ i, |(T i).slope| ≤ 1) →
    ∀ (u : Plane → ℝ) (lip : ℝ≥0), LipschitzWith lip u →
      300*((2*lip:ℝ≥0):ℝ)*(r-l) ≤ 1 →
    ∀ E : τ → Set (ℝ×ℝ), (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ (T i).radius z ≤ L^aw) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal (L^(-aw)*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) → 0 < ∑ i, (T i).area →
    ∀ (ratio : ℝ) (F G : Set (ℝ×ℝ)), 0 ≤ ratio →
      (volume.prod volume) F ≠ ∞ → MeasurableSet G → G ⊆ F →
      (∀ z ∈ G, z.1 ∈ Icc l r) →
      (∑ i, (T i).area) ≤ L^s*ratio^2*(volume.prod volume).real F →
    let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency
    let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency
    let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency alt
    let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w Freq
      hw hcone hFreq hwide hfrequency alt hAlt
    (∀ z ∈ G, ∀ top,
      ‖((Q top).withProfile (alts top) (halt top)).rawInterval
        (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig top j l) u.val)
        0 0 N z.1 (z.2-(T top).slope*z.1)‖ ≤ L^C*((T top).weight (L^a) d z)^8) →
    let original := fun z => ∑ q ∈ packets, P.crossPacketValue alt hAlt oldSlope b v f z q
    let masked := fun z => ∑ q ∈ packets, P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z q
    IntegrableOn (fun z => ‖original z-masked z‖) G (volume.prod volume) ∧
      (∫ z in G, ‖original z-masked z‖ ∂volume.prod volume) ≤
        L^(-H)*ratio*(volume.prod volume).real F := by
  obtain ⟨A,L0,haA,hA,hL0,hmask⟩ := source_mask_integral hLL C H a aw s d hC hH haw hs hd
  refine ⟨A,L0,haA,hA,hL0,?_⟩
  intro L hL τ κ _ _ N Label Item _ P packets assigned T oldSlope R cone w Freq
    hw hcone hFreq hwide hfrequency alt hAlt b v f hcondition l r hslopes u lip hu hlength
    E hE hdisj hinside hclose hsize hSpos ratio F G hratio hFfin hG hGF hstrip hS
    Q orig alts halt hraw original masked
  let V := fun top z => ∑ q ∈ packets.filter (fun q => assigned q = top),
    P.crossPacketValue alt hAlt oldSlope b v f z q
  have hV (top : τ) : Measurable (V top) := by
    apply Continuous.measurable
    exact continuous_finsetSum _ (fun q _ => P.crossPacketValue_continuous alt hAlt oldSlope b v f q)
  have hpoint : ∀ᵐ z ∂(volume.prod volume).restrict G, ∀ top,
      ‖V top z‖ ≤ L^C*((T top).weight (L^a) d z)^8 := by
    filter_upwards [ae_restrict_mem hG] with z hz
    intro top
    dsimp only [V]
    rw [P.assignedCrossSum_eq_rawInterval alt hAlt oldSlope b v f packets assigned T R cone w Freq
      hw hcone hFreq hwide hfrequency z top (fun q hq hqt => by
        simpa only [hqt] using hcondition q hq)]
    exact hraw z hz top
  have hm := hmask L hL τ κ T l r hslopes u lip hu hlength E hE hdisj hinside hclose
    hsize hSpos ratio F G hratio hFfin hG hGF hstrip hS V hV hpoint
  have horig (z : ℝ×ℝ) : (∑ top, V top z) = original z := by
    exact Finset.sum_fiberwise_of_maps_to (fun q _ => Finset.mem_univ (assigned q))
      (fun q => P.crossPacketValue alt hAlt oldSlope b v f z q)
  have hmasked (z : ℝ×ℝ) : (∑ top, (T top).mask L A z • V top z) = masked z := by
    exact (P.sum_assignedPhysicalMaskedValue alt hAlt oldSlope b v f packets assigned T
      Finset.univ (fun q _ => Finset.mem_univ (assigned q)) L A z).symm
  simpa only [horig,hmasked] using hm

end LipschitzHilbert.PacketLatticeData

end

end OAI
