import OAI.Analysis.LipschitzHilbert.Packets.PacketDataRecenteredReferenceConditions

namespace OAI

/-! The literal parent-square and continuing-path reference events have
one common weighted bad-mass and area bound. Only original physical packet
spectra, selectors, and assigned-top geometry enter the hypotheses. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology ENNReal BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable

theorem eventually_actual_reference_area
    (hVariation : LepingleInput)
    (D weightPower q A F cStar cEta CEta cb Cb C Lip : ℝ) (K Hlabels : ℕ)
    (hD : 2 < D) (hq : 0 ≤ q) (hA : 1 < A) (hF : 0 ≤ F)
    (hcStar : 0 ≤ cStar) (hcEta : 0 < cEta) (hCEta : 0 ≤ CEta)
    (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb) (hC : 0 ≤ C) (hLip : 0 ≤ Lip)
    (hgap : cStar < cEta*cb) :
    ∀ᶠ L : ℝ in atTop, ∀ (Kw : ℝ), 1 ≤ Kw → Kw ≤ L^weightPower →
    ∀ (N : ℕ) (κ τ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item), 6 ≤ P.order → P.referenceEnvelopeConstant ≤ L^q →
    ∀ (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (oldSlope w : ℝ) (hw : 0 < w)
      (hwide : ∀ i : Option (Fin (SourceParameters.blockCount L)),
        (C+(SourceParameters.branching L)^(if i.isNone then 3 else 2))*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w), Cb*w ≤ P.width →
    ∀ (b : ∀ j, P.labels j → κ → ℝ → ℂ),
      (∀ j l k, Measurable (b j l k)) → (∀ j l k s, ‖b j l k s‖ ≤ 1) →
      (∀ j l k s, b j l k s ≠ 0 →
        |s-(oldSlope+P.rowSlope j l)| ≤ (K:ℝ)*(w/P.length j)) →
      (∀ j l k s t, ‖b j l k s-b j l k t‖ ≤ Lip*(|s-t|/(w/P.length j))) →
      (∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
        (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) Hlabels) →
      (∀ j l k s, b j l k s ≠ 0 →
        cb*w/P.length j ≤ |s-(oldSlope+P.rowSlope j l)| ∧
          |s-(oldSlope+P.rowSlope j l)| ≤ Cb*w/P.length j) →
    ∀ (v : ℝ×ℝ → ℝ), Measurable v →
    ∀ (f : ℝ×ℝ → EuclideanSpace ℂ κ), Measurable f → (∀ z, ‖f z‖ ≤ 1) →
      (∀ j l u k xi eta,
        planarAngularFourier (P.physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
          |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
            cEta ≤ w*eta ∧ w*eta ≤ CEta) →
      (∀ j l u k xi eta,
        planarAngularFourier ((P.withProfile alt hAlt).physicalPacket oldSlope j l u k) (xi,eta) ≠ 0 →
          |xi+(oldSlope+P.rowSlope j l)*eta| ≤ cStar/P.length j ∧
            cEta ≤ w*eta ∧ w*eta ≤ CEta) →
    ∀ (g : AngularGrid) (tops : Finset τ) (T : τ → SlopeBox)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (hKb : 0 < SourceParameters.blockCount L),
      (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
      (∀ u ∈ packets,
        |oldSlope+P.rowSlope u.1 u.2.1-(T (assigned u)).slope| ≤ C*(w/P.length u.1)) →
      (∀ u ∈ packets, (SourceParameters.branching L)^2*w ≤ (T (assigned u)).width) →
    ∀ (base : Set (ℝ×ℝ)), MeasurableSet base →
      let bad := P.actualReferenceBad alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
        b v f g tops T packets assigned hKb A q
      let good := sourceGoodPathSet base tops (fun t => (T t).weight Kw D) bad L
      Integrable (sourceBadPathMass tops (fun t => (T t).weight Kw D) bad) (volume.prod volume) ∧
      (∫ z, sourceBadPathMass tops (fun t => (T t).weight Kw D) bad z ∂volume.prod volume) ≤
        (∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-10*L) ∧
      MeasurableSet good ∧ good ⊆ base ∧
      (volume.prod volume) (base \ good) ≤ ENNReal.ofReal
        ((∑ t ∈ tops, (T t).length*(T t).width)*Real.exp (-9*L)) ∧
      ∀ t, ∀ z ∉ bad t, ∀ i : Option (Fin (SourceParameters.blockCount L)),
        z ∉ ((P.actualReferenceData alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
          b v f T assigned t i).restrictPackets
          (P.actualReferenceSelection alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
            b v f g tops T packets assigned hKb t i)).bad
              L A (q+8) (2*q+9) (2*q+11) := by
  obtain ⟨J,hJ⟩ := SourceParameters.exists_reference_window_index C (K:ℝ)
  filter_upwards [eventually_polynomial_uniform_selected_reference_good_path
      hVariation D 3 weightPower q A F cStar cEta CEta cb Cb 1 Lip K Hlabels J
      hD hq hA hF hcStar hcEta hCEta hcb hCb (by norm_num) hLip hgap,
    SourceParameters.eventually_reference_mask_width C Cb,
    eventually_ge_atTop (5:ℝ)] with L harea hmask hL
  intro Kw hKw hKwL N κ τ Label Item _ _ P horder hP alt hAlt oldSlope w hw hwide
    hfrequency hband b hb hb1 hsupport hmotion hlocal hactive v hv f hf hf1 hspectrum haltSpectrum
    g tops T packets assigned hKb hlength hangle hwidth base hbase bad good
  let E := SourceParameters.stepExponent L*SourceParameters.blockCount L
  let B := SourceParameters.branching L
  have hB : 1 ≤ B := SourceParameters.branching_ge_one L
  have hBpow : B = (2:ℝ)^E := SourceParameters.branching_eq_two_pow_product L
  have hB4 : 1 ≤ B^4 := one_le_pow₀ hB
  have hCwide : 1 ≤ C+(K:ℝ)+1 := by linarith [show (0:ℝ) ≤ (K:ℝ) from Nat.cast_nonneg K]
  have hwideError : 1 ≤ (C+(K:ℝ)+1)*((2:ℝ)^E)^4 := by
    rw [← hBpow]
    exact one_le_mul_of_one_le_of_one_le hCwide hB4
  have hwidth' (u) (hu : u ∈ packets) : (Cb+C)*w ≤ (T (assigned u)).width :=
    hmask w _ hw.le (hwidth u hu)
  let R := P.actualReferenceData alt hAlt L oldSlope C w F hw hC hF hwide hfrequency b v f T assigned
  let Q := P.actualReferenceSelection alt hAlt L oldSlope C w F hw hC hF hwide hfrequency
    b v f g tops T packets assigned hKb
  have hdata (t : τ) (_ht : t ∈ tops) (i : Option (Fin (SourceParameters.blockCount L))) :=
    P.recentered_reference_conditions alt hAlt L q oldSlope (T t).slope (T t).length
      (C+B^(if i.isNone then 3 else 2)) w F (C+(K:ℝ)+1) K Lip cStar cEta CEta cb Cb C
      E J K Hlabels hw (add_nonneg hC (pow_nonneg (le_trans zero_le_one hB) _)) hF
      (hwide i) hfrequency horder hP hJ hwideError le_rfl
      (by
        rw [← hBpow]
        apply SourceParameters.reference_window_budget hB hC (Nat.cast_nonneg K)
        apply add_le_add le_rfl
        apply pow_le_pow_right₀ hB
        split <;> omega)
      rfl hband b hb hb1 hsupport hmotion hlocal hactive v hv f hf hf1 hspectrum haltSpectrum
      T packets (P.actualReferencePacketSet L oldSlope C w hw g tops T packets assigned hKb t i)
      assigned (P.actualReferencePacketSet_subset L oldSlope C w hw g tops T packets assigned hKb t i)
      hlength hangle hwidth'
  have ha := harea Kw hKw hKwL τ (Option (Fin (SourceParameters.blockCount L)))
    tops T (fun _ => Finset.univ) N κ Label Item R Q base hbase
    (fun _ _ => by
      simpa only [Real.rpow_ofNat] using
        parentShiftReference_card_le L (by linarith) (source_blockCount_le_square hL))
    (fun t ht i _ => hdata t ht i)
  have heq : (fun t => ⋃ i ∈ (Finset.univ : Finset (Option (Fin (SourceParameters.blockCount L)))),
      ((R t i).restrictPackets (Q t i)).bad L A (q+8) (2*q+9) (2*q+11)) = bad := by
    funext t
    simp only [Finset.mem_univ,iUnion_true,R,Q,bad,actualReferenceBad]
  rw [heq] at ha
  exact ⟨ha.1,ha.2.1,ha.2.2.1,ha.2.2.2.1,ha.2.2.2.2.1,
    fun t z hz i => (ha.2.2.2.2.2 t z hz i (Finset.mem_univ i)).1⟩

end LipschitzHilbert.PacketLatticeData

end

end OAI
