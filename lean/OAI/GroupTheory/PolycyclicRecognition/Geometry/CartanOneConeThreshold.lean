import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborRowOffset
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFixedPolarTargets
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFixedSamplingGeometry
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCanonicalPolarSamplers
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanContactStepBridge
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SmallFactorCell
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanOffsetThreshold

namespace OAI

/-! # A polar trace inequality uniformly before choosing a neighboring row -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal BigOperators

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [IsTopologicalGroup F.D.carrier] [SecondCountableTopology F.D.carrier]
  [Fintype I] [DecidableEq I] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

local notation "Eall" => M.samplingPolytope T hunimod eW

/-- The finite cone and label are fixed before the scale, maps or weak law.
All sampling, contact and target-volume data are constructed from the
published exponential inputs and the actual Cartan models. -/
theorem exists_one_cone_offset_threshold
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SFinite νD]
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
      [ErgodicSMul G (NormalizedPair G Λ) μ],
      ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (hΛ : 0 < (Λ : ℝ)) {Kπ : ℝ≥0}
    (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (M.boxCost T hunimod eW Eall) γ.val)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (hDletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords d)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hmN : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (pivot : Fin M.letterCount → H) (i : Fin M.letterCount)
    (hcanonical : cartanHeightSection T H (heightProjection T.character (pivot i)) = pivot i)
    (hunit : ‖eW (heightProjection T.character (pivot i))‖ = 1)
    (hcontact : ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap
      (eW (heightProjection T.character (pivot i))) =
        ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖)
    (hpositive : 0 < M.weight i (pivot i))
    {lo hi c B : ℝ} (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hB : 0 ≤ B)
    (hcost : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW Eall w ∧
      M.boxCost T hunimod eW Eall w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (σchamber : Fin M.letterCount → Bool)
    (hσchamber : (weightChamber (fun j =>
      ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap) σchamber).Nonempty)
    (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
    (K : ProperCone ℝ (StrongDual ℝ W))
    (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
    (hiK : ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K)
    (A : templateSymmetryGroup (M.supportIn T hunimod eW))
    (Ds : M.MeasuredCone F (heightConePreimage T eW K))
    (dynkinI : NilpotentDynkinExpansionInput Ds.I.modelSpace Ds.I.carrier)
    (haarI : NilpotentExponentialHaarInput Ds.I.modelSpace Ds.I.carrier)
    (Dt₀ : M.MeasuredCone F (heightConePreimage T eW (transformedPolarCone K A.val)))
    (haarQt : NilpotentExponentialHaarInput Dt₀.Q.modelSpace Dt₀.Q.carrier)
    (haarIt : NilpotentExponentialHaarInput Dt₀.I.modelSpace Dt₀.I.carrier) :
    ∃ coeff : Fin M.letterCount → ℕ,
      (∀ j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∉
        transformedPolarCone K A.val → coeff j = 0) ∧
      (∀ j, ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap ∈
        transformedPolarCone K A.val → 0 < coeff j) ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ row : AffineNeighborRow T M F hunimod eW π bN Eall γ X βD
        haarN chartN hchartN pivot c B δ Profiles (Λ := Λ),
      row.mode = i → row.label₁ = A → row.label₂ = A →
        (∑ j, (coeff j : ℝ) • ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)
          (row.offset₂ - row.offset₁) ≤ 0 := by
  classical
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  let : LocallyCompactSpace F.N.carrier := F.closedN.locallyCompactSpace
  let : LocallyCompactSpace F.D.carrier := F.closedD.locallyCompactSpace
  let : IsTopologicalGroup Ds.I.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, Ds.I.modelSpace)) ⊤
  let : IsTopologicalGroup Dt₀.Q.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, Dt₀.Q.modelSpace)) ⊤
  let bIs := finBasis ℝ (M.coneWordIdeal (heightConePreimage T eW K))
  let bIt := finBasis ℝ (M.coneWordIdeal (heightConePreimage T eW (transformedPolarCone K A.val)))
  let icoord := ((bIs.map Ds.I.equiv.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph).trans Ds.maps.chartI
  let : SecondCountableTopology Ds.I.carrier := icoord.symm.secondCountableTopology
  obtain ⟨U, hU, hUone, hsmall⟩ := exists_small_factor_cell F.inclusionN F.inclusionD
    F.closedN.continuous F.closedD.continuous
  obtain ⟨ε₀, δg, hε₀, hδg, hgeometry⟩ := M.exists_fixed_polar_sampling_geometry
    T hunimod eW i _ hunit hcontact K hiK hc
  let ε := ε₀
  have hε : 0 < ε := hε₀
  obtain ⟨actionQ, act, μQ, coeff, βtarget, hμQ, hact, hout, hin, hHaar,
      hβtarget, δtarget, hδtarget, hregions⟩ :=
    Dt₀.exists_fixed_polar_target_regions M F T hunimod eW hExp realize
      hbijN hbijD dynkinN dynkinD chartN hchartN chartD hchartD π hπExp hpath
      Kπ.coe_nonneg (fun x y => by simpa only [dist_eq_norm] using hπ.dist_le_mul x y)
      K A.val hK haarQt haarIt haarD νD bN bIt γ hU hε
  let Ct := heightConePreimage (H := H) T eW (transformedPolarCone K A.val)
  let Dt := Dt₀.withQuotientHaar M F Ct μQ hμQ
  let : IsTopologicalGroup Dt.Q.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, Dt.Q.modelSpace)) ⊤
  let μN := Dt.sectionMeasure M F Ct Dt.maps.sectionMap Dt.maps.section_rightInverse
  let : μN.IsHaarMeasure := Dt.sectionMeasure_isHaar M F Ct
    Dt.maps.sectionMap Dt.maps.section_rightInverse
  obtain ⟨hUmeas, hUzero, hUtop⟩ := small_factor_cell_measure μN νD hU ⟨1, hUone⟩
  obtain ⟨β, bQ, lift, Rbox, δs, hlift, hβ, hRbox, hδs, hsamplers⟩ :=
    Ds.exists_canonical_polar_samplers T M F hunimod eW K hExp realize haarN dynkinN
      hbijN chartN hchartN dynkinI haarI bN bIs i hiK (pivot i) hpositive
      (c + 1) B ε (by linarith) hB hε
  obtain ⟨Ca, Cb, hCa, hCb, hbridge⟩ := M.exists_uniform_contact_step_bridge (I := Ds.I.carrier)
    T F hunimod eW (heightConePreimage T eW K) hExp realize haarN haarD dynkinN
      hbijN chartN hchartN bN i (pivot i) hpositive (by linarith : 0 ≤ c + 1) hB
  obtain ⟨δ₀, η, hδ₀, hη, hδsource, hthreshold⟩ :=
    exists_source_offset_threshold hCa hCb hΛ.le (by linarith : 0 ≤ c + 1)
      hδtarget (lt_min hδg hδs)
  refine ⟨coeff, hout, hin, δ₀, hδ₀, ?_⟩
  intro δ hδ hd row hmode hlabel₁ hlabel₂
  have hδg' : δ ≤ δg := (hd.trans hδsource).trans (min_le_left _ _)
  have hδs' : δ ≤ δs := (hd.trans hδsource).trans (min_le_right _ _)
  obtain ⟨hδc, herror⟩ := hthreshold δ hδ hd
  obtain ⟨u, hu, hmono, hs1⟩ := exists_strictMono_scale_subsequence row.scale row.grows
  let row₁ := row.reindex T M F hunimod eW π bN Eall γ X βD
    haarN chartN hchartN pivot c B δ Profiles u hu
  have htime₁ (n) : |row₁.time n| ≤ row₁.radius n * Real.exp
      ((M.weight i (pivot i) + δ * B) * row₁.scale n) := by
    change |row.time (u n)| ≤ row.radius (u n) * Real.exp
      ((M.weight i (pivot i) + δ * B) * row.scale (u n))
    simpa only [hmode] using row.time_bound (u n)
  have hroot₁ (n) : F.inclusionN (row₁.step n) =
      Exp (row₁.time n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    change F.inclusionN (row.step (u n)) =
      Exp (row.time (u n) • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))
    simpa only [hmode] using row.root_step (u n)
  obtain ⟨n₀, P, hbQ, hL, hconj⟩ := hsamplers δ hδ hδs'
    row₁.scale hmono row₁.grows (fun n => zero_lt_one.trans_le (hs1 n))
    row₁.radius row₁.time row₁.radius_subexponential htime₁ row₁.step hroot₁
  have htail : StrictMono (fun n : ℕ => n + n₀) := by
    intro m n hmn
    exact Nat.add_lt_add_right hmn n₀
  let row₂ := row₁.reindex T M F hunimod eW π bN Eall γ X βD
    haarN chartN hchartN pivot c B δ Profiles (fun n => n + n₀) htail
  have hmono₂ : StrictMono row₂.scale := hmono.comp htail
  have hs₂ (n) : 1 ≤ row₂.scale n := hs1 (n + n₀)
  let p := eW (heightProjection T.character (pivot i))
  let w := (1 - (c + 1) * δ) • p
  let contact := (1 - (c + 1) * δ) • pivot i
  let h := fun n => (row₂.scale n * (1 - (c + 1) * δ)) • pivot i
  let S := fun n => M.sourceDilation T F hbijN chartN hchartN dynkinN (h n)
  obtain ⟨hfactor, hgeom, hV, hVconv, hVinside, hVall⟩ := hgeometry ε hε le_rfl δ hδ hδg'
  let V := samplingHeightDomain
    (fun j => ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap) (1 - c * δ)
  have hcontactHeight : eW (heightProjection T.character contact) = w := by
    simp only [contact, w, p, SetLike.val_smul, map_smul]
  have hsection : cartanHeightSection T H (eW.symm w) = contact := by
    simp only [w, p, contact, map_smul, eW.symm_apply_apply, hcanonical]
  have hS (n) (v : cartanRootIdeal H) : S n (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H
        (row₂.scale n • cartanHeightSection T H (eW.symm w)) v)) := by
    rw [hsection]
    simpa only [S, h, contact, smul_smul] using
      M.sourceDilation_apply_exp T F hbijN chartN hchartN dynkinN (h n) v
  have hb := hbridge (Ds.maps.expI ∘ Ds.I.equiv) (normalizedPolarTemplates K ε)
    (fun _ => β) P.ambient (fun j => ε * M.polarProbeWidths T hunimod eW K j)
    row₂.scale _ Ds.maps.inclusion P.tiles P.anchor P.chain Ds.Q Ds.maps.chartQ
    Ds.maps.quotient Ds.maps.inclusion_closed Ds.maps.inclusion_range
    row₂.radius row₂.grows (fun n => zero_le_one.trans (hs₂ n)) row₂.radius_nonneg
    row₂.radius_subexponential η hη δ hδ.le hδc row₂.base row₂.step row₂.time
    (fun n => by
      change |row₁.time (n + n₀)| ≤ row₁.radius (n + n₀) * Real.exp
        ((M.weight i (pivot i) + B * δ) * row₁.scale (n + n₀))
      simpa only [mul_comm B δ] using htime₁ (n + n₀))
    (fun n => hroot₁ (n + n₀))
  have hE : IsCompact Eall := M.isCompact_samplingPolytope T hunimod eW
  have hne : (Eall).Nonempty := ⟨0, by
    intro j
    simpa only [map_zero] using norm_nonneg (((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)⟩
  have hN : Continuous F.ExpN := funext hchartN ▸ chartN.continuous
  have hD : Continuous F.ExpD := funext hchartD ▸ chartD.continuous
  have hlabels : row₂.label₂ = row₂.label₁ := hlabel₂.trans hlabel₁.symm
  exact AffineNeighborRow.polar_offset_nonpos
    (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW)
    (π := π) (bN := bN) («Eall» := Eall) (γ := γ) (X := X) (βD := βD)
    (haarN := haarN) (chartN := chartN) (hchartN := hchartN)
    (pivotRoots := pivot) (c := c) (B := B) (δ := δ) (Profiles := Profiles)
    (row := row₂) (scale := row₂.scale) (A := A) (hscale := rfl) (hlabel := hlabel₁) (K := K) (D := Ds) (β := β) (Rbox := Rbox) (P := P)
    (w := w) (S := S) (βtarget := βtarget) (Dt := Dt)
    (hExp := hExp) (realize := realize) (haarD := haarD)
    (dynkinN := dynkinN) (dynkinD := dynkinD) (m := m)
    (hπExp := hπExp) (hdec := hdec) (hvan := hvan) (hΛ := hΛ)
    (hπ := hπ) (hpath := hpath) (hE := hE) (hne := hne) (γaux := γ)
    (hβ := hγ) (hweights := M.sampling_weightSupport_pos T hunimod eW)
    (hδ := hδ) (hc := hc) (hhi := hhi) (ht := by linarith)
    (hcost := hcost) (hgap := hgap) (hDnil := hDnil) (hDletters := hDletters)
    (bD₀ := bD₀) (hβD := hβD) (aN := aN) (hmN := hmN) (aD := aD) (hmD := hmD)
    (hmono := hmono₂) (hscale1 := hs₂)
    (hBE := (hgeom 1).2.2.2.trans hVall)
    (hφsource := hconj) (rem := rem) (hdim := hdim) (hN := hN) (hD := hD)
    (pivot := contact) (V := V) (hV := hV) (hVconv := hVconv)
    (hEc := fun k => (hgeom k).1) (hEconv := fun k => (hgeom k).2.1)
    (hpivot := fun k => by simpa only [hcontactHeight, polarSamplingTemplates, normalizedPolarTemplates, w, p] using (hgeom k).2.2.1)
    (hEV := fun k => (hgeom k).2.2.2) (hVheight := hVinside)
    (σchamber := σchamber) (hσchamber := hσchamber) (hlabels := hlabels)
    (haarI := haarI) (bI := bIs) (hε := hε) (hRbox := hRbox.le) (hβsource := hβ)
    (bItarget := bIt) (hβtarget := hβtarget) (hS := hS)
    (Dbridge := Ca * δ + Cb * η) (δtarget := δtarget) (hδtarget := hδtarget) (hDb := herror)
    (hbridge := by
      filter_upwards [hb] with n hn
      intro y
      simpa only [S, h, contact, smul_smul, SetLike.val_smul] using hn ⟨y.val, y.property⟩)
    (νD := νD) (actionQ := actionQ) (act := act) (hact := hact)
    (cell := U) (hcell := hUmeas) (hcell0 := hUzero) (hcelltop := hUtop) (hsmall := hsmall)
    (regionFactory := fun η hη0 hη Cp hCp => by
      convert hregions row₂.scale hmono₂ row₂.grows hs₂ w δtarget hδtarget le_rfl η hη0 hη Cp hCp using 1 <;>
        simp only [hcontactHeight, polarSamplingTemplates, normalizedPolarTemplates,
          Dt, Ct, MeasuredCone.withQuotientHaar, MeasuredCone.kernelMeasure] <;> rfl)
    (ell := ∑ j, (coeff j : ℝ) • ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)
    (hHaar := hHaar)

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "exists_one_cone_offset_threshold"

end PolycyclicRecognition.CartanWordModel

end

end OAI
