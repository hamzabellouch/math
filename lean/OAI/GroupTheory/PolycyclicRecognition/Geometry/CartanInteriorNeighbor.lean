import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProfileAffinity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSupportedCellAgreement

namespace OAI

/-! # Equality across strictly interior neighboring sheets -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology NNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

theorem cartan_interior_neighbor_profiles_eq
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
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
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
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
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale) (hscale1 : ∀ n, 1 ≤ scale n)
    (ε : ℕ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (k : ℕ → cartanRootIdeal H)
    (hk : ∀ᶠ r : ℕ in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale r)).equivFun (k r)‖ ≤
          Real.exp (scale r * ε r))
    (l : ℕ → cartanRootIdeal H)
    (hl : ∀ᶠ r : ℕ in atTop,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun i => (1 + δ) * M.boxCost T hunimod eW E (β.val i)) (scale r)).equivFun (l r)‖ ≤
          Real.exp (scale r * ε r))
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (profile : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) → S × S)
    (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n y, y ∈ Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)) → ∀ z, (profile n y).1.val z =
      rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
        (F.inclusionN (F.ExpN (F.N.equiv
          ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y))) *
            F.inclusionN (F.ExpN (F.N.equiv (k n))))
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (hactual₂ : ∀ n y, y ∈ Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ)) → ∀ z, (profile n y).2.val z =
      rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
        (F.inclusionN (F.ExpN (F.N.equiv
          ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y))) *
            F.inclusionN (F.ExpN (F.N.equiv (l n))))
        (max (Real.log (scale n)) 0)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm z)))) z)
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure volume (Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
        (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
      (profile n)) atTop (𝓝 ν))
    (U : Set (Fin (finrank ℝ H) → ℝ)) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hUne : U.Nonempty)
    (hUheight : ∀ z ∈ U, eW (heightProjection T.character
      ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
        GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
    (i : Fin M.letterCount) (t : ℕ → ℝ) {B s : ℝ} (hB : 0 ≤ B)
    (htamp : ∀ᶠ n in atTop, |t n| ≤ B * Real.exp (scale n * (s + ε n)))
    (hstep : ∀ n, F.inclusionN (F.ExpN (F.N.equiv (l n))) =
      F.inclusionN (F.ExpN (F.N.equiv (k n))) *
        Exp (t n • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (hinterior : ∃ z ∈ U,
      s < M.weight i ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z)) :
    ∀ f : S × S, f ∈ (ν : Measure (S × S)).support →
      ∀ z ∈ U, f.1.val z = f.2.val z := by
  classical
  let samples : ProbabilityMeasure (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) :=
    cellProbabilityMeasure volume (Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
      (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2
  have hν₁ := sampled_projection_tendsto (fun _ => samples) profile hp ν hν
    Prod.fst continuous_fst
  have hν₂ := sampled_projection_tendsto (fun _ => samples) profile hp ν hν
    Prod.snd continuous_snd
  intro f hf
  have hf₁ := mem_support_map_of_continuous ν Prod.fst continuous_fst hf
  have hf₂ := mem_support_map_of_continuous ν Prod.snd continuous_snd hf
  have ha₁ := M.cartan_supported_profile_affine_sequence T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
    b₀ hE hne β γ hβ hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD scale hscale hmono hscale1 ε hεpos hε k hk rem hdim p x S hS
    (fun n y => (profile n y).1) (fun n => measurable_fst.comp (hp n))
    hactual (ProbabilityMeasure.map ν Prod.fst) hν₁ U hU hconn hUne hUheight σ hσ f.1 hf₁
  have ha₂ := M.cartan_supported_profile_affine_sequence T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
    b₀ hE hne β γ hβ hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD scale hscale hmono hscale1 ε hεpos hε l hl rem hdim p x S hS
    (fun n y => (profile n y).2) (fun n => measurable_snd.comp (hp n))
    hactual₂ (ProbabilityMeasure.map ν Prod.snd) hν₂ U hU hconn hUne hUheight σ hσ f.2 hf₂
  obtain ⟨A₁, b₁, hab₁⟩ := ha₁
  obtain ⟨A₂, b₂, hab₂⟩ := ha₂
  let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
  let q := ((eW.toLinearMap.comp (heightProjection T.character)).comp
    (H.subtype.comp bD.equivFun.symm.toLinearMap)).toContinuousLinearMap
  have hq : Function.Surjective q := by
    intro w
    obtain ⟨v, hv⟩ := (eW.surjective.comp (cartan_height_surjective T H)) w
    refine ⟨bD.equivFun v, ?_⟩
    change eW (heightProjection T.character (bD.equivFun.symm (bD.equivFun v) : H)) = w
    rwa [bD.equivFun.symm_apply_apply]
  let α : (Fin (finrank ℝ H) → ℝ) →L[ℝ] ℝ :=
    ((cartanHeightWeight T H (M.weight i)).comp
      ((heightProjection T.character).comp (H.subtype.comp bD.equivFun.symm.toLinearMap))).toContinuousLinearMap
  have hα (z) : α z = M.weight i (bD.equivFun.symm z) :=
    cartanHeightWeight_projection T H (M.weight i) _
  let O := U ∩ {z | s < α z}
  have hO : IsOpen O := hU.inter (isOpen_lt continuous_const α.continuous)
  have hOne : O.Nonempty := by
    obtain ⟨z, hz, hs⟩ := hinterior
    refine ⟨z, hz, ?_⟩
    change s < α z
    rw [hα]
    exact hs
  have heq : ∀ z ∈ O, f.1.val z = f.2.val z := by
    intro z hz
    let J := fun n g => (π ((p n).val.1 g)).toAdd
    have hJ (n : ℕ) : LipschitzWith (Kπ * Λ) (J n) := hπ.comp (p n).property.1.1
    let suffix := fun n y => F.inclusionN (F.ExpN (F.N.equiv
      ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y))) *
        F.inclusionN (F.ExpN (F.N.equiv (k n)))
    apply M.supported_switch_profiles_agree_on T Exp hExp realize X (boundedBracketWords d) βD
      z i scale hscale ε hε t hB htamp (by
        have hh : s < α z := hz.2
        rw [hα] at hh
        exact hh)
      J hJ x suffix S (fun _ => samples) profile hp ν hν
      (Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))) measurableSet_Icc
      (fun _ => ae_mem_cellProbabilityMeasure volume _ measurableSet_Icc _ _) ?_ ?_ hf
    · intro n y hy w
      simpa only [J, suffix, wordChartPivot, F.compatibleD] using hactual n y hy w
    · intro n y hy w
      simpa only [J, suffix, wordChartPivot, hstep, F.compatibleD, mul_assoc] using hactual₂ n y hy w
  exact (affine_height_profiles_eq_of_open_agreement q hq
    A₁.val.toContinuousLinearEquiv.toContinuousLinearMap
    A₂.val.toContinuousLinearEquiv.toContinuousLinearMap b₁ b₂
    U O hO hOne inter_subset_left f.1.val f.2.val hab₁ hab₂ heq).2.2

end PolycyclicRecognition.CartanWordModel

end

end OAI
