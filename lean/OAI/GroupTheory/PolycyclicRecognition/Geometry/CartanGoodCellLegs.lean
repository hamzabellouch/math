import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartPivot
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorCharts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCellFlowLegs
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialGoodCells
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxExponents
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoordinateChartSampling

namespace OAI

/-! # Good physical legs on the actual translated Cartan Haar cells -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Set Filter
open scoped Manifold Topology ENNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Fintype I] [DecidableEq I]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

omit [SimplyConnectedSpace G] [FiniteDimensional ℝ W] in
/-- A supported coordinate profile supplies actual good group sheets. Their
relative Haar mass, their positivity and every physical segment leg are
proved together, with the original translated cell retained. -/
theorem exists_good_cartan_cell_legs_sequence
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (k : ℕ → cartanRootIdeal H)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ u v, F.ExpD (finiteDynkinPolynomial aD ![u, v]) = F.ExpD u * F.ExpD v)
    (J : ℕ → G → W) (x : ℕ → G)
    (C : Set (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ)) (hC : MeasurableSet C)
    (hC0 : volume C ≠ 0) (hCfin : volume C ≠ ∞)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (profile : ℕ → (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) → S)
    (hp : ∀ n, Measurable (profile n)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure volume C hC0 hCfin) (profile n)) atTop (𝓝 ν))
    (v : H) (z : Fin (finrank ℝ H) → ℝ) (T₀ : ℝ)
    (U : Set (Fin (finrank ℝ H) → ℝ)) (hU : IsOpen U)
    (hseg : ∀ t ∈ Icc 0 T₀,
      dynkinFlowMap aD
        (gradedCoordinateBracket (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)))
        (gradedGenerator (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) 1 v) (z, t) ∈ U)
    (hactual : ∀ n y, y ∈ C → ∀ w, (profile n y).val w =
      rescaledMapProfile (J n) (x n)
        (F.inclusionN (F.ExpN (F.N.equiv
            ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y))) *
          F.inclusionN (F.ExpN (F.N.equiv (k n))))
        (max (Real.log (scale n)) 0)
        (fun w => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) βD)
            (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (max (Real.log (scale n)) 0)).equivFun.symm w)))) w)
    {f : S} (hf : f ∈ (ν : Measure S).support) :
    let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
    let sample := fun n y => F.ExpN (F.N.equiv
      ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y)) * F.ExpN (F.N.equiv (k n))
    let b := WordBasisSelections.basis X (boundedBracketWords d) βD
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
    ∃ (A : ℕ → Set F.N.carrier) (ζ : ℕ → ℝ),
      (∀ n, MeasurableSet (A n)) ∧ (∀ n, A n ⊆ sample n '' C) ∧
      (∀ n, 0 < (μ (A n)).toReal) ∧ (∀ n, 0 < ζ n) ∧ Tendsto ζ atTop (𝓝 0) ∧
      HasSubexponentialLowerBoundSeq scale
        (fun n => (μ (A n)).toReal / (μ (sample n '' C)).toReal) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ u ∈ A n, ∀ t ∈ Icc 0 T₀,
        ‖J n ((x n * F.inclusionN u * F.inclusionD (F.ExpD (F.D.equiv
            ((exponentialRescaleBasis b cost (max (Real.log (scale n)) 0)).equivFun.symm z)))) *
              F.inclusionD (F.ExpD (F.D.equiv ((scale n * t) • v)))) -
            J n (x n) - scale n • f.val
              (dynkinFlowMap aD (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v) (z, t))‖ ≤
          scale n * (ζ n + η) := by
  dsimp only
  let μ := Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume
  let sample := fun n y => F.ExpN (F.N.equiv
    ((M.boxBasis T hunimod eW E β (scale n)).equivFun.symm y)) * F.ExpN (F.N.equiv (k n))
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)
  have hweight := maximizing_word_basis_bracket_weight X hDnil bD₀ (fun _ => 1) βD hβD
  have hv : ∀ j, b.repr v j ≠ 0 → (1 : ℝ) ≤ cost j := by
    intro j _
    have hlen (w : FreeMagma I) : 1 ≤ bracketWordLength w := by
      induction w using FreeMagma.rec with
      | of i => simp [bracketWordLength]
      | mul u w hu hw => simp only [bracketWordLength]; omega
    dsimp only [cost]
    rw [bracketWordExponent_one]
    exact_mod_cast hlen (βD.val j)
  obtain ⟨B, ζ, hB, hBC, hζ, hζlim, hmass, hBpos, hlegs⟩ :=
    exists_good_cell_rescaled_flow_legs_sequence (F.ExpD ∘ F.D.equiv) b cost aD
      (model_binary_dynkin F.D.equiv F.ExpD aD hmD) hweight v hv
      (fun n y => F.inclusionN (sample n y)) F.inclusionD J x S scale hscale
      volume (fun _ => C) (fun _ => hC) (fun _ => hC0) (fun _ => hCfin)
      profile hp ν hν (by simpa only [sample, b, cost, Function.comp_apply, map_mul] using hactual) z T₀ U hU hseg hf
  let A := fun n => sample n '' B n
  have hnil : LieRing.IsNilpotent (cartanRootIdeal H) :=
    (LieModule.isNilpotent_iff ℝ _ _).mpr ⟨M.bound, M.bound_zero⟩
  have hratio (n : ℕ) : (μ (A n)).toReal / (μ (sample n '' C)).toReal =
      (volume (B n)).toReal / (volume C).toReal :=
    translated_exponential_cell_ratio haarN F.N.equiv hnil F.ExpN F.isExpN chartN hchartN
      M.letter M.wordList b₀ β (M.boxCost T hunimod eW E) (scale n)
      (F.ExpN (F.N.equiv (k n))) (B n) C
  refine ⟨A, ζ, ?_, fun n => image_mono (hBC n), ?_, hζ, hζlim, ?_, ?_⟩
  · intro n
    exact (measurableEmbedding_translated_exponential_basis F.N.equiv F.ExpN chartN hchartN
      (M.boxBasis T hunimod eW E β (scale n)) (F.ExpN (F.N.equiv (k n)))).measurableSet_image.mpr (hB n)
  · intro n
    have hh := div_pos (hBpos n) (ENNReal.toReal_pos hC0 hCfin)
    rw [← hratio n] at hh
    exact (div_pos_iff.mp hh).resolve_right (fun h => ENNReal.toReal_nonneg.not_gt h.1) |>.1
  · change HasSubexponentialLowerBoundSeq scale
      (fun n => (μ (A n)).toReal / (μ (sample n '' C)).toReal)
    simpa only [hratio] using hmass
  · intro η hη
    filter_upwards [hlegs η hη] with n hn u hu t ht
    obtain ⟨y, hy, rfl⟩ := hu
    exact hn y hy t ht

end PolycyclicRecognition.CartanWordModel

end

end OAI
