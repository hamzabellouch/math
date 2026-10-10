import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborSamplingRow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCellTransport
import OAI.GroupTheory.PolycyclicRecognition.Analysis.FiniteModeProfileChains

namespace OAI

/-! # The original neighboring comparison along finite root chains -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set TopologicalSpace
open scoped Manifold Topology ENNReal NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [Fintype I] [DecidableEq I]
  (π : G →* Multiplicative W)
  (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  (cell : Set W) (β : M.Bases)
  (X : I → H) {d : ℕ} (βD : WordBasisSelections X (boundedBracketWords d))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (pivot : Fin M.letterCount → H) (B δ : ℝ)
  (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
  [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
  [CompactSpace Profiles] [MetrizableSpace Profiles]
  {Λ : ℝ≥0}

omit [SecondCountableTopology F.N.carrier] [BorelSpace (Profiles × Profiles)] in
/-- The proved neighboring-sheet comparison propagates along a bounded
root word. Its root index may change at each scale and each edge. -/
theorem neighbor_chain_concentration
    (Z : Set (Fin (finrank ℝ H) → ℝ)) [CompactSpace Z]
    (hneighbor : ∀ row : NeighborSamplingRow T M F hunimod eW π bN cell β X βD
      haarN chartN hchartN pivot B δ Profiles (Λ := Λ),
      ∀ z ∈ Z, row.point.1.val z = row.point.2.val z)
    (scale : ℕ → ℝ) (hgrows : Tendsto scale atTop atTop)
    (hmono : StrictMono scale) (hs1 : ∀ n, 1 ≤ scale n)
    (pair : ℕ → NormalizedPair G Λ) (center : ℕ → G)
    (radius : ℕ → ℝ) (hr0 : ∀ n, 0 ≤ radius n)
    (hr : HasSubexponentialUpperBoundSeq scale radius)
    {N : ℕ} (base : ℕ → Fin (N + 1) → F.N.carrier)
    (step : ℕ → Fin N → F.N.carrier)
    (hbase : ∀ n j, base n j ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' cell) β (scale n) (radius n))
    (hstep : ∀ n j, step n j ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' cell) β (scale n) (radius n))
    (hnext : ∀ n j, base n j.succ = base n j.castSucc * step n j)
    (mode : ℕ → Fin N → Fin M.letterCount) (time : ℕ → Fin N → ℝ)
    (htime : ∀ n j, |time n j| ≤ radius n * Real.exp
      ((M.weight (mode n j) (pivot (mode n j)) + δ * B) * scale n))
    (hroot : ∀ n j, F.inclusionN (step n j) =
      Exp (time n j • (M.letter (mode n j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (profile : ℕ → F.N.carrier → Profiles) (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n j q, q ∈ (fun v => v * base n j) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) cell β (scale n) 1 → ∀ z,
      (profile n q).val z = rescaledMapProfile
        (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (scale n)) 0))) z)
    (j : Fin (N + 1)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => (M.translatedGroupBoxProbability T F hunimod eW
      haarN chartN hchartN bN cell β (scale n) 1 : Measure F.N.carrier)
      {q | η ≤ dist ((profile n (q * base n j)).val.restrict Z)
        ((profile n (q * base n 0)).val.restrict Z)}) atTop (𝓝 0) := by
  let μ := fun n => M.translatedGroupBoxProbability T F hunimod eW
    haarN chartN hchartN bN cell β (scale n) 1
  let chain := fun n q (j : Fin (N + 1)) => profile n (q * base n j)
  have hc (n) : Measurable (chain n) := Measurable.of_eval (fun j =>
    (hp n).comp (measurable_id.mul_const _))
  have hedge (edge : Fin N) (ι : ℕ → ℕ) (hι : StrictMono ι)
      (ν : ProbabilityMeasure (Profiles × Profiles))
      (hν : Tendsto (fun n => ProbabilityMeasure.map
        (ProbabilityMeasure.map (μ (ι n)) (chain (ι n)))
        (fun f => (f edge.castSucc, f edge.succ))) atTop (𝓝 ν)) :
      ∀ f ∈ (ν : Measure (Profiles × Profiles)).support,
        ∀ z ∈ Z, f.1.val z = f.2.val z := by
    obtain ⟨i, u, hu, hmode⟩ := exists_constant_mode_subsequence (fun n => mode (ι n) edge)
    let v := ι ∘ u
    have hv : StrictMono v := hι.comp hu
    have hmarg (n) : ProbabilityMeasure.map
        (ProbabilityMeasure.map (μ n) (chain n)) (fun f => (f edge.castSucc, f edge.succ)) =
        ProbabilityMeasure.map
          (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN bN
            cell β (scale n) (base n edge.castSucc))
          (fun q => (profile n q, profile n (q * step n edge))) := by
      have hpair : Measurable (fun q => (profile n q, profile n (q * step n edge))) :=
        (hp n).prodMk ((hp n).comp (measurable_id.mul_const _))
      have htrans := M.translated_groupBox_profile_law_mul_right T F hunimod eW
        haarN chartN hchartN bN cell β (scale n) 1 (base n edge.castSucc) _ hpair
      rw [one_mul] at htrans
      rw [← htrans]
      apply ProbabilityMeasure.toMeasure_injective
      rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
        ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map (by fun_prop) (hc n)]
      congr 1
      funext q
      simp only [Function.comp_apply, chain, hnext, mul_assoc]
    have hconv : Tendsto (fun n => ProbabilityMeasure.map
        (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN bN
          cell β (scale (v n)) (base (v n) edge.castSucc))
        (fun q => (profile (v n) q, profile (v n) (q * step (v n) edge))))
        atTop (𝓝 ν) := by
      apply (hν.comp hu.tendsto_atTop).congr'
      filter_upwards [] with n
      exact hmarg (v n)
    intro f hf z hz
    let row : NeighborSamplingRow T M F hunimod eW π bN cell β X βD
        haarN chartN hchartN pivot B δ Profiles (Λ := Λ) := {
      scale := scale ∘ v
      grows := hgrows.comp hv.tendsto_atTop
      strict_mono := hmono.comp hv
      scale_ge_one := fun n => hs1 (v n)
      pair := pair ∘ v
      center := center ∘ v
      radius := radius ∘ v
      radius_nonneg := fun n => hr0 (v n)
      radius_subexponential := fun ε hε => hv.tendsto_atTop.eventually (hr ε hε)
      base := fun n => base (v n) edge.castSucc
      step := fun n => step (v n) edge
      base_mem := fun n => hbase (v n) edge.castSucc
      step_mem := fun n => hstep (v n) edge
      mode := i
      time := fun n => time (v n) edge
      time_bound := by
        intro n
        simpa only [v, Function.comp_apply, hmode n] using htime (v n) edge
      root_step := by
        intro n
        simpa only [v, Function.comp_apply, hmode n] using hroot (v n) edge
      profile := profile ∘ v
      measurable_profile := fun n => hp (v n)
      actual := by
        intro n q hq w
        rcases hq with hq | hq
        · exact hactual (v n) edge.castSucc q hq w
        · apply hactual (v n) edge.succ q _ w
          simpa only [hnext, mul_assoc, Function.comp_apply] using hq
      law := ν
      converges := hconv
      point := f
      supported := hf }
    exact hneighbor row z hz
  have hprob := profile_chain_concentration Profiles Z N
    (fun n => ProbabilityMeasure.map (μ n) (chain n)) hedge j hη
  apply hprob.congr'
  filter_upwards [] with n
  apply ProbabilityMeasure.map_apply' (μ n) (hc n).aemeasurable
  have hcoord (i : Fin (N + 1)) :
      Continuous (fun f : Fin (N + 1) → Profiles => (f i).val.restrict Z) :=
    (ContinuousMap.continuous_restrict Z).comp
      (continuous_subtype_val.comp (continuous_apply i))
  exact (isClosed_le continuous_const ((hcoord j).dist (hcoord 0))).measurableSet

end PolycyclicRecognition.CartanWordModel

end

end OAI
