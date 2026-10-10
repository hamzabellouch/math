import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCellTransport
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanActualProbeProfiles
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellProfileRestriction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineSheetAgreement

namespace OAI

/-! # The neighboring law in the coordinates of the linked probe selection -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Set Filter
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsTopologicalGroup G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The actual Haar neighboring law gives the joint coordinate-cube law of
the two original profiles restricted to any compact probe-height set.
Supported pairs remain supported. No new limiting-law assumption is used. -/
theorem restricted_neighbor_cube_law
    [IsTopologicalGroup F.N.carrier]
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases) (scale r : ℕ → ℝ)
    (base step : ℕ → F.N.carrier) (origin next : ℕ → cartanRootIdeal H)
    (horigin : ∀ n, F.ExpN (F.N.equiv (origin n)) = base n)
    (hnext : ∀ n, F.ExpN (F.N.equiv (next n)) = base n * step n)
    (hD : Continuous F.ExpD) (J : ℕ → G → W) (hJ : ∀ n, Continuous (J n))
    (x : ℕ → G) (bD : ℕ → Basis (Fin (finrank ℝ H)) ℝ H)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    (profile : ℕ → F.N.carrier → S) (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * base n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 ∪
      (fun v => v * base n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 →
      ∀ z, (profile n q).val z = rescaledMapProfile (J n) (x n) (F.inclusionN q)
        (r n) (F.profileChart (bD n)) z)
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        E β (scale n) (base n)) (fun q => (profile n q, profile n (q * step n))))
        atTop (𝓝 ν))
    (Z : Set (Fin (finrank ℝ H) → ℝ)) [CompactSpace Z]
    [MeasurableSpace C(Z, W)] [BorelSpace C(Z, W)] [BorelSpace (C(Z, W) × C(Z, W))]
    (f : S × S) (hf : f ∈ (ν : Measure (S × S)).support) :
    let restrictPair := fun g : S × S => (g.1.val.restrict Z, g.2.val.restrict Z)
    let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))
    Tendsto (fun n => ProbabilityMeasure.map (cellProbabilityMeasure volume cube
      (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2)
      (fun y =>
        ((F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n)
          (M.boxBasis T hunimod eW E β (scale n)) (bD n) y (origin n)).restrict Z,
         (F.sampledProbeProfile hD (J n) (hJ n) (x n) (r n)
          (M.boxBasis T hunimod eW E β (scale n)) (bD n) y (next n)).restrict Z)))
      atTop (𝓝 (ProbabilityMeasure.map ν restrictPair)) ∧
      restrictPair f ∈ (ProbabilityMeasure.map ν restrictPair :
        Measure (C(Z, W) × C(Z, W))).support := by
  dsimp only
  let restrictPair := fun g : S × S => (g.1.val.restrict Z, g.2.val.restrict Z)
  have hrp : Continuous restrictPair :=
    ((ContinuousMap.continuous_restrict Z).comp
      (continuous_subtype_val.comp continuous_fst)).prodMk
    ((ContinuousMap.continuous_restrict Z).comp
      (continuous_subtype_val.comp continuous_snd))
  refine ⟨?_, mem_support_map_of_continuous ν restrictPair hrp hf⟩
  let cellLaw := fun n => M.translatedGroupBoxProbability T F hunimod eW haarN chartN
    hchartN b₀ E β (scale n) (base n)
  let raw := fun n q => (profile n q, profile n (q * step n))
  have hraw n : Measurable (raw n) :=
    (hp n).prodMk ((hp n).comp (continuous_id.mul continuous_const).measurable)
  have hlim := sampled_projection_tendsto cellLaw raw hraw ν hν restrictPair hrp
  let cube := Icc (fun _ : Fin (finrank ℝ (cartanRootIdeal H)) => (-1 : ℝ)) (fun _ => (1 : ℝ))
  let sample := fun n y => ((F.ExpN ∘ F.N.equiv) ∘
    (M.boxBasis T hunimod eW E β (scale n)).equivFun.symm) y * base n
  apply hlim.congr'
  filter_upwards [] with n
  have hlaw := M.cube_profile_law_eq_cell_profile_law T F hunimod eW haarN chartN
    hchartN b₀ E β (scale n) (base n) (restrictPair ∘ raw n) (hrp.measurable.comp (hraw n))
  apply hlaw.symm.trans
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.map_congr
  filter_upwards [ae_mem_cellProbabilityMeasure volume cube measurableSet_Icc
    (coordinate_cube_mass zero_lt_one).1 (coordinate_cube_mass zero_lt_one).2] with y hy
  have hm : ((F.ExpN ∘ F.N.equiv) ∘
      (M.boxBasis T hunimod eW E β (scale n)).equivFun.symm) y ∈
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 := by
    rw [groupBox, exponentialCoordinateBox_eq_cube_image _ _ 1 zero_le_one]
    exact ⟨y, hy, rfl⟩
  have h₁ := hactual n (sample n y) (Or.inl ⟨_, hm, rfl⟩)
  have h₂ := hactual n (sample n y * step n) (Or.inr ⟨_, hm, rfl⟩)
  apply Prod.ext <;> apply ContinuousMap.ext <;> intro z
  · change (profile n (sample n y)).val z.val = rescaledMapProfile (J n) (x n)
      (F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n)) y (origin n))
      (r n) (F.profileChart (bD n)) z.val
    rw [h₁]
    simp only [CartanFactorModel.sampledProbeSuffix, sample, Function.comp_apply,
      map_mul, horigin n]
  · change (profile n (sample n y * step n)).val z.val = rescaledMapProfile (J n) (x n)
      (F.sampledProbeSuffix (M.boxBasis T hunimod eW E β (scale n)) y (next n))
      (r n) (F.profileChart (bD n)) z.val
    rw [h₂]
    simp only [CartanFactorModel.sampledProbeSuffix, sample, Function.comp_apply,
      map_mul, hnext, mul_assoc]

end PolycyclicRecognition.CartanWordModel

end

end OAI
