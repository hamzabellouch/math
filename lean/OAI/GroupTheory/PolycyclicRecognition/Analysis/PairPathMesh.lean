import OAI.GroupTheory.PolycyclicRecognition.Geometry.PairHeightCocycle
import OAI.GroupTheory.PolycyclicRecognition.Analysis.StationaryMesh
import Mathlib.Topology.Order.Compact

namespace OAI

/-! # Fixed meshes and height control of image paths

The mesh depends only on the requested error and the common path-length
constant, not on the scale or on the endpoint. The actual `L²` height cocycle
controls its finitely many samples; the common Lipschitz bounds then control
every point of the image path.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace PolycyclicRecognition

/-- A single finite mesh for the unit path interval. -/
theorem exists_fixed_path_mesh {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : Finset (Set.Icc (0 : ℝ) 1),
      ∀ t, ∃ u ∈ S, dist t u ≤ δ := by
  classical
  obtain ⟨S, _, hS, hcover⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) 1)).finite_cover_balls hδ
  refine ⟨hS.toFinset, ?_⟩
  intro t
  obtain ⟨u, hu, htu⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ t))
  exact ⟨u, hS.mem_toFinset.mpr hu, (Metric.mem_ball.mp htu).le⟩

variable {G W T : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [PseudoMetricSpace T]
  {Λ : ℝ≥0}

omit [ProperSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G] in
/-- Sampled height control extends to the whole image path, with the precise
linear loss furnished by the Lipschitz constants and mesh spacing. -/
theorem image_path_height_control
    (p : NormalizedPair G Λ) (π : G →* Multiplicative W) (l : G →* Multiplicative W)
    {Lπ L r δ η ε : ℝ} (hLπ : 0 ≤ Lπ) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ Lπ * dist x y)
    (γ : T → G) (hγ : ∀ t u, dist (γ t) (γ u) ≤ L * r * dist t u)
    (S : Finset T) (hmesh : ∀ t, ∃ u ∈ S, dist t u ≤ δ)
    (E : Set W)
    (hheight : ∀ u ∈ S, ∃ w ∈ E, ‖(l (γ u)).toAdd - r • w‖ ≤ ε * r)
    (herror : ∀ u ∈ S, ‖pairHeight π (γ u) p - (l (γ u)).toAdd‖ ≤ η * r) :
    ∀ t, ∃ w ∈ E,
      ‖pairHeight π (γ t) p - r • w‖ ≤ (Lπ * Λ * L * δ + η + ε) * r := by
  intro t
  obtain ⟨u, hu, htu⟩ := hmesh t
  obtain ⟨w, hw, hwu⟩ := hheight u hu
  refine ⟨w, hw, ?_⟩
  have hdist : dist (γ t) (γ u) ≤ L * r * δ :=
    (hγ t u).trans (mul_le_mul_of_nonneg_left htu (mul_nonneg hL hr))
  have hF := p.property.1.1.dist_le_mul (γ t) (γ u)
  have hp : ‖pairHeight π (γ t) p - pairHeight π (γ u) p‖ ≤ Lπ * Λ * (L * r * δ) := by
    apply (hπ (p.val.1 (γ t)) (p.val.1 (γ u))).trans
    calc
      Lπ * dist (p.val.1 (γ t)) (p.val.1 (γ u)) ≤ Lπ * (Λ * dist (γ t) (γ u)) :=
        mul_le_mul_of_nonneg_left hF hLπ
      _ ≤ Lπ * (Λ * (L * r * δ)) := by gcongr
      _ = _ := by ring
  have ht (a b c : W) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
    simpa only [dist_eq_norm] using dist_triangle a b c
  calc
    ‖pairHeight π (γ t) p - r • w‖ ≤
        ‖pairHeight π (γ t) p - pairHeight π (γ u) p‖ +
          ‖pairHeight π (γ u) p - r • w‖ := ht _ _ _
    _ ≤ Lπ * Λ * (L * r * δ) +
        (‖pairHeight π (γ u) p - (l (γ u)).toAdd‖ + ‖(l (γ u)).toAdd - r • w‖) :=
      add_le_add hp (ht _ _ _)
    _ ≤ Lπ * Λ * (L * r * δ) + (η * r + ε * r) :=
      add_le_add le_rfl (add_le_add (herror u hu) hwu)
    _ = _ := by ring

variable [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]

omit [IsIsometricSMul G G] in
/-- The norm in the actual Hilbert space equals the `L²` seminorm of the
pointwise height error; there is no choice of pointwise representatives here. -/
theorem eLpNorm_pairHeight_error
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (l : G →* Multiplicative W) (g : G) :
    eLpNorm (fun p : NormalizedPair G Λ => pairHeight π g p - (l g).toAdd) 2 μ =
      ENNReal.ofReal ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ := by
  rw [ofReal_norm, Lp.enorm_def]
  apply eLpNorm_congr_ae
  exact ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (pairHeightProfile π hπ g)).sub
    (Lp.coeFn_const 2 μ (l g).toAdd)).symm.trans
      (Lp.coeFn_sub _ _).symm

omit [IsIsometricSMul G G] in
/-- The fixed finite-mesh selection for the actual normalized maps. -/
theorem exists_pair_good_on_mesh
    {I Y : Type*} [Fintype I] [MeasurableSpace Y]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    (γ : Y → I → G) (hγ : ∀ i, Measurable (fun y => γ y i))
    {a : ℝ} {η t : ℝ≥0∞} (hη : η ≠ 0) (hηtop : η ≠ ∞)
    (hbound : ∀ i y, ‖pairHeightL2 μ π hπ (γ y i) -
      Lp.const 2 μ (l (γ y i)).toAdd‖ ≤ a)
    (hsmall : (Fintype.card I : ℝ≥0∞) * (η⁻¹ ^ 2 * (ENNReal.ofReal a) ^ 2) < t) :
    ∃ p : NormalizedPair G Λ,
      ν {y | ∃ i, η ≤ ‖pairHeight π (γ y i) p - (l (γ y i)).toAdd‖ₑ} < t := by
  let f : I → NormalizedPair G Λ × Y → W :=
    fun i z => pairHeight π (γ z.2 i) z.1 - (l (γ z.2 i)).toAdd
  have hf : ∀ i, Measurable (f i) := by
    intro i
    exact ((continuous_pairHeight π hπ).measurable.comp
      (((hγ i).comp measurable_snd).prodMk measurable_fst)).sub
      (hl.measurable.comp ((hγ i).comp measurable_snd))
  apply exists_good_mesh_fiber μ ν f hf hη hηtop _ hsmall
  intro i y
  exact (eLpNorm_pairHeight_error μ π hπ l (γ y i)).le.trans
    (ENNReal.ofReal_le_ofReal (hbound i y))

end PolycyclicRecognition

end

end OAI
