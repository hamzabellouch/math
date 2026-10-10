import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairAction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.StationaryCentered

namespace OAI

/-!+# Height evaluation on the compact pair space

The normalized action makes evaluation of a continuous height homomorphism
an actual continuous `L²` cocycle. The stationary slope estimate therefore
applies to this concrete cocycle.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {Λ : ℝ≥0}

/-- Height evaluation of the forward map of a normalized pair. -/
def pairHeight (π : G →* Multiplicative W) (g : G) (p : NormalizedPair G Λ) : W :=
  (π (p.val.1 g)).toAdd

omit [NormedSpace ℝ W] [ProperSpace G] in
theorem pairHeight_cocycle (π : G →* Multiplicative W) (g h : G)
    (p : NormalizedPair G Λ) :
    pairHeight π (g * h) p = pairHeight π g p + pairHeight π h (g⁻¹ • p) := by
  unfold pairHeight
  rw [normalizedPair_smul_fst, inv_inv, map_mul π, map_inv π]
  simp only [toAdd_mul, toAdd_inv]
  abel

omit [NormedSpace ℝ W] [IsIsometricSMul G G] [IsTopologicalGroup G] in
theorem continuous_pairHeight (π : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) :
    Continuous (fun q : G × NormalizedPair G Λ => pairHeight π q.1 q.2) := by
  exact hπ.comp (continuous_eval.comp
    ((continuous_fst.comp continuous_subtype_val).comp continuous_snd |>.prodMk continuous_fst))

/-- The continuous height profile at a fixed group element. -/
def pairHeightProfile (π : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (g : G) : C(NormalizedPair G Λ, W) :=
  ⟨pairHeight π g, (continuous_pairHeight π hπ).comp
    (continuous_const.prodMk continuous_id)⟩

omit [IsIsometricSMul G G] [NormedSpace ℝ W] [IsTopologicalGroup G] in
theorem continuous_pairHeightProfile (π : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) :
    Continuous (pairHeightProfile (Λ := Λ) π hπ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_pairHeight π hπ

variable [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]

/-- The `L²` class of height evaluation, using the canonical continuous-map inclusion. -/
def pairHeightL2 (π : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (g : G) : Lp W 2 μ :=
  ContinuousMap.toLp 2 μ ℝ (pairHeightProfile π hπ g)

omit [IsIsometricSMul G G] in
theorem continuous_pairHeightL2 (π : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) :
    Continuous (pairHeightL2 (Λ := Λ) μ π hπ) :=
  (ContinuousMap.toLp 2 μ ℝ).continuous.comp (continuous_pairHeightProfile π hπ)

attribute [local instance] stationaryL2Action
attribute [local instance] zeroMeanL2Action

theorem isCocycle_pairHeightL2 [SMulInvariantMeasure G (NormalizedPair G Λ) μ]
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd) :
    IsCocycle (pairHeightL2 μ π hπ) := by
  intro g h
  apply Lp.ext
  have hc (k : G) : pairHeightL2 μ π hπ k =ᵐ[μ] pairHeight π k :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (pairHeightProfile π hπ k)
  have hh := (measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving.ae_eq_comp (hc h)
  have hpull : stationaryPullback μ g (pairHeightL2 μ π hπ h) =ᵐ[μ]
      fun p => pairHeightL2 μ π hπ h (g⁻¹ • p) :=
    Lp.coeFn_compMeasurePreserving (pairHeightL2 μ π hπ h)
      (measurePreserving_smul g⁻¹ μ)
  filter_upwards [hc (g * h), hc g, hh,
    Lp.coeFn_add (pairHeightL2 μ π hπ g) (g • pairHeightL2 μ π hπ h),
    hpull] with p hgh hg hh hadd hpull
  simp only [Pi.add_apply, Function.comp_apply] at hadd hpull hh
  rw [hgh, hadd, hg]
  change pairHeight π (g * h) p = pairHeight π g p +
    (stationaryPullback μ g (pairHeightL2 μ π hπ h)) p
  rw [hpull, hh]
  exact pairHeight_cocycle π g h p

/-- The manuscript's fixed-ergodic-measure slope, now for the actual compact
space of normalized pairs and its actual evaluation cocycle. -/
theorem normalizedPair_stationary_sublinear
    {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
    [IsTopologicalGroup G] [IsIsometricSMul G G]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [SecondCountableTopology W] {Λ : ℝ≥0}
    [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [ErgodicSMul G (NormalizedPair G Λ) μ] [μ.InnerRegularCompactLTTop]
    (hvan : ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (Q : Set G) (hQ : IsCompact Q) (length : G → ℝ)
    (hlen : ∀ g, 0 ≤ length g) {a : ℝ} (ha : 0 ≤ a)
    (hword : ∀ g, ∃ l : List G, (∀ q ∈ l, q ∈ Q) ∧ l.prod = g ∧
      (l.length : ℝ) ≤ a * length g + a) :
    ∃ l : G →* Multiplicative W, (Continuous fun g => (l g).toAdd) ∧
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
        ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * length g + B := by
  let b := pairHeightL2 μ π hπ
  have hb : IsCocycle b := isCocycle_pairHeightL2 μ π hπ
  refine ⟨l2MeanSlope μ b hb, ?_, ?_⟩
  · change Continuous (fun g => stationaryL2Mean μ (b g))
    exact (stationaryL2Mean μ).continuous.comp (continuous_pairHeightL2 μ π hπ)
  · exact stationary_sublinear μ hvan b (continuous_pairHeightL2 μ π hπ) hb
      Q hQ length hlen ha hword

end PolycyclicRecognition

end

end OAI
