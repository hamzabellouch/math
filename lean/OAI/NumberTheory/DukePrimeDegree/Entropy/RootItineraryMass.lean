import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProductSupport
import OAI.NumberTheory.DukePrimeDegree.Entropy.RootAdaptedObservations

namespace OAI

/-! # Positive finite intrinsic mass of actual future-itinerary atoms

The good cuts supply neighborhoods in root time. The actual intrinsic
product gives every such neighborhood positive mass. Intersecting with
the normalizing unit cube makes these masses finite and at most one.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

def upperRootTimeProduct (n : ℕ) (μ : Measure (X n)) [IsFiniteMeasure μ] (x : X n) :
    Measure (UpperRootTime n) :=
  (completeRootChain n).remainingTimeProduct
    (by intro p hp; simp at hp) (completeRootChain_final n) μ x

def rootFutureAtom {n m : ℕ} (T : X n → X n) (Q : X n → Fin m)
    (x : X n) : Set (UpperRootTime n) :=
  {t | ∀ k : ℕ, Q (T^[k] (rightAction x ((completeRootChain n).word t))) = Q (T^[k] x)}

lemma rootFutureAtom_measurable {n m : ℕ} {T : X n → X n} (hT : Measurable T)
    {Q : X n → Fin m} (hQ : Measurable Q) (x : X n) :
    MeasurableSet (rootFutureAtom T Q x) := by
  change MeasurableSet {t | ∀ k : ℕ,
    Q (T^[k] (rightAction x ((completeRootChain n).word t))) = Q (T^[k] x)}
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  apply measurableSet_eq_fun _ measurable_const
  exact hQ.comp ((hT.iterate k).comp
    ((continuous_rightOrbit n x).comp (upperRootWord_isEmbedding n).continuous).measurable)

theorem ae_upperRootTimeProduct_nhds_pos (d : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ) :
    ∀ᵐ x ∂μ, ∀ U ∈ 𝓝 (completeRootChain (d+1)).zeroTime,
      0 < upperRootTimeProduct (d+1) μ x U :=
  EliminationChain.ae_remainingTimeProduct_nhds_pos d (completeRootChain (d+1))
    (by intro p hp; simp at hp) (completeRootChain_final (d+1)) μ hA

theorem ae_upperRootTimeProduct_unit (d : ℕ)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∀ᵐ x ∂μ, upperRootTimeProduct (d+1) μ x ((completeRootChain (d+1)).cube 1)=1 :=
  EliminationChain.ae_remainingTimeProduct_unit d (completeRootChain (d+1))
    (by intro p hp; simp at hp) (completeRootChain_final (d+1)) μ

/-- These are actual intrinsic masses, with no new entropy or leaf
disintegration hypothesis. -/
theorem exists_cuts_with_positive_finite_itinerary_mass (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0) (ε : ℝ) (hε : 0<ε)
    (hgap : ∀ p : allPositiveRoots (d+1), ε ≤ ell p.val.2-ell p.val.1)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∃ r : QuotientCutIndex → ℝ,
      (∀ i, (i.2.val.1 : ℝ)<r i ∧ r i<(i.2.val.2 : ℝ)) ∧
      ∀ᵐ x ∂μ, ∀ n : ℕ,
        0 < upperRootTimeProduct (d+1) μ x
          (rootFutureAtom (fun y => rightAction y (diagonalOneParameter ell hell (-1)))
            (quotientCutObservation r n) x ∩ (completeRootChain (d+1)).cube 1) ∧
        upperRootTimeProduct (d+1) μ x
          (rootFutureAtom (fun y => rightAction y (diagonalOneParameter ell hell (-1)))
            (quotientCutObservation r n) x ∩ (completeRootChain (d+1)).cube 1) ≤ 1 := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u))=μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  obtain ⟨r,hr,hgood⟩ := exists_observations_with_root_neighborhoods d ell hell ε hε hgap μ hA
  refine ⟨r,hr,?_⟩
  filter_upwards [hgood,ae_upperRootTimeProduct_nhds_pos d μ hA,
    ae_upperRootTimeProduct_unit d μ] with x hx hp hu
  intro n
  have hN : rootFutureAtom (fun y => rightAction y (diagonalOneParameter ell hell (-1)))
      (quotientCutObservation r n) x ∈ 𝓝 (completeRootChain (d+1)).zeroTime := hx n
  have hcube : (completeRootChain (d+1)).cube 1 ∈ 𝓝 (completeRootChain (d+1)).zeroTime :=
    ((completeRootChain (d+1)).cube_open 1).mem_nhds
      ((completeRootChain (d+1)).zeroTime_mem_cube zero_lt_one)
  exact ⟨hp _ (inter_mem hN hcube),(measure_mono inter_subset_right).trans_eq hu⟩

end DukePrimeDegree

end

end OAI
