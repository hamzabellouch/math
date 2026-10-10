import OAI.Combinatorics.Progressions.Estimates.MixedBooleanSiteValues

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

theorem coefficientJet_normalized_chart_mass {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {n : Fin m → ℕ} (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ) (ha : a ≠ 0)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (rows : ∀ j, O j → Finset α) (hinj : ∀ j, Function.Injective (rows j))
    (hdegree : ∀ j o, (rows j o).card ≤ j.val + 1)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
    (hΩm : ∀ j o, MeasurableSet (Ω j o))
    (hΩ : ∀ j o, Ω j o ⊆ standardLatticeSmallBox (J j)) :
    μ {x | ∀ j o, euclideanCoefficientJetMap U root D rows x j o ∈
      latticeSmallLiftRegion (standardEuclideanLattice (J j)) (euclideanSubspace (U j)) (Ω j o)} =
      ∏ j, ∏ o, (∑' z : Fin (n j) → ℤ, volume {u : euclideanSubspace (U j) |
        (normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm
          (u, fun i => (z i : ℝ) / (basisAxisScale (b j) i : ℝ)) ∈ Ω j o}) /
        ENNReal.ofReal (ZLattice.covolume
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))) := by
  let R := fun j o => latticeSmallLiftRegion (standardEuclideanLattice (J j))
    (euclideanSubspace (U j)) (Ω j o)
  let A := Set.pi Set.univ (fun j => Set.pi Set.univ (R j))
  have hA : MeasurableSet A := MeasurableSet.univ_pi (fun j =>
    MeasurableSet.univ_pi (fun o => smallLiftRegion_measurable _ (hΩm j o) (hΩ j o)))
  have hp := euclideanCoefficientJetMap_measurePreserving U root D a ha hperiod rows hinj hdegree μ ν
  have he := congrArg (fun ρ => ρ A) hp.map_eq
  rw [Measure.map_apply hp.measurable hA, Measure.pi_pi] at he
  simp_rw [Measure.pi_pi] at he
  have hpre : (euclideanCoefficientJetMap U root D rows) ⁻¹' A =
      {x | ∀ j o, euclideanCoefficientJetMap U root D rows x j o ∈ R j o} := by
    ext x
    simp [A]
  rw [hpre] at he
  exact he.trans (Finset.prod_congr rfl (fun j _ => Finset.prod_congr rfl (fun o _ =>
    normalized_smallLift_haar_formula (euclideanSubspace (U j)) (b j) (hb j) (ν j) (hΩm j o) (hΩ j o))))

end Erdos3.VectorPolynomial

end

end OAI
