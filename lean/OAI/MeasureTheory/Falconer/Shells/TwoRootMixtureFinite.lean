import OAI.MeasureTheory.Falconer.Shells.TwoRootClassMixture

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem twoRootClassMeasure_isFinite (Q₀ Q₁ : DyadicSquare)
    (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side) (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (m₀ m₁ : List ℕ → ℝ → ℝ)
    (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ x ∈ Q₀.carrier, ∀ y ∈ Q₁.carrier, r ≤ dist x y)
    (a : List ℕ × List ℕ) :
    IsFiniteMeasure (twoRootClassMeasure Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a) := by
  have hx : ∀ᵐ x ∂actualClassMeasure Q₀ μ N B₀ a.1, x ∈ Q₀.carrier :=
    actualClassMeasure_carry Q₀ hQ₀ μ N B₀ a.1
  have hy : ∀ᵐ y ∂actualClassMeasure Q₁ ν N B₁ a.2, y ∈ Q₁.carrier :=
    actualClassMeasure_carry Q₁ hQ₁ ν N B₁ a.2
  dsimp only [twoRootClassMeasure,RootShellData.ofOuter,RootShellData.measure,RootEndpointData.ofOuter]
  apply rootWeightedDistance_isFinite _ _ N sig hQ₀ hQ₁ hr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hx,
    Measure.quasiMeasurePreserving_snd.ae hy] with z hz₀ hz₁
  exact hsep z.1 hz₀ z.2 hz₁

theorem twoRootClassMixture_isFinite (Q₀ Q₁ : DyadicSquare)
    (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side) (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (m₀ m₁ : List ℕ → ℝ → ℝ)
    (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ x ∈ Q₀.carrier, ∀ y ∈ Q₁.carrier, r ≤ dist x y) :
    IsFiniteMeasure (∑ a ∈ retainedRootPairs Q₀ Q₁ μ ν N B₀ B₁ lam,
      twoRootClassCoefficient Q₀ Q₁ μ ν N B₀ B₁ a •
        twoRootClassMeasure Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a) := by
  let : ∀ pair : List ℕ × List ℕ,
      IsFiniteMeasure (twoRootClassMeasure Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β pair) :=
    fun pair =>
      twoRootClassMeasure_isFinite Q₀ Q₁ hQ₀ hQ₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β hr hsep pair
  infer_instance

end PlanarFalconer

end OAI
