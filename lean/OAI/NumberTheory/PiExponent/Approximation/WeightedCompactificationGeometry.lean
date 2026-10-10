import OAI.NumberTheory.PiExponent.Geometry.ProjectiveDenseChart
import OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveStructure

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial AlgebraicGeometry CategoryTheory Topology

universe u
variable {R ι σ : Type u} [CommRing R]

def affineChartMap (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Spec (CommRingCat.of (MvPolynomial ι R)) ⟶ Proj (imageGrade (R := R) a) :=
  (constantProjectiveChartIso (R := R) a z hz coordinate hcoordinate).inv ≫
    (Proj.basicOpen (imageGrade a) (imageCoordinate a z)).ι

instance affineChartMap_isOpenImmersion (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    IsOpenImmersion (affineChartMap (R := R) a z hz coordinate hcoordinate) := by
  let e := constantProjectiveChartIso (R := R) a z hz coordinate hcoordinate
  have : IsOpenImmersion e.inv := inferInstance
  exact IsOpenImmersion.comp _ _

theorem affineChartMap_range (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Set.range (affineChartMap (R := R) a z hz coordinate hcoordinate) =
      (Proj.basicOpen (imageGrade (R := R) a) (imageCoordinate a z) : Set (Proj (imageGrade (R := R) a))) := by
  let e := constantProjectiveChartIso (R := R) a z hz coordinate hcoordinate
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (e.inv y).2
  · intro hx
    refine ⟨e.hom ⟨x, hx⟩, ?_⟩
    change ((e.hom ≫ e.inv) ⟨x, hx⟩).1 = x
    simp only [Iso.hom_inv_id]
    rfl

theorem affineChartMap_denseRange [IsDomain R] (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    DenseRange (affineChartMap (R := R) a z hz coordinate hcoordinate) := by
  change Dense (Set.range _)
  rw [affineChartMap_range]
  exact constantChart_dense a z hz

theorem projective_range_eq_closure_affine [IsDomain R]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Set.range (projectiveMonomialMap (R := R) a) =
      closure (Set.range (affineChartMap a z hz coordinate hcoordinate ≫ projectiveMonomialMap a)) := by
  change Set.range (projectiveMonomialMap (R := R) a) =
    closure (Set.range ((projectiveMonomialMap (R := R) a) ∘
      (affineChartMap (R := R) a z hz coordinate hcoordinate)))
  rw [Set.range_comp]
  rw [(projectiveMonomialMap (R := R) a).isClosedEmbedding.closure_image_eq,
    (affineChartMap_denseRange a z hz coordinate hcoordinate).closure_range]
  simp

end PiExponent.WeightedCompactification

end

end OAI
