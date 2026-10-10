import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerSections
import OAI.NumberTheory.PiExponent.Ampleness.ReesProductChart
import OAI.NumberTheory.PiExponent.Geometry.IdealSheafPowers

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
namespace PiExponent.ReesProductPowerSections
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesProductChart
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) {s : Finset J} (hs : s.Nonempty)

theorem exists_chartMorphism :
    ∃ j : Spec (CommRingCat.of (Chart I a s)) ⟶ affineBlowup I,
      j = Proj.awayι (piece I) (productGenerator I a s) (productGenerator_mem I a s)
        (Finset.card_pos.mpr hs) :=
  ⟨_, rfl⟩

def chartMorphism : Spec (CommRingCat.of (Chart I a s)) ⟶ affineBlowup I :=
  (exists_chartMorphism I a hs).choose

theorem chartMorphism_eq :
    chartMorphism I a hs =
      Proj.awayι (piece I) (productGenerator I a s) (productGenerator_mem I a s)
        (Finset.card_pos.mpr hs) :=
  (exists_chartMorphism I a hs).choose_spec

instance chartMorphism_open : IsOpenImmersion (chartMorphism I a hs) := by
  rw [chartMorphism_eq]
  exact inferInstanceAs (IsOpenImmersion
    (Proj.awayι (m := s.card) (piece I) (productGenerator I a s)
      (productGenerator_mem I a s) (Finset.card_pos.mpr hs)))

theorem chartMorphism_projection :
    chartMorphism I a hs ≫ projection I =
      Spec.map (CommRingCat.ofHom (ReesProductChart.chartBase I a s)) := by
  rw [chartMorphism_eq]
  change Proj.awayι (piece I) (productGenerator I a s) _ _ ≫
    (Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

private local instance (q : I) : IsOpenImmersion ((chartCover I).f q) :=
  (chartCover I).map_prop q

theorem chartMorphism_opensRange :
    (chartMorphism I a hs).opensRange =
      s.inf (fun j => ((chartCover I).f (a j)).opensRange) := by
  have he : (chartMorphism I a hs).opensRange =
      (Proj.awayι (piece I) (productGenerator I a s) (productGenerator_mem I a s)
        (Finset.card_pos.mpr hs)).opensRange := by
    apply SetLike.coe_injective
    simp only [Scheme.Hom.coe_opensRange]
    rw [chartMorphism_eq]
    rfl
  rw [he]
  change (Proj.awayι (piece I) (productGenerator I a s) _ _).opensRange = _
  rw [Proj.opensRange_awayι, productGenerator_eq_prod]
  have h : ∀ t : Finset J,
      Proj.basicOpen (piece I) (∏ j ∈ t, generator I (a j)) =
      t.inf (fun j => Proj.basicOpen (piece I) (generator I (a j))) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert j t hj ih => rw [Finset.prod_insert hj, Proj.basicOpen_mul, ih, Finset.inf_insert]
  rw [h]
  congr 1
  funext j
  exact (Proj.opensRange_awayι (piece I) (generator I (a j))
    (generator_mem I (a j)) (by decide)).symm

def chartOpen : (affineBlowup I).affineOpens :=
  ⟨(chartMorphism I a hs).opensRange, isAffineOpen_opensRange _⟩

variable {p : J} (hp : p ∈ s)

def chartEquation : Γ(Spec (CommRingCat.of (Chart I a s)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Chart I a s))).inv
    (ReesProductChart.chartBase I a s (a p).val)

include hp in
theorem exceptional_chart :
    ((exceptionalIdeal I).comap (chartMorphism I a hs)).ideal
      ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {chartEquation I a (s := s) (p := p)} := by
  rw [exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp, chartMorphism_projection,
    PiExponentSeshadri.IdealPullback.specIdeal_comap,
    PiExponentSeshadri.IdealPullback.specIdeal_top,
    ReesProductChart.map_ideal_principal I a hp, Ideal.map_span, Set.image_singleton]
  rfl

include hp in
theorem chartEquation_regular : IsLeftRegular (chartEquation I a (s := s) (p := p)) := by
  exact PiExponentSeshadri.IdealModule.regular_map_flat _
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (Chart I a s))).inv))
    (ReesProductChart.chart_generator_regular I a hp).left

end PiExponent.ReesProductPowerSections
end

end OAI
