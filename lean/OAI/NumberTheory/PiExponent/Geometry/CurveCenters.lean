import OAI.NumberTheory.PiExponent.Geometry.CurveContactSum
import OAI.NumberTheory.PiExponent.Geometry.CurveProductFormula

namespace OAI

noncomputable section
namespace PiExponent.CurveCenters

open CurveValuationCenter

variable {E ι J : Type*} [Field E] [Algebra ℂ E]

def Centered (x : ι → E) (a : ι → ℂ) (p : NormalizedPlace ℂ E) : Prop :=
  ∀ i, 0 < p.valuation (x i - algebraMap ℂ E (a i))

theorem transcendental_sub_constant {x : E} (hx : Transcendental ℂ x) (c : ℂ) :
    Transcendental ℂ (x - algebraMap ℂ E c) := by
  intro h
  apply hx
  simpa only [sub_add_cancel] using h.add (isAlgebraic_algebraMap c)

theorem exists_transcendental_coordinate (x : ι → E)
    (hx : IntermediateField.adjoin ℂ (Set.range x) = ⊤)
    (hE : ∃ z : E, Transcendental ℂ z) : ∃ i, Transcendental ℂ (x i) := by
  by_contra hn
  push Not at hn
  have hle : IntermediateField.adjoin ℂ (Set.range x) ≤ ⊥ := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := CurveContactSum.exists_constant_of_isAlgebraic (x i) (by
      simpa only [Transcendental, not_not] using hn i)
    exact IntermediateField.mem_bot.mpr ⟨c, hc⟩
  obtain ⟨z, hz⟩ := hE
  have hzbot : z ∈ (⊥ : IntermediateField ℂ E) := hle (by simp [hx])
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hzbot
  exact hz (hc ▸ isAlgebraic_algebraMap c)

theorem finite_centered (x : ι → E) (a : ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i))
    (hfinite : ∀ g : E, Transcendental ℂ g →
      FiniteDimensional (IntermediateField.adjoin ℂ {g}) E) :
    Set.Finite {p : NormalizedPlace ℂ E | Centered x a p} := by
  obtain ⟨i, hi⟩ := hx
  have ht := transcendental_sub_constant hi (a i)
  let := hfinite (x i - algebraMap ℂ E (a i)) ht
  exact (finite_positivePlaces (x i - algebraMap ℂ E (a i)) ht).subset
    (fun p hp => hp i)

theorem finite_centered_family [Finite J] (x : ι → E) (a : J → ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i))
    (hfinite : ∀ g : E, Transcendental ℂ g →
      FiniteDimensional (IntermediateField.adjoin ℂ {g}) E) :
    Set.Finite {p : NormalizedPlace ℂ E | ∃ j, Centered x (a j) p} := by
  have he : {p : NormalizedPlace ℂ E | ∃ j, Centered x (a j) p} =
      ⋃ j, {p : NormalizedPlace ℂ E | Centered x (a j) p} := by ext p; simp
  rw [he]
  exact Set.finite_iUnion (fun j => finite_centered x (a j) hx hfinite)

def centerPlaces [Finite J] (x : ι → E) (a : J → ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i))
    (hfinite : ∀ g : E, Transcendental ℂ g →
      FiniteDimensional (IntermediateField.adjoin ℂ {g}) E) :
    Finset (NormalizedPlace ℂ E) :=
  (finite_centered_family x a hx hfinite).toFinset

@[simp] theorem mem_centerPlaces [Finite J] (x : ι → E) (a : J → ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i))
    (hfinite : ∀ g : E, Transcendental ℂ g →
      FiniteDimensional (IntermediateField.adjoin ℂ {g}) E)
    (p : NormalizedPlace ℂ E) :
    p ∈ centerPlaces x a hx hfinite ↔ ∃ j, Centered x (a j) p :=
  (finite_centered_family x a hx hfinite).mem_toFinset

theorem Centered.center_eq {x : ι → E} {a b : ι → ℂ} {p : NormalizedPlace ℂ E}
    (ha : Centered x a p) (hb : Centered x b p) : a = b := by
  funext i
  by_contra hne
  have hpos : 0 < p.valuation
      ((x i - algebraMap ℂ E (a i)) - (x i - algebraMap ℂ E (b i))) :=
    (lt_min (ha i) (hb i)).trans_le (p.valuation.map_sub _ _)
  have he : (x i - algebraMap ℂ E (a i)) - (x i - algebraMap ℂ E (b i)) =
      algebraMap ℂ E (b i - a i) := by rw [map_sub]; ring
  rw [he, CurveProductFormula.valuation_constant_eq_zero p _ (sub_ne_zero.mpr (fun h => hne h.symm))] at hpos
  exact lt_irrefl _ hpos

theorem Centered.constant_coordinate {x : ι → E} {a : ι → ℂ} {p : NormalizedPlace ℂ E}
    (ha : Centered x a p) (i : ι) (c : ℂ) (hc : x i = algebraMap ℂ E c) : c = a i := by
  by_contra hne
  have h := ha i
  rw [hc, ← map_sub, CurveProductFormula.valuation_constant_eq_zero p _ (sub_ne_zero.mpr hne)] at h
  exact lt_irrefl _ h

theorem Centered.coordinate_nonneg {x : ι → E} {a : ι → ℂ} {p : NormalizedPlace ℂ E}
    (ha : Centered x a p) (i : ι) : 0 ≤ p.valuation (x i) := by
  have h := (le_min (ha i).le (p.constants_nonneg (a i))).trans
    (p.valuation.map_add (x i - algebraMap ℂ E (a i)) (algebraMap ℂ E (a i)))
  simpa only [sub_add_cancel] using h

theorem center_index_unique_of_constant
    (x : ι → E) (a : J → ι → ℂ) (ha : ∀ i, Function.Injective (fun j => a j i))
    (i : ι) (c : ℂ) (hc : x i = algebraMap ℂ E c)
    (j l : J) (p q : NormalizedPlace ℂ E)
    (hp : Centered x (a j) p) (hq : Centered x (a l) q) : j = l := by
  apply ha i
  exact (hp.constant_coordinate i c hc).symm.trans (hq.constant_coordinate i c hc)

theorem Centered.exists_nonzero_difference (x : ι → E) (a : ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i)) :
    ∃ i, x i ≠ algebraMap ℂ E (a i) := by
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  intro he
  exact hi (he.symm ▸ isAlgebraic_algebraMap (a i))

end PiExponent.CurveCenters
end

end OAI
