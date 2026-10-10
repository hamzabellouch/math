import OAI.Geometry.HeilbronnTriangle.Definitions
import OAI.Geometry.HeilbronnTriangle.RandomAlteration

namespace OAI


namespace Problem355.Alteration

def smallTriangle (a : ℝ) (p q r : Point) : Prop :=
  p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ triangleArea p q r < a

theorem image_configuration {ι : Type*} (T : Finset ι) (f : ι → Point) (a : ℝ)
    (hinj : Set.InjOn f (T : Set ι))
    (hsquare : ∀ i ∈ T, pointInUnitSquare (f i))
    (hgood : ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T,
      i ≠ j → i ≠ k → j ≠ k → ¬ smallTriangle a (f i) (f j) (f k)) :
    ∃ P : Finset Point, P.card = T.card ∧ pointsInUnitSquare P ∧
      triangleAreasAtLeast P a := by
  classical
  refine ⟨T.image f, Finset.card_image_of_injOn hinj, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact hsquare i hi
  · intro p hp q hq r hr hpq hpr hqr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
    have hij : i ≠ j := fun h => hpq (congrArg f h)
    have hik : i ≠ k := fun h => hpr (congrArg f h)
    have hjk : j ≠ k := fun h => hqr (congrArg f h)
    apply le_of_not_gt
    intro harea
    exact hgood i hi j hj k hk hij hik hjk ⟨hpq, hpr, hqr, harea⟩

theorem exists_point_configuration_of_marginal_bounds
    {Ω ι : Type*} [DecidableEq ι]
    (outcomes : Finset Ω) (weight : Ω → ℝ) (S : Finset ι)
    (f : Ω → ι → Point) (n : ℕ) (a : ℝ)
    (hweight : ∀ ω ∈ outcomes, 0 ≤ weight ω)
    (hnorm : ∑ ω ∈ outcomes, weight ω = 1)
    (hsquare : ∀ ω ∈ outcomes, ∀ i ∈ S, pointInUnitSquare (f ω i))
    (hn : n ≤ S.card) (p q : ℝ)
    (hpair : ∀ e ∈ S.powersetCard 2,
      (∑ ω ∈ outcomes, if e ∈ collisionEdges S (f ω) then weight ω else 0) ≤ p)
    (htriple : ∀ e ∈ S.powersetCard 3,
      (∑ ω ∈ outcomes,
        if e ∈ badTripleEdges S (f ω) (smallTriangle a) then weight ω else 0) ≤ q)
    (hsmall : (Nat.choose S.card 2 : ℝ) * p + (Nat.choose S.card 3 : ℝ) * q <
      ((S.card - n + 1 : ℕ) : ℝ)) :
    ∃ P : Finset Point, P.card = n ∧ pointsInUnitSquare P ∧
      triangleAreasAtLeast P a := by
  obtain ⟨ω, hω, T, hTS, hcard, hinj, hgood⟩ :=
    exists_good_sample_of_marginal_bounds outcomes weight S f (smallTriangle a) n
      hweight hnorm hn p q hpair htriple hsmall
  obtain ⟨P, hPcard, hPsquare, hParea⟩ := image_configuration T (f ω) a hinj
    (fun i hi => hsquare ω hω i (hTS hi)) hgood
  exact ⟨P, hPcard.trans hcard, hPsquare, hParea⟩

end Problem355.Alteration

end OAI
