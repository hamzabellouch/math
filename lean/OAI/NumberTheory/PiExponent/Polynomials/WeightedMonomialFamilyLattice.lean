import OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal
import OAI.NumberTheory.PiExponent.Polynomials.WeightedMonomialLattice

namespace OAI

noncomputable section
open scoped BigOperators
open PiExponent.CurveValuationCenter PiExponent.WeightedPolynomialPole
open PiExponent.WeightedLocalLattice PiExponent.CurveGlobalMonomialLocal

namespace PiExponent.WeightedMonomialFamilyLattice

theorem exists_generator
    {E ι σ : Type} [Field E] [Algebra ℂ E] [Fintype ι] [Fintype σ]
    (p : NormalizedPlace ℂ E) (a : σ → ι →₀ ℕ) (x : ι → E)
    (z : σ) (hz : a z = 0) (w : ι → ℚ) (hw : ∀ j, 0 < w j)
    {R : ℚ} (hR : 0 < R) (powers : ι → ℕ)
    (hpowers : ∀ j, w j * (powers j : ℚ) = R)
    (pure : ι → σ) (hpure : ∀ j, a (pure j) = Finsupp.single j (powers j))
    (hbudget : ∀ s, (∑ j, w j * (a s j : ℚ)) ≤ R) :
    ∃ i : σ, monomialCoordinates (F := ℂ) a x i ≠ 0 ∧
      (coordinateOrder p.valuation (monomialCoordinates (F := ℂ) a x i) : ℚ) =
        -R * coordinatePole p.valuation x w ∧
      generatedLattice (PlaceValuationRing.ring p) (monomialCoordinates (F := ℂ) a x)
        Finset.univ = Submodule.span (PlaceValuationRing.ring p)
          {monomialCoordinates (F := ℂ) a x i} := by
  classical
  let M : Finset (ι → ℕ) := Finset.univ.image (fun s : σ => fun j => a s j)
  have hzero : 0 ∈ M := by
    apply Finset.mem_image.mpr
    refine ⟨z, Finset.mem_univ z, ?_⟩
    funext j
    simp [hz]
  have hpureM : ∀ j, Pi.single j (powers j) ∈ M := by
    intro j
    apply Finset.mem_image.mpr
    refine ⟨pure j, Finset.mem_univ _, ?_⟩
    ext k
    simp [hpure, Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hbudgetM : ∀ b ∈ M, (∑ j, w j * (b j : ℚ)) ≤ R := by
    intro b hb
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hb
    exact hbudget s
  obtain ⟨b, hb, hbn, hbo, hmin⟩ := WeightedMonomialPole.exists_minimizing_monomial
    p.valuation x w hw hR powers hpowers M hzero hpureM hbudgetM
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
  have hn : monomialCoordinates (F := ℂ) a x i ≠ 0 := by
    simpa only [monomialCoordinates_eq_prod] using hbn
  refine ⟨i, hn, ?_, ?_⟩
  · simpa only [monomialCoordinates_eq_prod] using hbo
  · apply generatedLattice_eq_span_of_minimum _ Finset.univ i (Finset.mem_univ i) hn
    intro j hj
    rw [← PlaceValuationRing.valuation_eq_fractionAddValuation]
    simpa only [monomialCoordinates_eq_prod] using
      hmin (fun k => a j k) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)

end PiExponent.WeightedMonomialFamilyLattice

end

end OAI
