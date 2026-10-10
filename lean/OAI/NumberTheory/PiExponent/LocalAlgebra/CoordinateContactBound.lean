import Mathlib
import OAI.NumberTheory.PiExponent.Geometry.CurveContactSum
import OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch
import OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CoordinateContactBound

open WeightedSliceDegree CurveValuationCenter CurveCenters

theorem supportBound_X_sub_C
    {K ι : Type*} [Field K] (W : ι → ℝ) (i : ι) (hi : 0 ≤ W i) (c : K) :
    SupportBound W (W i) (MvPolynomial.X i - MvPolynomial.C c) := by
  have hX : SupportBound W (W i) (MvPolynomial.X i : MvPolynomial ι K) :=
    supportBound_X W i
  have hC : SupportBound W (W i) (MvPolynomial.C (-c)) := (supportBound_C W (-c)).mono hi
  simpa only [map_neg, sub_eq_add_neg] using hX.add hC

@[simp] theorem ordinary_formalJet_X_sub_C {n : ℕ} (c : Fin n → ℂ) (i : Fin n) :
    OrdinaryAuxiliaryJet.formalJet c (MvPolynomial.X i - MvPolynomial.C (c i)) =
      MvPowerSeries.X i := by
  simp only [OrdinaryAuxiliaryJet.formalJet, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  change MvPowerSeries.C (c i) + MvPowerSeries.X i - MvPowerSeries.C (c i) = MvPowerSeries.X i
  abel

theorem X_mem_rationalWeightedIdeal
    {K ι : Type*} [CommRing K] (V : ι → ℚ) (hV : ∀ i, 0 ≤ V i) (i : ι) :
    MvPowerSeries.X i ∈ (JetGeometry.rationalWeightedIdeal V hV (V i) :
      Ideal (MvPowerSeries ι K)) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_X, ite_eq_right]
  intro he
  subst d
  simp [Finsupp.weight_single] at hd

theorem ordinary_formalJet_coordinate_mem {n : ℕ} (c : Fin n → ℂ)
    (V : Fin n → ℚ) (hV : ∀ i, 0 ≤ V i) (i : Fin n) :
    OrdinaryAuxiliaryJet.formalJet c (MvPolynomial.X i - MvPolynomial.C (c i)) ∈
      JetGeometry.rationalWeightedIdeal V hV (V i) := by
  rw [ordinary_formalJet_X_sub_C]
  exact X_mem_rationalWeightedIdeal V hV i

theorem coordinate_contact_sum_le
    {E : Type*} [Field E] [Algebra ℂ E] {n : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin n → E) (c : Fin n → ℂ)
    (W V : Fin n → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (i : Fin n) (hne : x i - algebraMap ℂ E (c i) ≠ 0)
    (S : Finset (NormalizedPlace ℂ E))
    (hc : ∀ p ∈ S, Centered x c p)
    (hres : ∀ p ∈ S,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p)))
    (μ : NormalizedPlace ℂ E → ℝ)
    (hμ : ∀ p (hp : p ∈ S), letI := hres p hp;
      μ p = (PlaceCenteredBranch.ordinaryContact p x c (hc p hp)
        ⟨i, sub_ne_zero.mp hne⟩ V : ℝ)) :
    (V i : ℝ) * (∑ p ∈ S, μ p) ≤
      (W i : ℝ) * CurveContactSum.weightedDegree hfinite x W := by
  let f : MvPolynomial (Fin n) ℂ := MvPolynomial.X i - MvPolynomial.C (c i)
  have hfe : MvPolynomial.aeval x f = x i - algebraMap ℂ E (c i) := by simp [f]
  apply CurveContactSum.polynomial_contact_sum_le hfinite x W hW
    (W i : ℝ) (V i : ℝ) (by exact_mod_cast (hW i).le) f
    (supportBound_X_sub_C (fun j => (W j : ℝ)) i (by exact_mod_cast (hW i).le) (c i))
    (hfe ▸ hne) S μ
  intro p hp
  let := hres p hp
  rw [hμ p hp]
  have h := PlaceCenteredBranch.ordinaryWord_field_order_lower p x c (hc p hp)
    ⟨i, sub_ne_zero.mp hne⟩ V hV (V i) f
    (ordinary_formalJet_coordinate_mem c V (fun j => (hV j).le) i) []
    (by simpa only [OrdinaryDerivatives.word_nil, hfe] using hne)
  simp only [List.map_nil, List.sum_nil, sub_zero, OrdinaryDerivatives.word_nil] at h
  exact_mod_cast (by simpa only [mul_comm] using h :
    V i * PlaceCenteredBranch.ordinaryContact p x c (hc p hp) ⟨i, sub_ne_zero.mp hne⟩ V ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℚ))

end PiExponent.CoordinateContactBound

end

end OAI
