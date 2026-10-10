import OAI.NumberTheory.PiExponent.Approximation.FibreWeightSeparation
import OAI.NumberTheory.PiExponent.Cohomology.CurveDerivativeVanishing
import OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite
import OAI.NumberTheory.PiExponent.Jets.FormalAuxiliaryJet
import OAI.NumberTheory.PiExponent.Jets.OrdinaryAuxiliaryJet
import OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace PiExponent.CurveInequality

open PiExponentApprox CurveValuationCenter PlaceValuationRing CurveContactFamily
open PersistentWeightComparison


theorem excess_implies_zeroth_eq_one
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hheight : (CurveFieldRigidity.coordinateKernel z).height ≤ m)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz, (contact hres hfinite z c hz v p : ℝ)) :
    z 0 = 1 := by
  have hvR (i : Fin (m+1)) : (0 : ℝ) < v i := by exact_mod_cast hv i
  have hsR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have haux := eventually_exists_formalJet_auxiliaryPolynomial_nat w v hw hv K
    (a := 1+3*sigma) (by positivity) (by simpa using hvol) c
  have hrect := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_uniformRectangles (m+1) (fun i => (v i : ℝ)) hvR
      ((sigma : ℝ)/((m : ℝ)+2)) (by positivity))
  obtain ⟨N, hauxN, hrectN, hN⟩ :=
    (haux.and (hrect.and (eventually_gt_atTop (0 : ℕ)))).exists
  obtain ⟨F, hF0, hF, hjet⟩ := hauxN
  have hwords := CurveDerivativeVanishing.logarithmic_words_vanish hres hfinite z c hz
    w v hw hv sigma hsigma N hN F hF hjet hexcess
  have hS : (places hfinite z c hz).Nonempty := by
    by_contra h
    have he : places hfinite z c hz = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he, Finset.sum_empty, mul_zero] at hexcess
    exact (not_lt_of_ge (CurveContactSum.weightedDegree_nonneg hfinite z w)) hexcess
  obtain ⟨p,hp⟩ := hS
  exact CurveFieldRigidity.logarithmic_coordinate_eq_one z
    (fullCenter (c (center hfinite z c hz p hp))) rfl p
    (centered hfinite z c hz p hp) hheight w hw (fun i => (v i : ℝ)) hvR
    sigma N hsR (by exact_mod_cast hN) hrectN F hF0 hF hwords hseparated

theorem excess_implies_fibre_coordinate_constant
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin m → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ ((fibre x) i))
    (hheight : (CurveFieldRigidity.coordinateKernel x).height ≤ m)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^m *
      (∏ i : Fin m, (w i.succ : ℝ)) / (∏ i : Fin m, (v i.succ : ℝ)) < 1)
    (hseparated : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      comparisonConstant m sigma * (∏ j ∈ B, (v j : ℝ)) < ∏ j ∈ A, (w j : ℝ))
    (hexcess : CurveContactSum.weightedDegree hfinite (fibre x) w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite (fibre x) c hz,
        (contact hres hfinite (fibre x) c hz v p : ℝ)) :
    ∃ i : Fin m, ∃ a : ℂ, x i = algebraMap ℂ E a := by
  have hvR (i : Fin m) : (0 : ℝ) < v i.succ := by exact_mod_cast hv i.succ
  have hsR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have haux := OrdinaryAuxiliaryJet.eventually_exists_auxiliaryPolynomial_nat
    (fun i => w i.succ) (fun i => v i.succ) (fun i => hw i.succ) (fun i => hv i.succ) K
    (a := 1+3*sigma) (by positivity) (by simpa using hvol) c
  have hrect := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_uniformRectangles m (fun i => (v i.succ : ℝ)) hvR
      ((sigma : ℝ)/((m : ℝ)+2)) (by positivity))
  obtain ⟨N, hauxN, hrectN, hN⟩ :=
    (haux.and (hrect.and (eventually_gt_atTop (0 : ℕ)))).exists
  obtain ⟨F, hF0, hF, hjet⟩ := hauxN
  have hdeg : CurveContactSum.weightedDegree hfinite (fibre x) w =
      CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) := by
    exact FibreContact.weightedDegree_one hfinite w x
  rw [hdeg] at hexcess
  have hwords := CurveDerivativeVanishing.ordinary_words_vanish hres hfinite x c hz
    w v hw hv sigma hsigma N hN F hF hjet hexcess
  exact CurveFieldRigidity.ordinary_coordinate_constant (m := m) (by omega) x m le_rfl
    hheight (fun i => w i.succ) (fun i => hw i.succ) (fun i => (v i.succ : ℝ)) hvR
    sigma N hsR (by exact_mod_cast hN) hrectN F hF0 hF hwords
    (FibreWeightSeparation.positive_indices (fun i => (w i : ℝ)) (fun i => (v i : ℝ))
      (comparisonConstant m sigma) hseparated)

theorem no_fibre_excess_of_constant_coordinate
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin m → E) (c : Fin K → Fin m → ℂ)
    (hc : ∀ i, Function.Injective (fun j => c j i))
    (hz : ∃ i, Transcendental ℂ ((fibre x) i))
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ : ℝ) < v i.succ)
    (hconst : ∃ i : Fin m, ∃ a : ℂ, x i = algebraMap ℂ E a) :
    ¬ CurveContactSum.weightedDegree hfinite (fibre x) w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite (fibre x) c hz,
        (contact hres hfinite (fibre x) c hz v p : ℝ) := by
  intro hexcess
  let z : Fin (m+1) → E := fibre x
  let S := places hfinite z c hz
  let μ := fun p => (contact hres hfinite z c hz v p : ℝ)
  have hdeg : CurveContactSum.weightedDegree hfinite (fibre x) w =
      CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) :=
    FibreContact.weightedDegree_one hfinite w x
  have hex : CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) <
      (1+(sigma : ℝ)) * ∑ p ∈ S, μ p := by
    rw [hdeg] at hexcess
    exact hexcess
  have hsum : 0 < ∑ p ∈ S, μ p := by
    have hn := CurveContactSum.weightedDegree_nonneg hfinite x (fun i => w i.succ)
    have hs : (0 : ℝ) < 1+sigma := by exact_mod_cast (by linarith : (0 : ℚ)<1+sigma)
    exact (mul_pos_iff_of_pos_left hs).mp (lt_of_le_of_lt hn hex)
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hsum
    exact lt_irrefl _ hsum
  obtain ⟨p0,hp0⟩ := hS
  let j0 := center hfinite z c hz p0 hp0
  obtain ⟨i0,a,ha⟩ := hconst
  have hcenters : ∀ p (hp : p ∈ S), center hfinite z c hz p hp = j0 := by
    intro p hp
    exact CurveCenters.center_index_unique_of_constant x c hc i0 a ha
      _ _ p p0 (fun i => centered hfinite z c hz p hp i.succ)
      (fun i => centered hfinite z c hz p0 hp0 i.succ)
  have hcenter : ∀ p ∈ S, CurveCenters.Centered x (c j0) p := by
    intro p hp i
    simpa only [hcenters p hp, z, fibre_succ, fullCenter_succ] using
      centered hfinite z c hz p hp i.succ
  have hnc : ∃ i, x i ≠ algebraMap ℂ E (c j0 i) :=
    PlaceCenteredBranch.fibre_nonconstant x (c j0) (nonconstant z (c j0) hz)
  obtain ⟨i,hi⟩ := hnc
  have hcoord := CoordinateContactBound.coordinate_contact_sum_le hfinite x (c j0)
    (fun i => w i.succ) (fun i => v i.succ) (fun i => hw i.succ) (fun i => hv i.succ)
    i (sub_ne_zero.mpr hi) S hcenter (fun p _ => hres p) μ (by
      intro p hp
      let := hres p
      have heq := contact_one hres hfinite x c hz v p hp
      have hcongr {a b : Fin m → ℂ} (hab : a = b)
          (ha : CurveCenters.Centered x a p) (hna : ∃ i, x i ≠ algebraMap ℂ E (a i))
          (hb : CurveCenters.Centered x b p) (hnb : ∃ i, x i ≠ algebraMap ℂ E (b i)) :
          PlaceCenteredBranch.ordinaryContact p x a ha hna (fun i => v i.succ) =
            PlaceCenteredBranch.ordinaryContact p x b hb hnb (fun i => v i.succ) := by
        subst b
        rfl
      have hcontact := heq.trans (hcongr (congrArg c (hcenters p hp)) _ _
        (hcenter p hp) ⟨i, hi⟩)
      exact congrArg (fun q : ℚ => (q : ℝ)) hcontact)
  have hwi : (0 : ℝ) < w i.succ := by exact_mod_cast hw i.succ
  have hb := mul_lt_mul_of_pos_left hex hwi
  have hr := mul_lt_mul_of_pos_right (hratio i) hsum
  nlinarith

end PiExponent.CurveInequality
end

end OAI
