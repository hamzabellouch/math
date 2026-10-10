import OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily
import OAI.NumberTheory.PiExponent.Geometry.CurveFieldRigidity

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveDerivativeVanishing

open PiExponentApprox CurveValuationCenter PlaceValuationRing CurveContactFamily

theorem cast_word_cost {ι : Type*} (v : ι → ℚ) (word : List ι) :
    (((word.map v).sum : ℚ) : ℝ) = (word.map (fun i => (v i : ℝ))).sum := by
  induction word with
  | nil => simp
  | cons i word ih => simp [ih]

theorem logarithmic_words_vanish
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i))
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma) (N : ℕ) (hN : 0 < N)
    (F : FramePolynomial m)
    (hF : HasWeightedDegreeLE (fun i => (w i : ℝ)) N F)
    (hjet : ∀ j, FormalLogJet.formalJet (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) ((1+3*sigma)*N))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz, (contact hres hfinite z c hz v p : ℝ)) :
    ∀ word : List (Fin (m+1)),
      frameWordCost (fun i => (v i : ℝ)) word ≤ (sigma : ℝ)*N →
        MvPolynomial.aeval z (polynomialFrameWord m word F) = 0 := by
  intro word hword
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsigR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have hcost : (word.map v).sum ≤ sigma*N := by
    change (word.map (fun i => (v i : ℝ))).sum ≤ (sigma : ℝ)*N at hword
    rw [← cast_word_cost v word] at hword
    exact_mod_cast hword
  have hdegree : ∀ d ∈ (polynomialFrameWord m word F).support,
      Finsupp.weight (fun i => (w i : ℝ)) d ≤ (N : ℝ) := by
    apply (FrameEquationFamily.hasWeightedDegreeLE_iff_supportBound _ _ _).mp
    exact hF.polynomialFrameWord (fun i => by exact_mod_cast (hw i).le) word
  have hsum : 0 ≤ ∑ p ∈ places hfinite z c hz, (contact hres hfinite z c hz v p : ℝ) := by
    apply Finset.sum_nonneg
    intro p hp
    exact_mod_cast contact_nonneg hres hfinite z c hz v hv p
  apply CurveContactSum.polynomial_eq_zero_of_excess_contact hfinite z w hw
    (N : ℝ) ((1+2*(sigma : ℝ))*N) hNR.le (polynomialFrameWord m word F) hdegree
    (places hfinite z c hz) (fun p => (contact hres hfinite z c hz v p : ℝ))
  · intro hne p hp
    have hret : (1+2*sigma)*(N : ℚ) ≤ (1+3*sigma)*N - (word.map v).sum := by
      nlinarith
    have hlocal := logWord_order_lower hres hfinite z c hz v hv ((1+3*sigma)*N)
      F hjet word hne p hp
    have hq := (mul_le_mul_of_nonneg_left hret
      (contact_nonneg hres hfinite z c hz v hv p)).trans hlocal
    have hr : (contact hres hfinite z c hz v p : ℝ) * ((1+2*(sigma : ℝ))*N) ≤
        (WeightedPolynomialPole.coordinateOrder p.valuation
          (MvPolynomial.aeval z (polynomialFrameWord m word F)) : ℝ) := by
      exact_mod_cast hq
    simpa only [mul_comm] using hr
  · calc
      (N : ℝ) * CurveContactSum.weightedDegree hfinite z w <
          N * ((1+(sigma : ℝ)) * ∑ p ∈ places hfinite z c hz,
            (contact hres hfinite z c hz v p : ℝ)) := mul_lt_mul_of_pos_left hexcess hNR
      _ = (1+(sigma : ℝ)) * (N * ∑ p ∈ places hfinite z c hz,
          (contact hres hfinite z c hz v p : ℝ)) := by ring
      _ ≤ (1+2*(sigma : ℝ)) * (N * ∑ p ∈ places hfinite z c hz,
          (contact hres hfinite z c hz v p : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hNR.le hsum)
      _ = _ := by ring

theorem ordinary_words_vanish
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin m → E) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ ((fibre x) i))
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma) (N : ℕ) (hN : 0 < N)
    (F : OrdinaryDerivatives.Polynomial m)
    (hF : WeightedSliceDegree.SupportBound (fun i => (w i.succ : ℝ)) N F)
    (hjet : ∀ j, OrdinaryAuxiliaryJet.formalJet (c j) F ∈
      JetGeometry.rationalWeightedIdeal (fun i => v i.succ) (fun i => (hv i.succ).le) ((1+3*sigma)*N))
    (hexcess : CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite (fibre x) c hz, (contact hres hfinite (fibre x) c hz v p : ℝ)) :
    ∀ word : List (Fin m),
      DerivativeIdeals.wordCost (fun i => (v i.succ : ℝ)) word ≤ (sigma : ℝ)*N →
        MvPolynomial.aeval x (OrdinaryDerivatives.word m word F) = 0 := by
  intro word hword
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsigR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have hcost : (word.map (fun i => v i.succ)).sum ≤ sigma*N := by
    change (word.map (fun i => (v i.succ : ℝ))).sum ≤ (sigma : ℝ)*N at hword
    rw [← cast_word_cost (fun i => v i.succ) word] at hword
    exact_mod_cast hword
  have hdegree : ∀ d ∈ (OrdinaryDerivatives.word m word F).support,
      Finsupp.weight (fun i => (w i.succ : ℝ)) d ≤ (N : ℝ) := by
    exact OrdinaryDerivatives.supportBound_word _ _ F hF
      (fun i => by exact_mod_cast (hw i.succ).le) word
  have hsum : 0 ≤ ∑ p ∈ places hfinite (fibre x) c hz, (contact hres hfinite (fibre x) c hz v p : ℝ) := by
    apply Finset.sum_nonneg
    intro p hp
    exact_mod_cast contact_nonneg hres hfinite (fibre x) c hz v hv p
  apply CurveContactSum.polynomial_eq_zero_of_excess_contact hfinite x (fun i => w i.succ) (fun i => hw i.succ)
    (N : ℝ) ((1+2*(sigma : ℝ))*N) hNR.le (OrdinaryDerivatives.word m word F) hdegree
    (places hfinite (fibre x) c hz) (fun p => (contact hres hfinite (fibre x) c hz v p : ℝ))
  · intro hne p hp
    have hret : (1+2*sigma)*(N : ℚ) ≤ (1+3*sigma)*N - (word.map (fun i => v i.succ)).sum := by
      nlinarith
    have hlocal := ordinaryWord_order_lower hres hfinite x c hz v hv ((1+3*sigma)*N)
      F hjet word hne p hp
    have hq := (mul_le_mul_of_nonneg_left hret
      (contact_nonneg hres hfinite (fibre x) c hz v hv p)).trans hlocal
    have hr : (contact hres hfinite (fibre x) c hz v p : ℝ) * ((1+2*(sigma : ℝ))*N) ≤
        (WeightedPolynomialPole.coordinateOrder p.valuation
          (MvPolynomial.aeval x (OrdinaryDerivatives.word m word F)) : ℝ) := by
      exact_mod_cast hq
    simpa only [mul_comm] using hr
  · calc
      (N : ℝ) * CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) <
          N * ((1+(sigma : ℝ)) * ∑ p ∈ places hfinite (fibre x) c hz,
            (contact hres hfinite (fibre x) c hz v p : ℝ)) := mul_lt_mul_of_pos_left hexcess hNR
      _ = (1+(sigma : ℝ)) * (N * ∑ p ∈ places hfinite (fibre x) c hz,
          (contact hres hfinite (fibre x) c hz v p : ℝ)) := by ring
      _ ≤ (1+2*(sigma : ℝ)) * (N * ∑ p ∈ places hfinite (fibre x) c hz,
          (contact hres hfinite (fibre x) c hz v p : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hNR.le hsum)
      _ = _ := by ring

end PiExponent.CurveDerivativeVanishing
end

end OAI
