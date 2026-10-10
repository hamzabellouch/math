import OAI.Analysis.Pureness.States.FiniteFamilyExtremalRestriction
import OAI.Analysis.Pureness.States.QuotientCentralValueDensity

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace
open scoped ComplexOrder
variable {A D : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))
variable (F : CompatibleFiniteQuasitrace (T.CauchyQuotient hadd))
variable (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix (T.CauchyQuotient hadd) n) => (F.level n a.1).re))
variable (hF : F.level 1 1=1)
variable (c : ℂ) (hval : ∀ x, F.toTwoQuasitrace.base x = c*T.quotientValue hadd hsqrt x)
variable (α : A →⋆ₐ[ℂ] T.CauchyQuotient hadd)
variable (hcover : ∀ a : D, ∃ b : A, α b = T.quotientEmbedding hadd a)
variable (hext : (fun x => F.toTwoQuasitrace.base (α x)) ∈
  (normalizedFiniteBaseQuasitraceCarrier (A := A)).extremePoints ℝ)

include hmono hF hval hcover hext

theorem finiteFamily_extreme_completion_central_projection_split
    (p : T.CauchyQuotient hadd) (hp : IsStarProjection p) (hc : ∀ x, Commute p x)
    (hp0 : 0 < (F.toTwoQuasitrace.base p).re) (hq0 : 0 < (F.toTwoQuasitrace.base (1-p)).re)
    (x : T.CauchyQuotient hadd) : F.toTwoQuasitrace.base (p*x) = F.toTwoQuasitrace.base p*F.toTwoQuasitrace.base x := by
  rw [hval (p*x), hval x]
  apply T.scaled_quotientValue_mul_of_embedding hadd hsqrt c (F.toTwoQuasitrace.base p) p
  intro a
  obtain ⟨b, hb⟩ := hcover a
  have he := finiteFamily_extreme_restriction_central_projection_split F hmono hF α hext p hp hc hp0 hq0 b
  rwa [hb, hval (p*T.quotientEmbedding hadd a), hval (T.quotientEmbedding hadd a)] at he

theorem finiteFamily_extreme_completion_central_projection_value
    (p : T.CauchyQuotient hadd) (hp : IsStarProjection p) (hc : ∀ x, Commute p x) :
    F.toTwoQuasitrace.base p = 0 ∨ F.toTwoQuasitrace.base p = 1 := by
  by_cases h0 : F.toTwoQuasitrace.base p = 0
  · exact Or.inl h0
  by_cases h1 : F.toTwoQuasitrace.base p = 1
  · exact Or.inr h1
  exfalso
  have hsum : F.toTwoQuasitrace.base p+F.toTwoQuasitrace.base (1-p)=1 := by
    simpa only [mul_one, F.toTwoQuasitrace_unit hF] using (F.toTwoQuasitrace.base.central_projection_split p hp hc 1).symm
  have hq0 : F.toTwoQuasitrace.base (1-p) ≠ 0 := by
    intro hz
    exact h1 (by simpa only [hz, add_zero] using hsum)
  have hpR := Complex.eq_re_of_ofReal_le (F.toTwoQuasitrace.base.nonneg p hp.nonneg)
  have hqR := Complex.eq_re_of_ofReal_le (F.toTwoQuasitrace.base.nonneg (1-p) hp.one_sub.nonneg)
  have hp0 : 0 < (F.toTwoQuasitrace.base p).re := lt_of_le_of_ne
    (F.toTwoQuasitrace.base.nonneg p hp.nonneg).1 (by intro hz; exact h0 (hpR.trans (by simp [← hz])))
  have hqpos : 0 < (F.toTwoQuasitrace.base (1-p)).re := lt_of_le_of_ne
    (F.toTwoQuasitrace.base.nonneg (1-p) hp.one_sub.nonneg).1
    (by intro hz; exact hq0 (hqR.trans (by simp [← hz])))
  have he := T.finiteFamily_extreme_completion_central_projection_split hadd hsqrt F hmono hF c hval α hcover
    hext p hp hc hp0 hqpos p
  rw [hp.isIdempotentElem.eq] at he
  have hm : F.toTwoQuasitrace.base p * (F.toTwoQuasitrace.base p-1) = 0 := by linear_combination -he
  exact h1 (sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left h0))

theorem finiteFamily_faithful_extreme_completion_central_projection
    (hfaith : ∀ x, F.toTwoQuasitrace.base (star x*x)=0 ↔ x=0)
    (p : T.CauchyQuotient hadd) (hp : IsStarProjection p) (hc : ∀ x, Commute p x) :
    p=0 ∨ p=1 := by
  rcases T.finiteFamily_extreme_completion_central_projection_value hadd hsqrt F hmono hF c hval α hcover
    hext p hp hc with h0 | h1
  · left
    apply (hfaith p).mp
    rwa [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  · right
    have hsum := F.toTwoQuasitrace.base.central_projection_split p hp hc 1
    simp only [mul_one, F.toTwoQuasitrace_unit hF, h1] at hsum
    have hzero : F.toTwoQuasitrace.base (1-p)=0 := by linear_combination -hsum
    have hqzero : 1-p=0 := (hfaith (1-p)).mp (by
      rwa [hp.one_sub.isSelfAdjoint.star_eq, hp.one_sub.isIdempotentElem.eq])
    exact (sub_eq_zero.mp hqzero).symm
end CuntzPureness.PositiveQuasitrace

end

end OAI
