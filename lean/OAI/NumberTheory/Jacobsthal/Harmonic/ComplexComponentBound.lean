import OAI.NumberTheory.Jacobsthal.Analysis.RealCoefficientNormalization

namespace OAI

namespace Erdos970

section

open Set
open scoped ComplexConjugate
namespace ErdosComplexCurveFactors
open ErdosCriticalGeometry ErdosImplicitCurvature ErdosAlgebraicCurve ErdosMarkedStrips

theorem nonreal_component_card_bound (F : MV ℂ) (hF : Irreducible F)
    (hdeg : 1 < F.totalDegree) (hreal : ¬RealScalable F) (S : ℝ) :
    (complexSquarePoints F S).card ≤ 2*F.totalDegree^3 := by
  have hnd := nonreal_not_dvd_conjugate F hF hreal
  obtain ⟨hfinite,hcard⟩ := irreducible_intersection_bound F (conjugate F) hF hdeg hnd
  have hmap : ∀ p ∈ (complexSquarePoints F S : Set (ℤ × ℤ)),
      complexIntPoint p ∈ intersectionPoints F (conjugate F) := by
    intro p hp
    have hz := ((mem_complexSquarePoints F S p).mp hp).2
    change MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] F = 0 ∧
      MvPolynomial.eval ![(p.1 : ℂ),(p.2 : ℂ)] (conjugate F) = 0
    refine ⟨hz,?_⟩
    simpa only [Complex.ofReal_intCast,hz,map_zero] using eval_conjugate_real F p.1 p.2
  have hc := ncard_le_ncard_of_injOn complexIntPoint hmap complexIntPoint_injective.injOn hfinite
  simp only [ncard_coe_finset] at hc
  calc
    _ ≤ _ := hc
    _ ≤ _ := hcard
    _ = 2*F.totalDegree^3 := by rw [conjugate_totalDegree]; ring

theorem realScalable_component_bound (F : MV ℂ) (hF : Irreducible F)
    (hdeg : 1 < F.totalDegree) (hreal : RealScalable F) (S : ℝ) (hS : 0 ≤ S) :
    ((complexSquarePoints F S).card : ℝ) ≤
      182*(F.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) := by
  obtain ⟨a,ha,R,rfl⟩ := hreal
  have hR := (scalar_irreducible_iff a ha (complexify R)).mp hF
  have hd : 1 < R.totalDegree := by
    simpa only [scalar_totalDegree a ha,complexify_totalDegree] using hdeg
  simpa only [complexSquare_scalar a ha,complexSquare_complexify,scalar_totalDegree a ha,
    complexify_totalDegree] using absolutely_irreducible_curve_lattice_bound R hR hd S hS

theorem irreducible_complex_curve_bound (F : MV ℂ) (hF : Irreducible F)
    (hdeg : 1 < F.totalDegree) (S : ℝ) (hS : 0 ≤ S) :
    ((complexSquarePoints F S).card : ℝ) ≤
      182*(F.totalDegree : ℝ)^3*(1+S^((2 : ℝ)/3)) := by
  by_cases hreal : RealScalable F
  · exact realScalable_component_bound F hF hdeg hreal S hS
  · have h := nonreal_component_card_bound F hF hdeg hreal S
    have hB : 1 ≤ 1+S^((2 : ℝ)/3) := le_add_of_nonneg_right (Real.rpow_nonneg hS _)
    calc
      ((complexSquarePoints F S).card : ℝ) ≤ 2*(F.totalDegree : ℝ)^3 := by exact_mod_cast h
      _ ≤ 182*(F.totalDegree : ℝ)^3 := by gcongr; norm_num
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hB

end ErdosComplexCurveFactors

end

end Erdos970

end OAI
