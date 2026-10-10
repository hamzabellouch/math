import OAI.Geometry.TranslativeCovering.MatchingSelf

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2

namespace PoissonDiagrams
open MeasureTheory CellMatching MatchingBounds MatchingSelf
open scoped Classical BigOperators
variable {Ω : Type u_1} {I : Type u_2} [MeasurableSpace Ω] [Fintype I]

lemma self_bound (μ : Measure Ω) (E : I → Set Ω)
    (hpos : ∀ i, 0 < μ.real (E i)) :
    1 + diagram μ E E / (∏ i, μ.real (E i))^2 ≤
      (∏ i, (1 + (μ.real (E i))⁻¹)) *
        ∏ i, (1 + ∑ j ∈ Finset.univ.erase i,
          μ.real (E i ∩ E j) /
            Real.sqrt (μ.real (E i) * (1+μ.real (E i)) *
              μ.real (E j) * (1+μ.real (E j)))) := by
  let lam := fun i => μ.real (E i)
  let h := fun e : I × I => μ.real (E e.1 ∩ E e.2) / (lam e.1*lam e.2)
  have hdiag (i : I) : h (i,i) = (lam i)⁻¹ := by
    dsimp only [h, lam]
    rw [Set.inter_self]
    field_simp [(hpos i).ne']
  have hnorm (i j : I) : h (i,j) /
      (Real.sqrt (1+h (i,i)) * Real.sqrt (1+h (j,j))) =
      μ.real (E i ∩ E j) /
        Real.sqrt (lam i * (1+lam i) * lam j * (1+lam j)) := by
    rw [hdiag, hdiag]
    have hi := hpos i
    have hj := hpos j
    change 0 < lam i at hi
    change 0 < lam j at hj
    have hi' : 0 ≤ 1+(lam i)⁻¹ := by positivity
    have hj' : 0 ≤ 1+(lam j)⁻¹ := by positivity
    have hroot : Real.sqrt (lam i*(1+lam i)*lam j*(1+lam j)) =
        lam i*lam j*(Real.sqrt (1+(lam i)⁻¹)*Real.sqrt (1+(lam j)⁻¹)) := by
      have he : lam i*(1+lam i)*lam j*(1+lam j) =
          (lam i*lam j)^2 * ((1+(lam i)⁻¹)*(1+(lam j)⁻¹)) := by
        field_simp
        ring
      rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hi.le hj.le),
        Real.sqrt_mul hi']
    rw [hroot]
    dsimp only [h]
    rw [div_div]
  have hh : ∀ e, 0 ≤ h e := fun e => div_nonneg (measureReal_nonneg)
    (mul_nonneg (hpos e.1).le (hpos e.2).le)
  have hb := self_matching_bound h hh
  rw [all_matchings_eq] at hb
  simp_rw [hnorm, hdiag] at hb
  convert! hb using 1
  unfold diagram
  have hp : (∏ i, μ.real (E i)) ≠ 0 := ne_of_gt (Finset.prod_pos (fun i _ => hpos i))
  dsimp only [h, lam]
  field_simp

end PoissonDiagrams

end OAI
