import OAI.NumberTheory.Ostmann.Conclusion.RegularNormCellEstimate
import OAI.NumberTheory.Ostmann.Conclusion.RegularNormResidue

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open scoped BigOperators
open Ostmann.Construction Ostmann.Arithmetic.PrimeCellReplacement

def regularSmallUnitTest (g : (p : ℕ) → ZMod p → ℂ)
    (outside : List ℕ) (q : ℕ) (small : List SmallSlot) (s : ℤ)
    (hcop : Pairwise (fun i j : Fin small.length =>
      small[i].value.Coprime small[j].value))
    (u : (ZMod (regularSmallModulus small))ˣ) : ℝ :=
  regularResidueTestValue (fun i : Fin small.length => small[i].value)
    (fun i => g small[i].value) (regularSmallNumerator outside q small s)
    (Ostmann.Supply.crtUnitsEquiv (fun i : Fin small.length => small[i].value) hcop u)

theorem regularSmallUnitTest_nonneg (g : (p : ℕ) → ZMod p → ℂ)
    (outside : List ℕ) (q : ℕ) (small : List SmallSlot) (s : ℤ) (hcop) (u) :
    0 ≤ regularSmallUnitTest g outside q small s hcop u :=
  regularResidueTestValue_nonneg _ _ _ _

theorem regularSmallUnitTest_sum_le (g : (p : ℕ) → ZMod p → ℂ)
    (outside : List ℕ) (q : ℕ) (small : List SmallSlot) (s : ℤ)
    [∀ i : Fin small.length, Fact small[i].value.Prime]
    [NeZero (regularSmallModulus small)]
    (hcop : Pairwise (fun i j : Fin small.length =>
      small[i].value.Coprime small[j].value))
    (hg0 : ∀ i : Fin small.length, g small[i].value 0=0)
    (hgnorm : ∀ i : Fin small.length,
      ∑ x : ZMod small[i].value, ‖g small[i].value x‖^2 = (small[i].value : ℝ)) :
    ∑ u, regularSmallUnitTest g outside q small s hcop u ≤
      (regularSmallModulus small : ℝ) :=
  regularResidueTestValue_crt_sum_le _ hcop _ hg0 hgnorm _

theorem supportedRegularTransform_sq_le_unitTest
    (g giant : (p : ℕ) → ZMod p → ℂ) (hg : ∀ p x, ‖giant p x‖ ≤ 1)
    (outside : List ℕ) (s : ℤ) (p q : ℕ) (small : List SmallSlot)
    [∀ i : Fin small.length, Fact small[i].value.Prime]
    [NeZero (regularSmallModulus small)]
    (hcop : Pairwise (fun i j : Fin small.length =>
      small[i].value.Coprime small[j].value)) :
    ‖supportedRegularTransform g giant outside (State.mk s p q small)‖^2 ≤
      unitTest (regularSmallUnitTest g outside q small s hcop)
        (p : ZMod (regularSmallModulus small)) := by
  classical
  by_cases hs : (State.mk s p q small).Coprime outside ∧ s ≠ 0
  · have hpM := supported_regular_giant_coprime p q s small outside hs.1
    let u : (ZMod (regularSmallModulus small))ˣ := ZMod.unitOfCoprime p hpM
    have hu : (u : ZMod (regularSmallModulus small)) = p := ZMod.coe_unitOfCoprime p hpM
    rw [←hu,unitTest_unit]
    simp only [supportedRegularTransform,ite_eq_left hs]
    refine (regularTransform_norm_sq_le g giant hg outside s p q small).trans_eq ?_
    unfold regularSmallUnitTest regularResidueTestValue
    apply Finset.prod_congr rfl
    intro i hi
    have hr : small[i].value ∣ regularSmallModulus small :=
      Finset.dvd_prod_of_mem (fun i : Fin small.length => small[i].value) (Finset.mem_univ i)
    have hprod : (State.mk s p q small).product=p*q*regularSmallModulus small := by
      rw [regularSmallModulus_eq]
      simp only [State.product,State.values,List.prod_cons]
      ring
    rw [hprod,regular_modFraction_small p q (outsideProduct outside)
      (regularSmallModulus small) s hr]
    rw [Ostmann.Supply.crtUnitsEquiv_apply,hu]
    simp only [map_natCast,regularSmallNumerator]
  · simp only [supportedRegularTransform,ite_eq_right hs,norm_zero,zero_pow (by decide : 2 ≠ 0)]
    exact unitTest_nonneg _ (regularSmallUnitTest_nonneg g outside q small s hcop) _

end Ostmann.Conclusion

end

end OAI
