import OAI.NumberTheory.Ostmann.Conclusion.RegularNormProduct
import OAI.NumberTheory.Ostmann.Conclusion.RegularNormScale
import OAI.NumberTheory.Ostmann.Conclusion.RegularNormTuple

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open Filter
open scoped BigOperators
open Ostmann.Construction

theorem actual_regular_tuple_eventually :
    ∀ᶠ L : ℝ in atTop, ∀ (d : Decomposition) (P : Finset ℕ)
      (c : ℝ) (hZ : 0<logCellMass c ∅) (small : List SmallSlot),
      Real.exp ((1/20:ℝ)*L)-2≤c → c≤Real.exp ((9/10:ℝ)*L)+2 →
      (small.length:ℝ)≤Real.exp ((1/1000:ℝ)*L) →
      (∀z∈small,Nat.Prime z.value ∧ Real.exp ((1/250:ℝ)*L)≤Real.log (z.value:ℝ) ∧
        Real.log (z.value:ℝ)≤Real.exp ((11/1000:ℝ)*L)) →
      ∀ (outside : List ℕ) (s : ℤ) (q : ℕ),
      (logCellPrior c ∅ hZ).mean (fun p =>
        ‖supportedRegularTransform (residueTransform d) (favorableGiantResidueTransform d P)
          outside (State.mk s p.val q small)‖^2)≤18 := by
  obtain ⟨dAP,K,L₀,hd,hK,hL₀,hbound⟩ := exists_actual_regular_tuple_bound
  filter_upwards [regular_numeric_scale_eventually dAP K L₀ hd hK] with L hL
  intro d P c hZ small hclo hchi hlen hsmall outside s q
  have hprime (i : Fin small.length) : Nat.Prime small[i].value := (hsmall _ (List.getElem_mem i.isLt)).1
  let : ∀i : Fin small.length,Fact small[i].value.Prime := fun i => ⟨hprime i⟩
  let : NeZero (regularSmallModulus small) := ⟨Finset.prod_ne_zero_iff.mpr
    (fun i _ => (hprime i).ne_zero)⟩
  have hprod : (regularSmallModulus small:ℝ)≤Real.exp (Real.exp ((3/250:ℝ)*L)) := by
    have hh := regular_prime_product_le_exp (fun i : Fin small.length => small[i].value)
      (fun i => (hprime i).pos)
      (fun i => (hsmall _ (List.getElem_mem i.isLt)).2.2)
    refine hh.trans (Real.exp_le_exp.mpr ?_)
    simp only [Fintype.card_fin]
    calc
      _ ≤ Real.exp ((1/1000:ℝ)*L)*Real.exp ((11/1000:ℝ)*L) :=
        mul_le_mul_of_nonneg_right hlen (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  have hn := hL.2.2.2 c (regularSmallModulus small) hclo hchi (Nat.cast_nonneg _) hprod
  apply hbound d P c hn.1 hn.2.1 hZ small (fun z hz => (hsmall z hz).1) hn.2.2.1
  · intro hcop
    apply regular_prime_product_ratio_le _ hcop
    have hsingle (i : Fin small.length) :
        1/((small[i].value:ℝ)-1)≤2/Real.exp ((1/250:ℝ)*L) := by
      have hp := hprime i
      have hpr : (0:ℝ)<small[i].value := by exact_mod_cast hp.pos
      have hpl : Real.exp ((1/250:ℝ)*L)≤Real.log (small[i].value:ℝ) :=
        (hsmall _ (List.getElem_mem i.isLt)).2.1
      have hlog := Real.log_le_sub_one_of_pos hpr
      have hden : 0<(small[i].value:ℝ)-1 := by
        have hh : (1:ℝ)<small[i].value := by exact_mod_cast hp.one_lt
        linarith
      apply (div_le_div_iff₀ hden (Real.exp_pos _)).mpr
      nlinarith [hL.2.2.1]
    calc
      _ ≤ ∑ _ : Fin small.length,2/Real.exp ((1/250:ℝ)*L) :=
        Finset.sum_le_sum (fun i _ => hsingle i)
      _ = (small.length:ℝ)*(2/Real.exp ((1/250:ℝ)*L)) := by simp
      _ ≤ Real.exp ((1/1000:ℝ)*L)*(2/Real.exp ((1/250:ℝ)*L)) := by gcongr
      _ = 2*Real.exp ((1/1000:ℝ)*L)/Real.exp ((1/250:ℝ)*L) := by ring
      _ ≤ Real.log 2 := hL.2.1
  · exact hn.2.2.2.1
  · exact hn.2.2.2.2

end Ostmann.Conclusion

end

end OAI
