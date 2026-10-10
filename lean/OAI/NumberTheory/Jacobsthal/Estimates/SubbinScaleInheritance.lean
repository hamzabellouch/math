import OAI.NumberTheory.Jacobsthal.Primes.CanonicalTagPrimePartition

namespace OAI

namespace Erdos970


namespace ErdosStoppedSubbinAggregation
open ErdosTagSubbins ErdosInversePrimeBin

theorem subbin_scale_inheritance {R theta w Cs xi lowerBound : ℝ}
    (hw : 1 < w) (hCs : 0 ≤ Cs) (hR : 0 < R)
    (hxi : 0 < xi) (htxi : xi/4 ≤ theta) (ht1 : theta ≤ 1)
    (hLower : lowerBound ≤ R) (i : Fin (count w Cs)) :
    0 < left R theta (count w Cs) i ∧ 0 < step R theta (count w Cs) ∧
      lowerBound ≤ left R theta (count w Cs) i ∧
      left R theta (count w Cs) i ≤ (1+theta)*R ∧
      xi/(16*w^(2*Cs+10)) ≤ step R theta (count w Cs)/left R theta (count w Cs) i ∧
      step R theta (count w Cs)/left R theta (count w Cs) i ≤ w^(-(2*Cs+10)) ∧
      left R theta (count w Cs) i + step R theta (count w Cs) ≤ (1+theta)*R := by
  have ht : 0 < theta := (div_pos hxi (by norm_num)).trans_le htxi
  have hN : 0 < count w Cs := (count_bounds hw hCs).1
  refine ⟨left_pos hR ht hN,step_pos hR ht hN,
    hLower.trans (left_lower (step_pos hR ht hN).le),
    (left_lt_right hR ht hN).le.trans (right_upper hR ht i.isLt),
    width_lower hR hxi htxi ht1 hw hCs i.isLt,?_,?_⟩
  · simpa only [width,show -2*Cs-10=-(2*Cs+10) by ring] using
      (width_upper (i:=i) hR ht ht1 hw hCs)
  · rw [← right_eq_left_add]
    exact right_upper hR ht i.isLt

theorem subbin_inherits_band {R theta : ℝ} {N : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (hN : 0 < N) (band : ℝ → Prop)
    (hband : ∀ x ∈ Set.Icc R ((1+theta)*R),band x) (i : Fin N) :
    band (left R theta N i) := by
  apply hband
  exact ⟨left_lower (step_pos hR ht hN).le,
    (left_lt_right hR ht hN).le.trans (right_upper hR ht i.isLt)⟩

end ErdosStoppedSubbinAggregation


end Erdos970

end OAI
