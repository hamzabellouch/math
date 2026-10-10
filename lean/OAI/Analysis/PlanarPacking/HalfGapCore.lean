import OAI.Analysis.PlanarPacking.JetError
import OAI.Analysis.PlanarPacking.BernsteinBoxes
import OAI.Analysis.PlanarPacking.TaylorControl

namespace OAI

namespace SharpPlanar
open scoped BigOperators
lemma normalizedH_eq (a : Bool) (m : ℝ) (ell : ℕ) :
    normalizedH a m ell=tableHJet a ell m/(ell.factorial:ℝ) := by
  rw [normalizedH,fullMoment_direct,fullMoment_transformed]
  exact (add_div _ _ _).symm
lemma sourcePower_sum (a : Bool) (m y v : ℝ) (nu d : ℕ) :
    (∑ r ∈ Finset.range (d+1), sourcePower a m y nu r*v^r)=
      (if a then 1 else -1)*deletedPolynomial (tableHJet a) nu d m (y*v) := by
  simp only [sourcePower,normalizedH_eq,deletedPolynomial,Finset.mul_sum,mul_pow]
  apply Finset.sum_congr rfl
  intro r hr
  ring
lemma sourcePower_lower {a : Bool} {m y v L : ℝ} {nu : ℕ}
    (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k : Fin 29,L ≤ powerToBernstein 28 (sourcePower a m y nu) k.val) :
    L ≤ (if a then 1 else -1)*deletedPolynomial (tableHJet a) nu 28 m (y*v) := by
  rw [← sourcePower_sum]
  apply bernstein_lower hv
  intro k hk
  exact hB ⟨k,Finset.mem_range.mp hk⟩
lemma scaled_remainder_bound {x z Z E R f g : ℝ}
    (hx : 0 ≤ x) (hr : 0 ≤ R) (hz : z ≤ Z) (hg : 0 ≤ g) :
    E*x/f+R*(x*z)/g ≤ x*(E/f+R*Z/g) := by
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hz (mul_nonneg hr hx)) hg
  calc
    _ = E*x/f+(R*x*z)/g := by ring
    _ ≤ E*x/f+(R*x*Z)/g := by linarith only [hh]
    _ = _ := by ring
lemma signed_error_lower (a : Bool) {J P x A B L : ℝ}
    (he : |J-x*P|≤x*(A+B)) (hl : x*L ≤ x*((if a then 1 else -1)*P)) :
    (L-A-B)*x ≤ (if a then 1 else -1)*J := by
  cases a <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hl ⊢ <;>
    nlinarith [(abs_le.mp he).1,(abs_le.mp he).2]

lemma halfGap_lower {a : Bool} {m y v Y E R L : ℝ} {nu : ℕ}
    (hv : v ∈ Set.Icc 0 1) (hu : |y*v| ≤ Y) (hpow : (y*v)^nu=|y*v|^nu)
    (hj : ∀ k<nu,exactJet a k m=0)
    (hE : ∀ s ∈ Set.uIcc m (m+y*v), |exactJet a nu s-tableHJet a nu s|≤E)
    (hR : ∀ s ∈ Set.uIcc m (m+y*v), |tableHJet a (nu+29) s|≤R)
    (hB : ∀ k : Fin 29,L ≤ powerToBernstein 28 (sourcePower a m y nu) k.val) :
    (L-E/(nu.factorial:ℝ)-R*Y^29/((nu+29).factorial:ℝ))*|y*v|^nu ≤
      (if a then 1 else -1)*exactJet a 0 (m+y*v) := by
  have herr := deletedPolynomial_error (exactJet_deriv a) (tableHJet_deriv a)
    nu 28 m (y*v) E R hj hE hR
  have hr0 : 0 ≤ R := (abs_nonneg _).trans (hR m Set.left_mem_uIcc)
  have hn0 : 0 ≤ |y*v|^nu := pow_nonneg (abs_nonneg _) _
  have hu29 : |y*v|^29 ≤ Y^29 := pow_le_pow_left₀ (abs_nonneg _) hu _
  have her := scaled_remainder_bound (E := E) (f := (nu.factorial:ℝ))
    (g := ((nu+29).factorial:ℝ)) hn0 hr0 hu29 (Nat.cast_nonneg _)
  rw [← pow_add] at her
  have hh : |exactJet a 0 (m+y*v)-(y*v)^nu*deletedPolynomial (tableHJet a) nu 28 m (y*v)| ≤
      |y*v|^nu*(E/(nu.factorial:ℝ)+R*Y^29/((nu+29).factorial:ℝ)) := herr.trans her
  have hl := mul_le_mul_of_nonneg_left (sourcePower_lower hv hB) hn0
  rw [hpow] at hh
  exact signed_error_lower a hh hl
lemma exactJet_zero_false (s : ℝ) : exactJet false 0 s=H₁ s := by
  rw [exactJet,← cardinal_eq_cardinalSeries]
  rfl
lemma exactJet_zero_true (s : ℝ) : exactJet true 0 s=H₂ s := by
  rw [exactJet,← cardinal_eq_cardinalSeries]
  rfl
lemma exactJet_one_false (s : ℝ) : exactJet false 1 s=deriv H₁ s := (H₁_hasDerivAt s).deriv.symm
lemma exactJet_one_true (s : ℝ) : exactJet true 1 s=deriv H₂ s := (H₂_hasDerivAt s).deriv.symm
lemma exactJet_node_zero (a : Bool) (n : Node) : exactJet a 0 n.val=0 := by
  cases a
  · rw [exactJet_zero_false]; exact (H₁_jets n).1
  · rw [exactJet_zero_true]; exact (H₂_jets n).1
lemma exactJet_node_first (a : Bool) (n : Node) (hn : n.val≠1 ∨ a=true) :
    exactJet a 1 n.val=0 := by
  cases a
  · rw [exactJet_one_false,(H₁_jets n).2,ite_eq_right (by simpa using hn)]
  · rw [exactJet_one_true]; exact (H₂_jets n).2
end SharpPlanar

end OAI
