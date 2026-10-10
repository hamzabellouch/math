import Mathlib
import OAI.Combinatorics.UniformKServer.ShortRosterValidity
import OAI.Combinatorics.UniformKServer.RosterTails

namespace OAI

                                    
section
namespace UniformKServer.TierInsertion
noncomputable section
open PilotCompact TierPilot ShortRoster ChronologicalRoster

def gainCoefficient (P : Parameters) : ℝ := min (1/2) (128*P.deltaH)

def lifetimeExponent (P : Parameters) : ℝ :=
  2*(Real.log (2*257*49/gainCoefficient P)+3)

variable {I X : Type} [Fintype I] [LinearOrder I] [Fintype X] [MetricSpace X]
omit [Fintype I] [LinearOrder I] [Fintype X] [MetricSpace X] in
theorem coefficient_bounds (P : Parameters) : 0 < gainCoefficient P ∧ gainCoefficient P ≤ 1/2 := by
  exact ⟨lt_min (by norm_num) (mul_pos (by norm_num) P.deltaH_pos),min_le_left _ _⟩

omit [Fintype I] [LinearOrder I] [Fintype X] [MetricSpace X] in
theorem exponent_bounds (P : Parameters) (h : ℝ) (hh : 1 ≤ h) (K : ℕ)
    (hlarge : Real.exp (lifetimeExponent P*h) ≤ K) :
    257*(49/Real.sqrt (K:ℝ)) ≤ gainCoefficient P/2*Real.exp (-h) ∧
      1/(K:ℝ) ≤ gainCoefficient P/2*Real.exp (-2*h) := by
  let c := gainCoefficient P
  let A := 2*257*49/c
  have hc : 0 < c := (coefficient_bounds P).1
  have hcBound : c ≤ 1/2 := (coefficient_bounds P).2
  have hApos : 0 < A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by
    dsimp [A]
    apply (le_div_iff₀ hc).mpr
    linarith
  have hlog : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hk : 0 < (K:ℝ) := (Real.exp_pos _).trans_le hlarge
  have hs := Real.sqrt_pos.mpr hk
  have he : h+Real.log A ≤ lifetimeExponent P*h/2 := by
    change h+Real.log A ≤ (2*(Real.log A+3))*h/2
    nlinarith [mul_nonneg hlog (show 0 ≤ h-1 by linarith)]
  have hroot : Real.exp (lifetimeExponent P*h/2) ≤ Real.sqrt (K:ℝ) := by
    apply (Real.le_sqrt (Real.exp_nonneg _) hk.le).mpr
    rw [←Real.exp_nat_mul]
    convert hlarge using 1
    congr 1
    ring
  have hAs : A*Real.exp h ≤ Real.sqrt (K:ℝ) := by
    have := (Real.exp_le_exp.mpr he).trans hroot
    simpa [Real.exp_add,Real.exp_log hApos,mul_comm] using this
  have hinv : 257*(49/Real.sqrt (K:ℝ)) ≤ c/2*Real.exp (-h) := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hs).mpr
    have hAs' := mul_le_mul_of_nonneg_left hAs
      (show 0 ≤ c/2*Real.exp (-h) by positivity)
    have hid : c/2*Real.exp (-h)*(A*Real.exp h) = 257*49 := by
      have hex : Real.exp (-h)*Real.exp h=1 := by rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]
      calc
        _ = (c/2*A)*(Real.exp (-h)*Real.exp h) := by ring
        _ = 257*49 := by rw [hex]; dsimp [A]; field_simp
    rw [hid] at hAs'
    exact hAs'
  have hpay : 1/(K:ℝ) ≤ c/2*Real.exp (-2*h) := by
    have hsq := mul_self_le_mul_self (show 0 ≤ A*Real.exp h by positivity) hAs
    rw [Real.mul_self_sqrt hk.le] at hsq
    have ha2 : 2/c ≤ A^2 := by
      have hAc : A*c=2*257*49 := by dsimp [A]; field_simp
      apply (div_le_iff₀ hc).mpr
      nlinarith [mul_le_mul_of_nonneg_right hA1 hc.le]
    have hb := mul_le_mul_of_nonneg_right ha2 (sq_nonneg (Real.exp h))
    have he2 : Real.exp (2*h) = (Real.exp h)^2 := by rw [show 2*h=h+h by ring,Real.exp_add,pow_two]
    have hmain : (2/c)*Real.exp (2*h) ≤ K := by rw [he2]; nlinarith
    apply (div_le_iff₀ hk).mpr
    have hm := mul_le_mul_of_nonneg_left hmain (show 0 ≤ c/2*Real.exp (-2*h) by positivity)
    have hid : c/2*Real.exp (-2*h)*((2/c)*Real.exp (2*h)) = 1 := by
      have hex : Real.exp (-2*h)*Real.exp (2*h)=1 := by
        rw [←Real.exp_add,show -2*h+2*h=0 by ring,Real.exp_zero]
      calc
        _ = (c/2*(2/c))*(Real.exp (-2*h)*Real.exp (2*h)) := by ring
        _ = 1 := by rw [hex]; field_simp
    rw [hid] at hm
    exact hm
  exact ⟨hinv,hpay⟩
/-- The literal weighted insertion payment, with the auxiliary roster built
by independent lifetime experiments and a single fixed lifetime exponent. -/
theorem weighted_short_gain (P : Parameters) (D : State I) (S : Finset I)
    (c : I → X) (r h : ℝ) (hr : 0 < r) (hh : 1 ≤ h) (K : ℕ) (hK : 2 ≤ K)
    (hlarge : Real.exp (lifetimeExponent P*h) ≤ K)
    (hq : 1/Real.sqrt (K:ℝ) ∈ Set.Icc (0:ℝ) 1)
    (n : I) (hD : D.Valid S c r K (1/Real.sqrt (K:ℝ)))
    (hn : ∀ i ∈ S, i < n)
    (htest : ∀ i ∈ young S c r K, r/2 < dist (c n) (c i))
    (μ : X → ℝ) (hμ : ∀ p, 0 ≤ μ p)
    (hM : 0 < ballMass r P.gammaH μ (c n))
    (hqual : ballMass r 20480000 μ (c n) ≤ Real.exp h*ballMass r P.gammaL μ (c n)) :
    r*insertionMass P r μ (c n)/(K:ℝ) ≤
      Real.exp (-h)*(value r P.sigma 204800 μ (D.parameter c r)-
        value r P.sigma 204800 μ
          ((D.next S c r K (1/Real.sqrt (K:ℝ)) hq n).parameter c r))
 := by
  let q := 1/Real.sqrt (K:ℝ)
  let ε := q+(K:ℝ)*(1-q)^(K-1)
  have hε : 0 ≤ ε := by
    dsimp only [ε]
    exact add_nonneg hq.1 (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith [hq.2]) _))
  have he := short_edit D S c r hr K (by omega) q hq n hD hn htest
  have hg := insertion_gain P r ε h hr hε hh μ (D.parameter c r)
    ((D.next S c r K q hq n).parameter c r) hμ (c n) hM hqual he
  have ht : ε ≤ 49/Real.sqrt (K:ℝ) := RosterTails.short_tail K hK
  obtain ⟨herr,hpay⟩ := exponent_bounds P h hh K hlarge
  have herr' : 257*ε ≤ gainCoefficient P/2*Real.exp (-h) :=
    (mul_le_mul_of_nonneg_left ht (by norm_num)).trans herr
  have hW := (insertionMass_bounds P r hr.le μ hμ (c n)).1
  have hrW : 0 ≤ r*insertionMass P r μ (c n) := mul_nonneg hr.le hW
  have hdrop : r*insertionMass P r μ (c n)*(gainCoefficient P/2*Real.exp (-h)) ≤
      value r P.sigma 204800 μ (D.parameter c r)-
        value r P.sigma 204800 μ ((D.next S c r K q hq n).parameter c r) := by
    apply le_trans _ hg
    apply mul_le_mul_of_nonneg_left _ hrW
    change _ ≤ gainCoefficient P*Real.exp (-h)-257*ε
    linarith
  have hw := mul_le_mul_of_nonneg_left hdrop (Real.exp_nonneg (-h))
  have heq : Real.exp (-h)*Real.exp (-h)=Real.exp (-2*h) := by
    rw [←Real.exp_add]; congr 1; ring
  have hpayment := mul_le_mul_of_nonneg_left hpay hrW
  calc
    _ = (r*insertionMass P r μ (c n))*(1/(K:ℝ)) := by ring
    _ ≤ (r*insertionMass P r μ (c n))*(gainCoefficient P/2*Real.exp (-2*h)) := hpayment
    _ = Real.exp (-h)*(r*insertionMass P r μ (c n)*(gainCoefficient P/2*Real.exp (-h))) := by
      rw [←heq]; ring
    _ ≤ _ := hw
end
end UniformKServer.TierInsertion

end



end OAI
