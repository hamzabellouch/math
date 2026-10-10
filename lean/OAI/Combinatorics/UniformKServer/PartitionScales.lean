import Mathlib
import OAI.Combinatorics.UniformKServer.SmallScales
import OAI.Combinatorics.UniformKServer.PartitionSeparation

namespace OAI

                                      
section

/-! Final-map separation summed over geometric scales. The additive one in
the level estimate is charged only at nonheavy scales, not at every scale. -/
noncomputable section
namespace UniformKServer.PartitionScales
open Finset FiniteProbability FirstStructure GeometricMass
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N J : ℕ}

structure Input (X : Type) [Fintype X] [MetricSpace X] (N J : ℕ) where
  k : ℕ
  two : 2 ≤ k
  P : TierPilot.Parameters
  C : ℝ
  C_one : 1 ≤ C
  R : ℝ
  R_pos : 0< R
  q : ℝ
  q_pos : 0< q
  q_small : q ≤ 1/2
  shiftH : 51200*q ≤ P.gammaH
  shiftL : 20480000*q ≤ P.gammaL
  base : X
  center : Fin N → X
  μ : Fin N → X → ℝ
  μ_nonneg : ∀ n x, 0 ≤ μ n x
  μ_total : ∀ n, ∑ x, μ n x ≤ k
  served : ∀ n, 1 ≤ μ n (center n)

namespace Input

def level (I : Input X N J) (j : ℕ) : PartitionLevel.Input X N where
  k := I.k
  two := I.two
  P := I.P
  C := I.C
  C_one := I.C_one
  r := radius I.R I.q j
  r_pos := radius_pos I.R I.q I.R_pos I.q_pos j
  base := I.base
  center := I.center
  μ := I.μ
  μ_nonneg := I.μ_nonneg
  μ_total := I.μ_total
  served := I.served

def isNonheavy (I : Input X N J) (n : Fin N) (j : ℕ) : Prop :=
  nonheavy (I.μ n) (I.center n) I.R I.q I.P.gammaH 51200 I.P.deltaH j

theorem not_heavy (I : Input X N J) (n : Fin N) (j : ℕ) :
    I.isNonheavy n j ↔ ¬(I.level j).data.heavy n := by
  exact lt_iff_not_ge

theorem log_sum (I : Input X N J) (n : Fin N) :
    (∑ j∈range J, (I.level j).localLog n) ≤ Real.log I.k := by
  have hg : I.P.gammaL ≤ 20480000 := by linarith [I.P.gammaL_small,I.P.sigma_small]
  have h := GeometricMass.log_sum (I.μ n) (I.μ_nonneg n) (I.center n) (I.served n)
    I.k I.R I.q I.P.gammaL 20480000 (I.μ_total n) I.R_pos I.q_pos I.P.gammaL_pos.le hg 1 J
    (by simpa only [pow_one] using I.shiftL)
  simpa only [Nat.cast_one,one_mul,level,PartitionLevel.Input.localLog,logarithm] using h

theorem nonheavy_count (I : Input X N J) (n : Fin N) :
    ((range J).filter (I.isNonheavy n)).card ≤ Real.log I.k/Real.log (1+I.P.deltaH) := by
  have hg : I.P.gammaH ≤ 51200 := by linarith [I.P.gammaH_small]
  have h := GeometricMass.nonheavy_count (I.μ n) (I.μ_nonneg n) (I.center n) (I.served n)
    I.k I.R I.q I.P.gammaH 51200 I.P.deltaH (I.μ_total n) I.R_pos I.q_pos
    I.P.gammaH_pos.le hg I.P.deltaH_pos 1 J (by simpa only [pow_one] using I.shiftH)
  change (((range J).filter (nonheavy (I.μ n) (I.center n) I.R I.q I.P.gammaH 51200 I.P.deltaH)).card : ℝ) ≤ _
  simpa only [Nat.cast_one,one_mul] using h

def coefficient (I : Input X N J) : ℝ := 8+(16*I.C+33)*(1+1/Real.log (1+I.P.deltaH))

theorem separation (I : Input X N J) (n : Fin N) (p : X) :
    (∑ j∈range J, (I.level j).r*(I.level j).separation n p) ≤
      I.coefficient*(1+Real.log I.k)*dist (I.center n) p := by
  let d := dist (I.center n) p
  let A := 16*I.C+33
  have hd : 0 ≤ d := dist_nonneg
  have hA : 0 ≤ A := by dsimp [A]; linarith [I.C_one]
  have hr (j : ℕ) : 0<(I.level j).r := (I.level j).r_pos
  have hL (j : ℕ) : 0 ≤ (I.level j).localLog n := (I.level j).localLog_nonneg n
  have hp (j : ℕ) : (I.level j).r*(I.level j).separation n p ≤
      (if (I.level j).r ≤ 4*d then (I.level j).r else 0)+
      A*d*((if I.isNonheavy n j then 1 else 0)+(I.level j).localLog n) := by
    by_cases hs : (I.level j).r ≤ 4*d
    · rw [ite_eq_left hs]
      have h := mul_le_mul_of_nonneg_left ((I.level j).separation_le_one n p) (hr j).le
      have hnn : 0 ≤ (if I.isNonheavy n j then (1:ℝ) else 0)+(I.level j).localLog n := by
        split_ifs <;> linarith [hL j]
      nlinarith only [h,mul_nonneg (mul_nonneg hA hd) hnn]
    · rw [ite_eq_right hs,zero_add]
      have hshort : d<(I.level j).r/4 := by linarith
      by_cases hn : I.isNonheavy n j
      · rw [ite_eq_left hn]
        have h := (I.level j).short_separation n p hshort
        change (I.level j).r*(I.level j).separation n p ≤ A*(1+(I.level j).localLog n)*d at h
        calc
          _ ≤ A*(1+(I.level j).localLog n)*d := h
          _ = _ := by ring
      · rw [ite_eq_right hn]
        have hh : (I.level j).data.heavy n := by
          exact not_not.mp (fun h => hn ((I.not_heavy n j).mpr h))
        have hz := (I.level j).heavy_zero n p hh (by change d ≤ _; nlinarith only [hshort,(hr j).le])
        rw [hz,mul_zero,zero_add]
        exact mul_nonneg (mul_nonneg hA hd) (hL j)
  have hsum := sum_le_sum (s:=range J) (fun j _ => hp j)
  rw [sum_add_distrib,←mul_sum,sum_add_distrib] at hsum
  have hcount : (∑ j∈range J, if I.isNonheavy n j then (1:ℝ) else 0)=
      ((range J).filter (I.isNonheavy n)).card := by
    rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one]
  rw [hcount] at hsum
  have hsmall : (∑ j∈range J, if (I.level j).r ≤ 4*d then (I.level j).r else 0) ≤ 8*d := by
    have hc := SmallScales.small (I.R*I.q) I.q (4*d) (mul_pos I.R_pos I.q_pos).le I.q_pos.le
      (by linarith [I.q_small]) (by positivity) J
    have he (j : ℕ) : (I.level j).r=(I.R*I.q)*I.q^j := by dsimp [level,radius]; rw [pow_succ]; ring
    simp only [he]
    apply hc.trans
    apply (div_le_iff₀ (by linarith [I.q_small] : 0<1-I.q)).mpr
    nlinarith [I.q_small]
  have hlog : 0 ≤ Real.log I.k := Real.log_nonneg (by exact_mod_cast (show 1 ≤ I.k from le_trans (by decide) I.two))
  have hdelta : 0<Real.log (1+I.P.deltaH) := Real.log_pos (by linarith [I.P.deltaH_pos])
  have htot := add_le_add (I.nonheavy_count n) (I.log_sum n)
  have hmul := mul_le_mul_of_nonneg_left htot (mul_nonneg hA hd)
  have hz : 0 ≤ A*(1+1/Real.log (1+I.P.deltaH))*d := by positivity
  change _ ≤ I.coefficient*(1+Real.log I.k)*d
  calc
    _ ≤ 8*d+A*d*(Real.log I.k/Real.log (1+I.P.deltaH)+Real.log I.k) := by linarith only [hsum,hsmall,hmul]
    _ ≤ I.coefficient*(1+Real.log I.k)*d := by
      dsimp [coefficient,A] at *
      have he : (8+(16*I.C+33)*(1+1/Real.log (1+I.P.deltaH)))*(1+Real.log I.k)*d-
          (8*d+(16*I.C+33)*d*(Real.log I.k/Real.log (1+I.P.deltaH)+Real.log I.k))=
          8*d*Real.log I.k+(16*I.C+33)*(1+1/Real.log (1+I.P.deltaH))*d := by ring
      have hn : 0 ≤ 8*d*Real.log I.k := by positivity
      linarith only [he,hn,hz]

end Input
end UniformKServer.PartitionScales

end


end

end OAI
