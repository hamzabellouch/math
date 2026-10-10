import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCharacterRows
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedMellinRows
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorPartition
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedRoughRows
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorRows

namespace OAI

/-! The exact divisor partition for a rough stopped coefficient. Every
nonempty row below the roughness cutoff and every row above the original
support length vanishes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def angular_stoppedDivisorRowMass (ℓ : ℤ) (X w z l b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein)
    (H s : Finset Eisenstein) : ℝ :=
  ∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
    (fun n => (∏ p ∈ s,p) ∣ n),
    angularStoppedRowCoefficient ℓ X w z u W selected n*cubicSymbol n v‖^2


theorem angular_stopped_rough_divisor_partition (ℓ : ℤ) (X w z l b u R D : ℝ)
    (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
    (e : Eisenstein) (U H : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (hR : 2 < R) (hD : 1 ≤ D)
    (hrough : ∀ n ∈ stoppedIntervalSupport ι X l b e,
      angularStoppedRowCoefficient ℓ X w z u W selected n ≠ 0 →
      ∀ p, primaryPrime p → p ∣ n → R ≤ norm p) :
    angularStoppedDivisorMass ℓ X w z l b u W selected e H U =
      (∑ v ∈ H, ‖angularStoppedCharacterSum ℓ X w z l b u W selected v e‖^2)+
      (∑ s ∈ U.powerset.filter (fun s => R/2 < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ D),
        angular_stoppedDivisorRowMass ℓ X w z l b u W selected e H s)+
      (∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ b),
        angular_stoppedDivisorRowMass ℓ X w z l b u W selected e H s) := by
  let f := angular_stoppedDivisorRowMass ℓ X w z l b u W selected e H
  let E := ∑ v ∈ H, ‖angularStoppedCharacterSum ℓ X w z l b u W selected v e‖^2
  have hempty : f ∅ = E := by
    simp [f,E,angular_stoppedDivisorRowMass,angularStoppedCharacterSum]
  have hsmall (s : Finset Eisenstein) (hs : s ∈ U.powerset) (hne : s ≠ ∅)
      (hn : norm (∏ p ∈ s,p) ≤ R/2) : f s = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    have hh := rough_filtered_row_zero (stoppedIntervalSupport ι X l b e) s
      (fun p hp => hU p (Finset.mem_powerset.mp hs hp))
      (Finset.nonempty_iff_ne_empty.mpr hne)
      (angularStoppedRowCoefficient ℓ X w z u W selected) R hrough
      (show norm (∏ p ∈ s,p) < R by linarith) v
    simp only [hh,norm_zero,zero_pow (by decide : 2 ≠ 0)]
  have hlarge (s : Finset Eisenstein) (hn : b < norm (∏ p ∈ s,p)) : f s = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    have hh : (∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
        (fun n => (∏ p ∈ s,p) ∣ n),
        angularStoppedRowCoefficient ℓ X w z u W selected n*cubicSymbol n v) = 0 := by
      apply Finset.sum_eq_zero
      intro n hm
      have hp := stoppedIntervalSupport_spec X l b e (Finset.mem_filter.mp hm).1
      have hle := (norm_le_of_dvd (primary_ne_zero hp.1)
        (Finset.mem_filter.mp hm).2).trans hp.2.2
      exact False.elim ((not_lt_of_ge hle) hn)
    simp only [hh,norm_zero,zero_pow (by decide : 2 ≠ 0)]
  have hterm (s : Finset Eisenstein) (hs : s ∈ U.powerset) :
      f s = (if s = ∅ then E else 0)+
        (if R/2 < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ D then f s else 0)+
        (if D < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ b then f s else 0) := by
    by_cases hse : s = ∅
    · subst s
      have hhalf : ¬R/2 < (1:ℝ) := by linarith
      simp [hempty,norm_one_eq,hhalf,not_lt_of_ge hD]
    · by_cases hq : R/2 < norm (∏ p ∈ s,p)
      · by_cases hqd : norm (∏ p ∈ s,p) ≤ D
        · simp [hse,hq,hqd,not_lt_of_ge hqd]
        · by_cases hqb : norm (∏ p ∈ s,p) ≤ b
          · simp [hse,hq,hqd,hqb,lt_of_not_ge hqd]
          · simp [hse,hqd,hqb,hlarge s (lt_of_not_ge hqb)]
      · simp [hse,hq,hsmall s hs hse (le_of_not_gt hq)]
  change (∑ s ∈ U.powerset,f s) = _
  calc
    _ = ∑ s ∈ U.powerset, ((if s = ∅ then E else 0)+
        (if R/2 < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ D then f s else 0)+
        (if D < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ b then f s else 0)) :=
      Finset.sum_congr rfl hterm
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      simp [Finset.sum_filter,f,E]

end CubicFirstMoment

end

end OAI
