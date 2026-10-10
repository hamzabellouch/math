import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorPartition
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSmallDivisorMass
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedLargeDivisorPower

namespace OAI

/-! The complete divisor mass differs from its empty row by the two
controlled tails. The roughness premise concerns the actual coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_rough_divisor_mass (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ ∀ (X w z l b u M V B R : ℝ)
      (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
      (e : Eisenstein) (U H : Finset Eisenstein),
      1 ≤ b → 0 < V → 1 ≤ B → B ≤ b^(3/5:ℝ) → 2 < R →
      65536 ≤ b/b^(1/8:ℝ) → 8*B ≤ (b/b^(1/8:ℝ))^(3/4:ℝ) →
      (∀ p ∈ U, primaryPrime p) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖stoppedRowCoefficient X w z u W selected n‖ ≤ M) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        stoppedRowCoefficient X w z u W selected n ≠ 0 →
        ∀ p, primaryPrime p → p ∣ n → R ≤ norm p) →
      (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      stoppedDivisorMass X w z l b u W selected e H U ≤
      (∑ v ∈ H, ‖stoppedCharacterSum X w z l b u W selected v e‖^2)+
      (104976*V*B^(1/3:ℝ)*b^2*M^2*(R/2)^(-(1/2:ℝ))*
        (∑' n : Eisenstein, norm n^(-(3/2:ℝ)))+
      K₁*((largeCoreDyadicIndices V B).card:ℝ)*B^(1/3:ℝ)*M^2*(
        b^2*(V/5832)^(-(1/4:ℝ))*(∑' n : Eisenstein, norm n^(-2:ℝ))+
        b^(2-1/20000:ℝ)*(∑' n : Eisenstein, norm n^(-(2-1/20000:ℝ)))))+
      K₂*B^(1/3:ℝ)*b^(2-1/20:ℝ)*M^2 := by
  obtain ⟨K₁,hK₁,hsmall⟩ := stopped_small_divisor_mass (ι := ι) hHuxley
  obtain ⟨K₂,hK₂,hlarge⟩ := stopped_large_divisor_power_mass (ι := ι)
  refine ⟨K₁,K₂,hK₁,hK₂,?_⟩
  intro X w z l b u M V B R W selected e U H hb hV hB hBb hR hN hsize hU hcoeff hrough hH
  let A := U.powerset.filter
    (fun s => R/2 < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ b^(1/8:ℝ))
  have hA : A ⊆ U.powerset := Finset.filter_subset _ _
  have hrows (s : Finset Eisenstein) (hs : s ∈ A) :
      R/2 < norm (∏ p ∈ s,p) ∧ 65536 ≤ b/norm (∏ p ∈ s,p) ∧
        8*B ≤ (b/norm (∏ p ∈ s,p))^(3/4:ℝ) := by
    have hsp := primary_finset_prod s (fun p => p)
      (fun p hp => (hU p (Finset.mem_powerset.mp (hA hs) hp)).1)
    have hq := norm_pos_of_ne_zero (primary_ne_zero hsp)
    have hquot := div_le_div_of_nonneg_left (zero_le_one.trans hb) hq
      (Finset.mem_filter.mp hs).2.2
    exact ⟨(Finset.mem_filter.mp hs).2.1,hN.trans hquot,
      hsize.trans (Real.rpow_le_rpow (by positivity) hquot (by norm_num))⟩
  have hs := hsmall X w z l b u M V B (R/2) W selected e U A H
    (zero_lt_one.trans_le hb) hV (zero_le_one.trans hB) (by linarith) hU hA hrows hcoeff hH
  have hl := hlarge X w z l b u M B W selected e U H hb hB hBb hU hcoeff
    (fun v hv => ⟨(hH v hv).1,(hH v hv).2.1⟩)
  rw [stopped_rough_divisor_partition X w z l b u R (b^(1/8:ℝ)) W selected e U H
    hU hR (Real.one_le_rpow hb (by norm_num)) hrough]
  exact add_le_add (add_le_add (le_refl _) hs) hl

end CubicFirstMoment

end

end OAI
