import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCommonCoefficient
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedRoughRows
import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeThirdMoment
import OAI.NumberTheory.CubicGram.SieveMajorant

namespace OAI

/-! Common-factor geometry and energy for the literal stopped row.
Zero coefficients are allowed on the ambient support: roughness is used
only after finding an active coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma rough_small_common_coefficient_zero (S : Finset Eisenstein)
    (F : Eisenstein → ℂ) (R : ℝ)
    (hrough : ∀ n ∈ S, F n ≠ 0 → ∀ p, primaryPrime p → p ∣ n → R ≤ norm p)
    {k : Eisenstein} (hk : primary k) (hks : Squarefree k) (hk1 : k ≠ 1)
    (hkR : norm k < R) {a : Eisenstein} (ha : a ∈ residualRows S k) : F (k*a) = 0 := by
  by_contra hF
  have hne : (primaryPrimeFactors k).Nonempty := by
    by_contra hn
    have he := primaryPrimeFactors_prod hk hks
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.prod_empty] at he
    exact hk1 he.symm
  obtain ⟨p,hp⟩ := hne
  have hprime := primaryPrimeFactor_spec hk hp
  have hlow := hrough (k*a) ((mem_residualRows (primary_ne_zero hk)).mp ha)
    hF p hprime.1 (hprime.2.trans (dvd_mul_right k a))
  exact (not_lt_of_ge (hlow.trans (norm_le_of_dvd (primary_ne_zero hk) hprime.2))) hkR

theorem bounded_common_energy_log (hpnt : PrimaryPrimePNT) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S : Finset Eisenstein)
      (v : Eisenstein → ℂ) (b M : ℝ), Real.exp 1 ≤ b → 0 ≤ M →
      (∀ a ∈ S, primary a ∧ Squarefree a ∧ norm a ≤ b) →
      (∀ a ∈ S, ‖v a‖ ≤ M) →
      (∑ k ∈ commonRowFactors S, (2:ℝ)^(primaryPrimeFactors k).card*
        commonBlockEnergy S v k) ≤ K*b*(1+Real.log b)^d*M^2 := by
  obtain ⟨K,d,hK,hmoment⟩ := squarefree_divisor_third_moment hpnt
  refine ⟨K,d,hK,?_⟩
  intro S v b M hb hM hS hv
  apply (common_energy_cubic_weight S (fun a ha => ⟨(hS a ha).1,(hS a ha).2.1⟩) v).trans
  calc
    _ = ∑ a ∈ S, (8:ℝ)^(primaryPrimeFactors a).card*‖v a‖^2 := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      rw [←pow_mul,Nat.mul_comm,pow_mul]
      norm_num
    _ ≤ ∑ a ∈ S, (8:ℝ)^(primaryPrimeFactors a).card*M^2 := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (_root_.norm_nonneg _) (hv a ha) 2) (by positivity)
    _ = (∑ a ∈ S, (8:ℝ)^(primaryPrimeFactors a).card)*M^2 :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hmoment b S hb hS) (sq_nonneg M)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_common_energy_log (hpnt : PrimaryPrimePNT)
    {ξ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (W : ι → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (selected : Eisenstein → Eisenstein → Prop) (u l b : ℝ)
        (e q : Eisenstein), Real.exp 1 ≤ b → b ≤ X →
      let S := stoppedIntervalSupport ι X l b e
      let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected
      (∑ k ∈ commonRowFactors S, (2:ℝ)^(primaryPrimeFactors k).card*
        commonBlockEnergy S (divisorGramCoefficient q β u) k) ≤ K*b*(1+Real.log b)^d := by
  obtain ⟨K,d,hK,henergy⟩ := bounded_common_energy_log hpnt
  obtain ⟨M,hM,hcoeff⟩ := stopped_interval_energy (ι := ι) hξ hξz
  refine ⟨K*M^2,d,by positivity,?_⟩
  filter_upwards [hcoeff] with X hcoeff
  intro W hW selected u l b e q hb hbX
  dsimp only
  have hbp : 0 < b := (Real.exp_pos 1).trans_le hb
  have hc := (hcoeff W hW selected 0 l b e hbp.le hbX).1
  have he := henergy (stoppedIntervalSupport ι X l b e)
    (divisorGramCoefficient q (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected) u)
    b M hb hM.le
    (fun a ha => stoppedIntervalSupport_spec X l b e ha)
    (fun a ha => (divisorGramCoefficient_norm_le q _ u
      (stoppedIntervalSupport_spec X l b e ha).1).trans (hc a ha))
  exact he.trans_eq (by ring)

theorem stopped_early_common_block_zero
    (X w z l b u ρ Z Q : ℝ) (W : ι → ℝ → ℂ)
    (hw : 0 < w) (hwz : w ≤ z) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (j₀ k₀ h : ℕ) (early : Bool) (hj : j₀ ≤ h) (e q k : Eisenstein)
    (hk : primary k) (hks : Squarefree k) (hk1 : k ≠ 1)
    (hkR : norm k < min w (geometricBinLower ρ X h))
    (Φ : ℝ → ℂ) (A : ℝ) :
    let S := stoppedIntervalSupport ι X l b e
    let β := stoppedRowCoefficient X w z 0 W
      (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X) j₀ k₀ h Z Q early)
    commonGramBlock S (divisorGramCoefficient q β u) Φ A k = 0 := by
  dsimp only
  let selected := stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
    j₀ k₀ h Z Q early
  let S := stoppedIntervalSupport ι X l b e
  let β := stoppedRowCoefficient X w z 0 W selected
  have hz (a : Eisenstein) (ha : a ∈ residualRows S k) : β (k*a) = 0 :=
    rough_small_common_coefficient_zero S β (min w (geometricBinLower ρ X h))
      (fun n _ hn p hp hpn => stoppedRowCoefficient_early_roughness X w z 0 ρ Z Q W
        hw hwz hρ hρ₂ j₀ k₀ h early hj hn hp hpn) hk hks hk1 hkR ha
  change commonGramBlock S (divisorGramCoefficient q β u) Φ A k = 0
  unfold commonGramBlock
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro c hc
  simp only [divisorGramCoefficient,dispersionAmplitude,divisorTwistedCoefficient,hz a ha,
    zero_mul,star_zero,ite_self]

end CubicFirstMoment

end

end OAI
