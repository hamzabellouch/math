import OAI.NumberTheory.CubicMoment.Decomposition.StoppedRoughSupport
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedMellinRows

namespace OAI

/-! Early stopping makes every nonempty small-divisor row identically
zero. The cutoff is the actual minimum of the distinguished-prime cutoff
and the final permitted stopping-bin endpoint. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma rough_filtered_row_zero (S U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (hne : U.Nonempty)
    (F : Eisenstein → ℂ) (R : ℝ)
    (hrough : ∀ n ∈ S, F n ≠ 0 → ∀ p, primaryPrime p → p ∣ n → R ≤ norm p)
    (hsmall : norm (∏ p ∈ U,p) < R) (v : Eisenstein) :
    (∑ n ∈ S.filter (fun n => (∏ p ∈ U,p) ∣ n), F n*cubicSymbol n v) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  obtain ⟨hn,hd⟩ := Finset.mem_filter.mp hn
  have hF : F n = 0 := by
    by_contra hF
    obtain ⟨p,hp⟩ := hne
    have hpd : p ∣ ∏ p ∈ U,p := Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp
    have hprod : (∏ p ∈ U,p) ≠ 0 := Finset.prod_ne_zero_iff.mpr
      (fun q hq => (hU q hq).2.ne_zero)
    have hlow := hrough n hn hF p (hU p hp) (hpd.trans hd)
    exact (not_lt_of_ge (hlow.trans (norm_le_of_dvd hprod hpd))) hsmall
  rw [hF,zero_mul]

theorem rough_small_divisor_mass (S H U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (F : Eisenstein → ℂ) {R : ℝ} (hR : 1 < R)
    (hrough : ∀ n ∈ S, F n ≠ 0 → ∀ p, primaryPrime p → p ∣ n → R ≤ norm p) :
    (∑ d ∈ U.powerset.filter (fun d => norm (∏ p ∈ d,p) < R),
      ∑ v ∈ H, ‖∑ n ∈ S.filter (fun n => (∏ p ∈ d,p) ∣ n),
        F n*cubicSymbol n v‖^2) =
      ∑ v ∈ H, ‖∑ n ∈ S, F n*cubicSymbol n v‖^2 := by
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro d hd hde
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hd).1
    have hsmall := (Finset.mem_filter.mp hd).2
    apply Finset.sum_eq_zero
    intro v _
    rw [rough_filtered_row_zero S d (fun p hp => hU p (hsub hp))
      (Finset.nonempty_iff_ne_empty.mpr hde) F R hrough hsmall v]
    norm_num
  · intro hempty
    exact False.elim (hempty (by simpa using hR))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedRowCoefficient_early_roughness
    (X w z u ρ Z Q : ℝ) (W : ι → ℝ → ℂ)
    (hw : 0 < w) (hwz : w ≤ z) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (j k h : ℕ) (early : Bool) (hj : j ≤ h) {n p : Eisenstein}
    (hn : stoppedRowCoefficient X w z u W
      (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
        j k h Z Q early) n ≠ 0)
    (hp : primaryPrime p) (hpn : p ∣ n) :
    min w (geometricBinLower ρ X h) ≤ norm p := by
  have hb := (mul_ne_zero_iff.mp hn).1
  exact stoppedBeta_early_prime_roughness (fun _ : ι => primeCutoff X)
    (fun _ _ hp => (mem_primeCutoff.mp hp).1) (fun i p => W i (norm p))
    (orderedConvolutionSupport (fun _ : ι => primeCutoff X)) (primaryElementBall X)
    (fun _ _ hx => primeDetectorCutoff_one hx)
    (fun _ hx => primeDetectorCutoff_zero hx) hw hwz hρ hρ₂
    (fun _ hd => mem_primaryElementBall.mp hd) j k h early hj hb hp hpn

theorem stopped_early_small_divisor_mass
    (X w z l b u ρ Z Q : ℝ) (W : ι → ℝ → ℂ)
    (hw : 0 < w) (hwz : w ≤ z) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (j k h : ℕ) (early : Bool) (hj : j ≤ h) (e : Eisenstein)
    (H U : Finset Eisenstein) (hU : ∀ p ∈ U, primaryPrime p)
    (hR : 1 < min w (geometricBinLower ρ X h)) :
    let selected := stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h Z Q early
    (∑ d ∈ U.powerset.filter (fun d => norm (∏ p ∈ d,p) <
        min w (geometricBinLower ρ X h)),
      ∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
          (fun n => (∏ p ∈ d,p) ∣ n),
        stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖^2) =
      ∑ v ∈ H, ‖stoppedCharacterSum X w z l b u W selected v e‖^2 := by
  dsimp only
  simp_rw [stoppedCharacterSum_row]
  exact rough_small_divisor_mass _ H U hU _ hR
    (fun n _ hn p hp hpn => stoppedRowCoefficient_early_roughness
      X w z u ρ Z Q W hw hwz hρ hρ₂ j k h early hj hn hp hpn)

end CubicFirstMoment

end

end OAI
