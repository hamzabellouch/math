import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedRoughness
import OAI.NumberTheory.CubicMoment.Estimates.GeometricPrimeBins
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPrimePredicate

namespace OAI

/-! Prime-factor roughness of the actual stopped coefficient. The selected
factor is rough because its bins precede the stopping bin; the distinguished
factor is rough because its coefficient vanishes at small primes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma geometricBinLower_antitone {ρ X : ℝ} (hρ : 1 ≤ ρ) :
    Antitone (geometricBinLower ρ X) := by
  intro i j hij
  exact pow_le_pow_right₀ hρ (Nat.sub_le_sub_left hij _)

theorem stoppingSideTest_prime_roughness {ρ X Z : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j k : ℕ} {r d p : Eisenstein} (hd : primary d) (hdX : norm d ≤ X)
    (hs : stoppingSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X) j k Z r d)
    (hp : primaryPrime p) (hpd : p ∣ d) :
    geometricBinLower ρ X j ≤ norm p := by
  have hmem := (primaryPrime_mem_factors_iff hd).mpr ⟨hp,hpd⟩
  have hbin := hs.1 p hmem
  have hpX := (norm_le_of_dvd (primary_ne_zero hd) hpd).trans hdX
  exact (geometricBinLower_antitone hρ.le hbin).trans
    (geometricPrimeBin_cell hρ hρ₂ hp hpX).1

theorem stoppedBeta_prime_roughness
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (W : ι → Eisenstein → ℂ) (R D : Finset Eisenstein)
    {ψ : ℝ → ℝ} (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z ρ X Z Q : ℝ} (hw : 0 < w) (hwz : w ≤ z)
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hD : ∀ d ∈ D, primary d ∧ norm d ≤ X)
    (j k h : ℕ) (early : Bool) {b p : Eisenstein}
    (hb : stoppedBeta R D (distinguishedTupleCoefficient S W ψ w z) ψ w
      (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
        j k h Z Q early) b ≠ 0)
    (hp : primaryPrime p) (hpb : p ∣ b) :
    min w (geometricBinLower ρ X j) ≤ norm p := by
  unfold stoppedBeta primaryPairCoefficient at hb
  obtain ⟨q,hq,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  obtain ⟨hq,hprod⟩ := Finset.mem_filter.mp hq
  obtain ⟨_hr,hd⟩ := Finset.mem_product.mp hq
  have hsel : stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h Z Q early q.1 q.2 := by
    by_contra hn
    exact hterm (ite_eq_right hn)
  rw [ite_eq_left hsel] at hterm
  have hv := (mul_ne_zero_iff.mp hterm).1
  have hdiv : p ∣ q.1*q.2 := by rwa [hprod]
  rcases hp.2.dvd_mul.mp hdiv with hpr | hpd
  · exact (min_le_left _ _).trans
      (distinguishedTupleCoefficient_prime_support S hS W hψone hψzero
        hw hwz hv hp hpr).1.le
  · exact (min_le_right _ _).trans
      (stoppingSideTest_prime_roughness hρ hρ₂ (hD q.2 hd).1 (hD q.2 hd).2
        hsel.1 hp hpd)

theorem stoppedBeta_early_prime_roughness
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (W : ι → Eisenstein → ℂ) (R D : Finset Eisenstein)
    {ψ : ℝ → ℝ} (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z ρ X Z Q : ℝ} (hw : 0 < w) (hwz : w ≤ z)
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hD : ∀ d ∈ D, primary d ∧ norm d ≤ X)
    (j k h : ℕ) (early : Bool) (hj : j ≤ h) {b p : Eisenstein}
    (hb : stoppedBeta R D (distinguishedTupleCoefficient S W ψ w z) ψ w
      (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
        j k h Z Q early) b ≠ 0)
    (hp : primaryPrime p) (hpb : p ∣ b) :
    min w (geometricBinLower ρ X h) ≤ norm p := by
  exact (min_le_min_left w (geometricBinLower_antitone hρ.le hj)).trans
    (stoppedBeta_prime_roughness S hS W R D hψone hψzero hw hwz hρ hρ₂ hD
      j k h early hb hp hpb)

end CubicFirstMoment

end

end OAI
