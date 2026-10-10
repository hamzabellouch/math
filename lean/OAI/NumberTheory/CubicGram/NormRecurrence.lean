import Mathlib
import OAI.NumberTheory.CubicGram.MellinNorm

namespace OAI

/-! Divisor-completed energies and the coprime Poisson norm recurrence. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisorCompleted_energy_le (S U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (hU : ∀ p ∈ U, primaryPrime p)
    (v : Eisenstein → ℂ) :
    (∑ s ∈ U.powerset, ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖^2) ≤
      ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖v a‖^2 := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  rw [← Finset.sum_filter]
  have hs : U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ a) ⊆
      (primaryPrimeFactors a).powerset := by
    intro s hs
    obtain ⟨hs,hd⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_powerset.mpr (primeSet_subset_factors_of_prod_dvd (hS a ha)
      (fun p hp => hU p (Finset.mem_powerset.mp hs hp)) hd)
  calc
    _ ≤ ∑ _s ∈ (primaryPrimeFactors a).powerset, ‖v a‖^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => sq_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]

lemma coprimeNormMajorant_le_divisorEnergy (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (hU : ∀ p ∈ U, primaryPrime p)
    (v w : Eisenstein → ℂ) :
    coprimeNormMajorant S H U v w ≤ finiteCubicBound S H *
      ((∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖v a‖^2) +
       (∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖w a‖^2)) / 2 := by
  calc
    _ ≤ ∑ s ∈ U.powerset, finiteCubicBound S H *
        ((∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖^2) +
         (∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖w a‖^2)) / 2 := by
      apply Finset.sum_le_sum
      intro s hs
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (finiteCubicBound_mono (Finset.filter_subset _ _) (Finset.Subset.refl _))
        (add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))) (by norm_num)
    _ = finiteCubicBound S H *
        ((∑ s ∈ U.powerset, ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖^2) +
         (∑ s ∈ U.powerset, ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖w a‖^2)) / 2 := by
      rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (add_le_add (divisorCompleted_energy_le S U hS hU v)
        (divisorCompleted_energy_le S U hS hU w)) (finiteCubicBound_nonneg _ _)) (by norm_num)

def sievePrimeSet (S : Finset Eisenstein) : Finset Eisenstein :=
  S.biUnion primaryPrimeFactors

lemma sievePrimeSet_primary (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a) :
    ∀ p ∈ sievePrimeSet S, primaryPrime p := by
  intro p hp
  obtain ⟨a,ha,hp⟩ := Finset.mem_biUnion.mp hp
  exact (primaryPrimeFactor_spec (hS a ha) hp).1

lemma factors_subset_sievePrimeSet {S : Finset Eisenstein} {a : Eisenstein} (ha : a ∈ S) :
    primaryPrimeFactors a ⊆ sievePrimeSet S := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨a,ha,hp⟩

end CubicFirstMoment

namespace CubicFirstMoment

def gaussRowCoefficient (u : Eisenstein → ℂ) (a : Eisenstein) : ℂ :=
  u a * gauss a / (Real.sqrt (norm a) : ℂ)

lemma gaussRowCoefficient_norm_sq {a : Eisenstein} (ha : primary a)
    (hsa : Squarefree a) (u : Eisenstein → ℂ) :
    ‖gaussRowCoefficient u a‖^2 = ‖u a‖^2 / norm a := by
  simp only [gaussRowCoefficient, norm_div, norm_mul, norm_gauss_of_squarefree ha hsa,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    div_pow, Real.sq_sqrt (norm_nonneg _)]

def coprimePoissonDyad (S H : Finset Eisenstein) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) (Z : ℝ) : ℂ :=
  ∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
    u a * star (u b) * ((Z / (9*Real.sqrt (norm (a*b))) : ℝ) : ℂ) *
      (gauss a * star (gauss b)) * ∑ h ∈ H, gramDualTerm a b W Z h else 0

lemma gramDyadTerm_separated (a b h : Eisenstein) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) {Z J N : ℝ} (hZ : 0 ≤ Z) (hJ : J ≠ 0) (hN : N ≠ 0) :
    u a * star (u b) * ((Z / (9*Real.sqrt (norm (a*b))) : ℝ) : ℂ) *
      (gauss a * star (gauss b)) * gramDualTerm a b W Z h =
    ((Z/9 : ℝ) : ℂ) *
      (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ) *
      ((gaussRowCoefficient u a * star (cubicSymbol a h)) *
        star (gaussRowCoefficient u b * star (cubicSymbol b h))) *
      radialDualProfile W ((Z*J/(27*N^2))*(norm h/J)/((norm a/N)*(norm b/N))) := by
  have hn : norm (a*b) = norm a * norm b := Complex.normSq_mul _ _
  have hs := Real.sqrt_mul (norm_nonneg a) (norm b)
  have he : (Z*J/(27*N^2))*(norm h/J)/((norm a/N)*(norm b/N)) =
      Z*norm h/(27*(norm a * norm b)) := by
    field_simp
  rw [gramDualTerm_radial a b W hZ, hn, hs, he]
  have hr (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp
  simp only [gaussRowCoefficient, star_mul, star_star, star_inv₀, hr,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_inv, div_eq_mul_inv,
    mul_inv_rev]
  ring

lemma coprimePoissonDyad_separated (S H : Finset Eisenstein) (u : Eisenstein → ℂ)
    (W : ℝ → ℂ) {Z J N : ℝ} (hZ : 0 ≤ Z) (hJ : J ≠ 0) (hN : N ≠ 0) :
    coprimePoissonDyad S H u W Z = ((Z/9 : ℝ) : ℂ) *
      coprimeRadialForm S H (gaussRowCoefficient u) (gaussRowCoefficient u)
        (fun h => (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ))
        (fun h => norm h/J) (fun a => norm a/N) W (Z*J/(27*N^2)) := by
  unfold coprimePoissonDyad coprimeRadialForm
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (s := H) (t := S)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm (s := H) (t := S)]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    apply Finset.sum_congr rfl
    intro h hh
    rw [gramDyadTerm_separated a b h u W hZ hJ hN]
    ring
  · simp [hab]

end CubicFirstMoment

namespace CubicFirstMoment

lemma gaussRowCoefficient_divisor_energy (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (u : Eisenstein → ℂ)
    {N : ℝ} (hN : 0 < N) (hSN : ∀ a ∈ S, N ≤ norm a) :
    (∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖gaussRowCoefficient u a‖^2) ≤
      (∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2) / N := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro a ha
  rw [gaussRowCoefficient_norm_sq (hS a ha).1 (hS a ha).2, ← mul_div_assoc]
  exact div_le_div_of_nonneg_left (by positivity) hN (hSN a ha)

theorem coprimePoissonDyad_norm_recurrence (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ Squarefree a) →
      ∀ (u : Eisenstein → ℂ) (Z J N : ℝ), 0 ≤ Z → 0 < J → 0 < N →
      (∀ a ∈ S, N ≤ norm a ∧ norm a ≤ Real.sqrt 2*N) →
      (∀ h ∈ H, J ≤ norm h ∧ norm h ≤ 2*J) →
      (1+Z*J/(27*N^2))^A * ‖coprimePoissonDyad S H u W Z‖ ≤
        C*(Z/N)*finiteCubicBound S H *
          ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2 := by
  obtain ⟨C,hC,hbound⟩ := coprimeRadialForm_rapidDecay W hW hW' A
  refine ⟨C/9, by positivity, ?_⟩
  intro S H hS u Z J N hZ hJ hN hSN hHJ
  let U := sievePrimeSet S
  have hU : ∀ p ∈ U, primaryPrime p := sievePrimeSet_primary S (fun a ha => (hS a ha).1)
  have hu : ∀ a ∈ S, primaryPrimeFactors a ⊆ U := fun a ha => factors_subset_sievePrimeSet ha
  have hx : ∀ h ∈ H, norm h/J ∈ Icc (1 : ℝ) 2 := by
    intro h hh
    exact ⟨(le_div_iff₀ hJ).mpr (by simpa using (hHJ h hh).1),
      (div_le_iff₀ hJ).mpr (hHJ h hh).2⟩
  have hy : ∀ a ∈ S, norm a/N ∈ Icc (1 : ℝ) (Real.sqrt 2) := by
    intro a ha
    exact ⟨(le_div_iff₀ hN).mpr (by simpa using (hSN a ha).1),
      (div_le_iff₀ hN).mpr (hSN a ha).2⟩
  have hi := hbound S H U hS hU hu (gaussRowCoefficient u) (gaussRowCoefficient u)
    (fun h => (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ))
    (fun h hh => by simp only [Circle.norm_coe, le_refl])
    (fun h => norm h/J) (fun a => norm a/N) hx hy (Z*J/(27*N^2)) (by positivity)
  have hmajor : coprimeNormMajorant S H U (gaussRowCoefficient u) (gaussRowCoefficient u) ≤
      finiteCubicBound S H *
        ((∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2)/N) := by
    calc
      _ ≤ finiteCubicBound S H *
          ∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖gaussRowCoefficient u a‖^2 := by
        convert coprimeNormMajorant_le_divisorEnergy S H U (fun a ha => (hS a ha).1)
          hU (gaussRowCoefficient u) (gaussRowCoefficient u) using 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (gaussRowCoefficient_divisor_energy S hS u hN (fun a ha => (hSN a ha).1))
        (finiteCubicBound_nonneg _ _)
  rw [coprimePoissonDyad_separated S H u W hZ (ne_of_gt hJ) (ne_of_gt hN),
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ = (Z/9) * ((1+Z*J/(27*N^2))^A * ‖coprimeRadialForm S H
        (gaussRowCoefficient u) (gaussRowCoefficient u)
        (fun h => (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ))
        (fun h => norm h/J) (fun a => norm a/N) W (Z*J/(27*N^2))‖) := by ring
    _ ≤ (Z/9) * (C*(finiteCubicBound S H *
        ((∑ a ∈ S, (2 : ℝ)^(primaryPrimeFactors a).card * ‖u a‖^2)/N))) :=
      mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_left hmajor hC.le)) (by positivity)
    _ = _ := by ring

end CubicFirstMoment
end
end

end OAI
