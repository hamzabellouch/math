import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeRoughDivisor
import OAI.NumberTheory.CubicMoment.Estimates.GramEmptyRows
import OAI.NumberTheory.CubicMoment.Estimates.CoprimeMellinMass

namespace OAI

/-! The exact common-divisor mass for full prime rows. Roughness leaves
only the empty divisor below a chosen threshold; every remaining term
has a genuinely large common divisor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def fullPrimeDivisorMellinMass (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) (H : Finset Eisenstein) (u N : ℝ) (f : Eisenstein) (t : ℝ) : ℝ :=
  ((∑ h ∈ H, ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter (fun a => f ∣ a),
      star (fullPrimeCoefficient R W X a*mellinPhase u (norm a))*
        star (gramMellinPhase t (norm a/N))*star (cubicSymbol a h)‖^2)+
   (∑ h ∈ H, ‖∑ a ∈ (fullSquarefreePrimeSupport R W X e).filter (fun a => f ∣ a),
      star (fullPrimeCoefficient R W X a*mellinPhase u (norm a))*
        gramMellinPhase t (norm a/N)*star (cubicSymbol a h)‖^2))/2

lemma fullPrimeDivisorMellinMass_one (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (e : Eisenstein) (H : Finset Eisenstein) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    fullPrimeDivisorMellinMass R W X e H u N 1 t =
      (fullStructuredHeightMass R H 1 e 0 u W X (2*Real.pi*t)+
        fullStructuredHeightMass R H 1 e 0 u W X (-(2*Real.pi*t)))/2 := by
  simpa only [fullPrimeDivisorMellinMass,Finset.prod_empty,one_dvd,Finset.filter_true] using
    fullPrime_empty_divisor_mass R W X H e u t hN

lemma fullPrimeDivisorMellinMass_small {R D : ℝ} (W : ι → ℝ → ℂ) (X : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hlo : ∀ i x, x < 1 → W i x = 0)
    (hhi : ∀ i x, R < x → W i x = 0) (hrough : ∀ i, D < X i)
    (s : Finset Eisenstein) (hs : ∀ p ∈ s, primaryPrime p) (hsne : s.Nonempty)
    (hsmall : norm (∏ p ∈ s, p) ≤ D) (e : Eisenstein) (H : Finset Eisenstein)
    (u N t : ℝ) :
    fullPrimeDivisorMellinMass R W X e H u N (∏ p ∈ s, p) t = 0 := by
  have hempty : (fullSquarefreePrimeSupport R W X e).filter
      (fun a => (∏ p ∈ s, p) ∣ a) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨ha,hsd⟩ := Finset.mem_filter.mp ha
    have hh := fullPrime_nonempty_divisor_large W X hX hlo hhi hrough s hs hsne
      (Finset.mem_filter.mp ha).1 hsd
    exact (not_lt_of_ge hsmall) hh
  simp only [fullPrimeDivisorMellinMass,hempty,Finset.sum_empty,norm_zero,zero_pow
    (by decide : (2:ℕ) ≠ 0),Finset.sum_const_zero,zero_add,zero_div]

lemma fullPrime_coprime_mass_split {R D : ℝ} (hD : 1 ≤ D)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (hX : ∀ i, 0 < X i)
    (hlo : ∀ i x, x < 1 → W i x = 0) (hhi : ∀ i x, R < x → W i x = 0)
    (hrough : ∀ i, D < X i) (e : Eisenstein) (H U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (u t : ℝ) {N : ℝ} (hN : 0 < N) :
    coprimeMellinMass (fullSquarefreePrimeSupport R W X e) H U
      (fun a => star (fullPrimeCoefficient R W X a*mellinPhase u (norm a)))
      (fun a => star (fullPrimeCoefficient R W X a*mellinPhase u (norm a)))
      (fun a => norm a/N) t =
    (fullStructuredHeightMass R H 1 e 0 u W X (2*Real.pi*t)+
      fullStructuredHeightMass R H 1 e 0 u W X (-(2*Real.pi*t)))/2+
    ∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s, p)),
      fullPrimeDivisorMellinMass R W X e H u N (∏ p ∈ s, p) t := by
  let F := fun s : Finset Eisenstein =>
    fullPrimeDivisorMellinMass R W X e H u N (∏ p ∈ s, p) t
  have hsmall : (∑ s ∈ U.powerset.filter (fun s => norm (∏ p ∈ s, p) ≤ D), F s) = F ∅ := by
    apply Finset.sum_eq_single ∅
    · intro s hs hsne
      obtain ⟨hsU,hsmall⟩ := Finset.mem_filter.mp hs
      exact fullPrimeDivisorMellinMass_small W X hX hlo hhi hrough s
        (fun p hp => hU p (Finset.mem_powerset.mp hsU hp))
        (Finset.nonempty_iff_ne_empty.mpr hsne) hsmall e H u N t
    · intro hn
      exact (hn (by simpa only [Finset.mem_filter,Finset.mem_powerset,Finset.empty_subset,
        true_and,Finset.prod_empty] using (show norm (1:Eisenstein) ≤ D by simpa [norm] using hD))).elim
  have hsplit := Finset.sum_filter_add_sum_filter_not U.powerset
    (fun s => norm (∏ p ∈ s, p) ≤ D) F
  rw [hsmall] at hsplit
  change (∑ s ∈ U.powerset, F s) = _
  rw [← hsplit]
  simp only [not_le] 
  congr 1
  exact fullPrimeDivisorMellinMass_one R W X e H u t hN

end CubicFirstMoment

end

end OAI
