import OAI.NumberTheory.CubicMoment.Estimates.CommonGramRemainder
import OAI.NumberTheory.CubicMoment.Estimates.CoprimeOuterComplete
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTotient

namespace OAI

/-! The zero mode in a common-factor block is a single original row.
Its signed Möbius sum is the exact finite coprimality density. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def commonGramZeroMode (S : Finset Eisenstein) (v : Eisenstein → ℂ)
    (W : ℝ → ℂ) (A : ℝ) (k : Eisenstein) : ℂ :=
  ∑ s ∈ (primaryPrimeFactors k).powerset,
    let m := ∏ p ∈ s,p
    (idealMoebius m:ℂ)*coprimePoissonDyad (residualRows S k) {0}
      (commonBlockCoefficient v k m) W (A/norm m)

lemma primary_moebius_density_bounds {k : Eisenstein} (hk : primary k)
    (hsk : Squarefree k) :
    0 ≤ metaplecticTotient k/norm k ∧ metaplecticTotient k/norm k ≤ 1 := by
  rw [metaplecticTotient_density hk hsk]
  have hp (p : Eisenstein) (h : p ∈ primaryPrimeFactors k) :
      0 ≤ 1-(norm p)⁻¹ ∧ 1-(norm p)⁻¹ ≤ 1 := by
    have hn := one_le_norm (primaryPrimeFactor_spec hk h).1.2.ne_zero
    constructor
    · exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hn)
    · have : 0 ≤ (norm p)⁻¹ := by positivity
      linarith
  exact ⟨Finset.prod_nonneg (fun p h => (hp p h).1),
    Finset.prod_le_one₀ (fun p h => (hp p h).1) (fun p h => (hp p h).2)⟩

lemma commonGramZeroMode_eq (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (v : Eisenstein → ℂ)
    (W : ℝ → ℂ) (A : ℝ) {k : Eisenstein} (hk : primary k) (hsk : Squarefree k) :
    commonGramZeroMode S v W A k = if k ∈ S then
      v k*star (v k)*(A/9:ℝ)*normProfileFourier W 0*
        (metaplecticTotient k/norm k:ℝ) else 0 := by
  have hr := residualRows_primary hk hS
  have hmem : (1:Eisenstein) ∈ residualRows S k ↔ k ∈ S := by
    rw [mem_residualRows (primary_ne_zero hk),mul_one]
  unfold commonGramZeroMode
  simp_rw [coprimePoissonDyad_unit_frequency _ hr,hmem]
  by_cases hks : k ∈ S
  · simp only [ite_eq_left hks]
    calc
      _ = (v k*star (v k)*(A/9:ℝ)*normProfileFourier W 0)*
          (((∑ s ∈ (primaryPrimeFactors k).powerset,
            (idealMoebius (∏ p ∈ s,p):ℝ)/norm (∏ p ∈ s,p)):ℝ):ℂ) := by
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        simp only [commonBlockCoefficient,mul_one,cubicSymbol_one_lower,mul_one]
        ring
      _ = _ := by rw [primary_moebius_density hk hsk]
  · simp only [ite_eq_right hks,mul_zero,Finset.sum_const_zero]

lemma commonGramZeroMode_norm_le (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (v : Eisenstein → ℂ)
    (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) {k : Eisenstein}
    (hk : primary k) (hsk : Squarefree k) :
    ‖commonGramZeroMode S v W A k‖ ≤
      if k ∈ S then (‖normProfileFourier W 0‖/9)*A*‖v k‖^2 else 0 := by
  rw [commonGramZeroMode_eq S hS v W A hk hsk]
  split_ifs
  · rw [norm_mul,norm_mul,norm_mul,norm_mul,norm_star,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ A/9),
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (primary_moebius_density_bounds hk hsk).1]
    calc
      _ ≤ ‖v k‖*‖v k‖*(A/9)*‖normProfileFourier W 0‖*1 :=
        mul_le_mul_of_nonneg_left (primary_moebius_density_bounds hk hsk).2
          (show 0 ≤ ‖v k‖*‖v k‖*(A/9)*‖normProfileFourier W 0‖ by positivity)
      _ = _ := by ring
  · simp only [norm_zero,le_refl]

lemma commonGramZeroMode_sum_bound (S K : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hK : ∀ k ∈ K, primary k ∧ Squarefree k) (v : Eisenstein → ℂ)
    (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) :
    ‖∑ k ∈ K, commonGramZeroMode S v W A k‖ ≤
      (‖normProfileFourier W 0‖/9)*A*∑ a ∈ S, ‖v a‖^2 := by
  let c := (‖normProfileFourier W 0‖/9)*A
  have hc : 0 ≤ c := by dsimp [c]; positivity
  calc
    _ ≤ ∑ k ∈ K, ‖commonGramZeroMode S v W A k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ K, if k ∈ S then c*‖v k‖^2 else 0 := by
      apply Finset.sum_le_sum
      intro k hk
      exact commonGramZeroMode_norm_le S hS v W hA (hK k hk).1 (hK k hk).2
    _ = ∑ k ∈ K.filter (fun k => k ∈ S), c*‖v k‖^2 :=
      (Finset.sum_filter (s := K) (fun k => k ∈ S) (fun k => c*‖v k‖^2)).symm
    _ ≤ ∑ k ∈ S, c*‖v k‖^2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (fun k hk => (Finset.mem_filter.mp hk).2)
      intro k hk hnot
      positivity
    _ = _ := by rw [← Finset.mul_sum]

end CubicFirstMoment

end

end OAI
