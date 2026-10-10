import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeLowWindow
import OAI.NumberTheory.CubicMoment.Estimates.PrimeModelLogTail

namespace OAI

/-! Summing every actual semiprime norm piece in the central Mellin
window. Only zero original pieces are omitted, and their complementary
Mellin remainder stays explicit in the exact decomposition. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def semiprimeCentralMellinSum (H T X S : ℝ) : ℂ :=
  (1/2:ℂ)*∑ i ∈ Finset.range (normPartitionCount (3*X)),
    ∑ j ∈ Finset.range (normPartitionCount (3*X)),
      if semiprimePartitionPiece 0 H T X i j = 0 then 0 else
        semiprimeLowMellinWindow H T X S i j

def semiprimeMellinRemainder (H T X S : ℝ) : ℂ :=
  (1/2:ℂ)*∑ i ∈ Finset.range (normPartitionCount (3*X)),
    ∑ j ∈ Finset.range (normPartitionCount (3*X)),
      if semiprimePartitionPiece 0 H T X i j = 0 then 0 else
        semiprimePartitionPiece 0 H T X i j-semiprimeLowMellinWindow H T X S i j

theorem centralSemiprimeProduct_mellin_decomposition {X : ℝ} (hX : 1 ≤ X)
    (H T S : ℝ) :
    centralSemiprimeProduct 0 H T X =
      semiprimeCentralMellinSum H T X S+semiprimeMellinRemainder H T X S := by
  rw [centralSemiprimeProduct_partition 0 H T hX]
  unfold semiprimeCentralMellinSum semiprimeMellinRemainder
  rw [← mul_add,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : semiprimePartitionPiece 0 H T X i j = 0 <;> simp [h]

lemma semiprimePartitionCount_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      (normPartitionCount (3*X):ℝ) ≤ C*(1+Real.log X) := by
  obtain ⟨C,hC,hbound⟩ := normPartitionCount_log_bound
  refine ⟨C*(1+Real.log 3),by positivity,?_⟩
  intro X hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  apply (hbound (3*X) (by linarith)).trans
  rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hXp.ne']
  have hlog := Real.log_nonneg hX
  have hthree := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)
  nlinarith [mul_nonneg hlog hthree]

theorem semiprime_central_mellin_isLittleO
    (hSW : KummerPrimeSiegelWalfisz) (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (Ct Cs : ℕ) (H : ℝ → ℝ) :
    (fun X => semiprimeCentralMellinSum (H X) ((1+Real.log X)^Ct) X ((1+Real.log X)^Cs))
      =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hbound⟩ := semiprime_low_mellin_window_log_saving
    hSW hpub hHuxley hperiod hMV hC hGI hGQ hVor hGamma 5 Ct Cs
  obtain ⟨D,hD,hcount⟩ := semiprimePartitionCount_log_bound
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound (D^2*K)
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with X hbound hX
  let N := normPartitionCount (3*X)
  let L := 1+Real.log X
  let F := fun i j => if semiprimePartitionPiece 0 (H X) (L^Ct) X i j = 0 then 0 else
    semiprimeLowMellinWindow (H X) (L^Ct) X (L^Cs) i j
  let B := K*X^(5/6:ℝ)/L^5
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_nonneg hX]
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hf (i j : ℕ) : ‖F i j‖ ≤ B := by
    dsimp only [F]
    split_ifs with hij
    · simpa only [norm_zero] using hB
    · exact hbound (H X) i j hij
  have hrow (i : ℕ) : ‖∑ j ∈ Finset.range N, F i j‖ ≤ (N:ℝ)*B := by
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun j _ => hf i j)).trans_eq
    simp
  have hall : ‖∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, F i j‖ ≤ (N:ℝ)^2*B := by
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun i _ => hrow i)).trans_eq
    simp [pow_two,mul_assoc]
  have hs : ‖semiprimeCentralMellinSum (H X) (L^Ct) X (L^Cs)‖ ≤ (N:ℝ)^2*B := by
    apply (le_trans ?_ hall)
    change ‖(1/2:ℂ)*(∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, F i j)‖ ≤ _
    rw [norm_mul]
    exact mul_le_of_le_one_left (_root_.norm_nonneg _) (by norm_num)
  have hn : (N:ℝ) ≤ D*L := hcount X hX
  have hn2 := pow_le_pow_left₀ (Nat.cast_nonneg N) hn 2
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
  apply hs.trans
  calc
    _ ≤ (D*L)^2*B := mul_le_mul_of_nonneg_right hn2 hB
    _ = (D^2*K)*(X^(5/6:ℝ)/(1+Real.log X)^3) := by
      dsimp [B,L]
      field_simp [hL.ne']

end CubicFirstMoment

end

end OAI
