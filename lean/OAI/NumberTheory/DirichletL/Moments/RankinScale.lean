import OAI.NumberTheory.DirichletL.Moments.RankinLabels

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinScale
open IdealMobiusDivisorSum CenteredMomentRankinRadical CenteredMomentRankinLabels
local notation "O" => ActualEisensteinCubic.O

theorem source_partition_count (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : ℝ,0 < C ∧ ∀ (Z p s₀ : ℝ),1 ≤ Z → 0 ≤ p → p ≤ B →
      ∀ (s : Ideal O),Squarefree s → s ≠ 0 → Z^s₀ ≤ (Ideal.absNorm s:ℝ) →
      ∀ S : Finset ((Ideal O × Ideal O) × Finset (Ideal O)),
      (∀ v ∈ S,v.1.1 ≠ 0 ∧ v.1.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1.1=primeSupport v.1.2) →
      (∀ v ∈ S,s ∣ v.1.1 ∧ s ∣ v.1.2) →
      (∀ v ∈ S,v.2 ⊆ primeSupport (commonRadical v.1.1 v.1.2)) →
      (∀ v ∈ S,(Ideal.absNorm v.1.1:ℝ) ≤ Z^B ∧ (Ideal.absNorm v.1.2:ℝ) ≤ Z^B) →
      (∀ v ∈ S,(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ) ≤ Z^p) →
      (S.card:ℝ) ≤ C*Z^(p-s₀+δ) := by
  let a : ℝ := δ/(3*(B+1))
  have ha : 0 < a := div_pos hδ (by positivity)
  obtain ⟨C,hC,hcount⟩ := partitioned_common_pair_count a a ha ha
  refine ⟨C,hC,?_⟩
  intro Z p s₀ hZ hp hpB s hs hs0 hNs S hS heq hdiv hpart hN hR
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hb := hcount s hs hs0 S hS heq hdiv hpart (Z^B) (Z^B) (Z^p)
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _)
    (Real.rpow_pos_of_pos hZ0 _) hN hR
  have hpower : B*a+B*a+p*(1+a) ≤ p+δ := by
    have he : a*(3*(B+1))=δ := by dsimp only [a]; field_simp
    have hpa := mul_le_mul_of_nonneg_right hpB ha.le
    nlinarith
  calc
    _ ≤ C*(Z^B)^a*(Z^B)^a*(Z^p)^(1+a)/(Ideal.absNorm s:ℝ) := hb
    _ ≤ C*(Z^B)^a*(Z^B)^a*(Z^p)^(1+a)/(Z^s₀) :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hZ0 _) hNs
    _ = C*Z^(B*a+B*a+p*(1+a)-s₀) := by
      rw [← Real.rpow_mul hZ0.le,← Real.rpow_mul hZ0.le]
      rw [div_eq_mul_inv,← Real.rpow_neg hZ0.le]
      simp only [sub_eq_add_neg]
      rw [Real.rpow_add hZ0,Real.rpow_add hZ0,Real.rpow_add hZ0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hC.le

end SevenEighths.CenteredMomentRankinScale

end

end OAI
