import OAI.GroupTheory.PolycyclicRecognition.Analysis.HarmonicSeparatedRadii

namespace OAI

/-! # The volume and quadratic-form bounds at two actual word-ball scales -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type*} [Group G] [DecidableEq G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_harmonic_analytic_scales (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (V : Submodule ℝ (G → ℝ)) (basis : Module.Basis ι ℝ V) (d b : ℕ)
    (hk : 0 < Fintype.card ι)
    (hF : ∀ i, PolynomiallyBoundedOnWords S d (basis i).val)
    (D : ℝ) (hD : 0 ≤ D)
    (hvol : ∀ R, ((wordBall S R).card : ℝ) ≤ D * (1 + (R : ℝ)) ^ b)
    (w : ℕ) (hw : 0 < w) :
    let K := harmonicScaleConstant b d
    ∃ a i j : ℕ, a ≤ i ∧ w < j - i ∧
      (wordBallGram S (harmonicRadius a j) (fun i => (basis i).val)).PosDef ∧
      ((wordBall S (harmonicRadius a (i + 1))).card : ℝ) ≤
        K * (wordBall S (harmonicRadius a i)).card ∧
      ((wordBall S (harmonicRadius a (j + 1))).card : ℝ) ≤
        K ^ w * (wordBall S (harmonicRadius a i)).card ∧
      (wordBallGram S (harmonicRadius a (j + 1)) (fun i => (basis i).val)).det ≤
        K ^ Fintype.card ι * (wordBallGram S (harmonicRadius a j) (fun i => (basis i).val)).det := by
  let F := fun i => (basis i).val
  let K := harmonicScaleConstant b d
  let A := 2 * ((16 : ℝ) ^ ((2 * b + 2 * d) * Fintype.card ι)) ^ 3
  have hK : 0 < K := (harmonicScaleConstant_gt_one b d).trans' zero_lt_one
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAK : A ≤ K ^ Fintype.card ι := harmonic_good_scale_factor_bound b d _ hk
  have hAKw : A ^ w ≤ (K ^ w) ^ Fintype.card ι := by
    calc
      _ ≤ (K ^ Fintype.card ι) ^ w := pow_le_pow_left₀ hA hAK w
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  obtain ⟨a, ha, hscales⟩ := exists_wordBall_volume_determinant_good_scales
    S hS hgen V basis d b hF D hD hvol
  obtain ⟨i, j, hi, hij, _, hvi, hvj, hvij⟩ := hscales a w hw
  have hpos (n : ℕ) : (wordBallGram S (harmonicRadius a n) F).PosDef :=
    wordBallGram_posDef_mono S F (Nat.le_add_right a _) ha
  have hmon (m n : ℕ) (hmn : m ≤ n) : harmonicRadius a m ≤ harmonicRadius a n :=
    Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) hmn) a
  have hvi' : wordBallVolumeDeterminant S F (harmonicRadius a (i + 1)) ≤
      K ^ Fintype.card ι * wordBallVolumeDeterminant S F (harmonicRadius a i) :=
    hvi.trans (mul_le_mul_of_nonneg_right hAK (wordBallVolumeDeterminant_nonneg S F _))
  have hvj' : wordBallVolumeDeterminant S F (harmonicRadius a (j + 1)) ≤
      K ^ Fintype.card ι * wordBallVolumeDeterminant S F (harmonicRadius a j) :=
    hvj.trans (mul_le_mul_of_nonneg_right hAK (wordBallVolumeDeterminant_nonneg S F _))
  have hvij' : wordBallVolumeDeterminant S F (harmonicRadius a (j + 1)) ≤
      (K ^ w) ^ Fintype.card ι * wordBallVolumeDeterminant S F (harmonicRadius a i) :=
    hvij.trans (mul_le_mul_of_nonneg_right hAKw (wordBallVolumeDeterminant_nonneg S F _))
  refine ⟨a, i, j, hi, hij, hpos j, ?_, ?_, ?_⟩
  · exact wordBall_good_scale_volume_bound S F (hmon i (i + 1) (by omega))
      (hpos i) hk K hK.le hvi'
  · exact wordBall_good_scale_volume_bound S F (hmon i (j + 1) (by omega))
      (hpos i) hk (K ^ w) (pow_nonneg hK.le w) hvij'
  · exact wordBall_good_scale_determinant_bound S F (hmon j (j + 1) (by omega)) K hvj'

end PolycyclicRecognition

end

end OAI
