import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeHeightBlock
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeBlockEstimate
import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeFullSupport

namespace OAI

/-! Coarse bounds for the genuine semiprime polynomials. These bounds are
uniform in all heights and are used only beyond the power cutoff. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma semiprimeFullSupport_bounds {X : ℝ} (hX : 0 < X) (i : ℕ)
    {p : Eisenstein} (hp : p ∈ semiprimeFullSupport X i) :
    primary p ∧ semiprimePartitionScale i ≤ norm p ∧ norm p ≤ 2*semiprimePartitionScale i := by
  have hm := (semiprimeFullSupport_mem X i p).mp hp
  have hr := semiprimePartitionCoefficient_range hX hm.2
  exact ⟨hm.1.1,hr.2⟩

lemma semiprimeFullSupport_card {X : ℝ} (hX : 0 < X) (i : ℕ) :
    ((semiprimeFullSupport X i).card:ℝ) ≤ 36*semiprimePartitionScale i := by
  have hAi := semiprimePartitionScale_pos i
  have h := primary_support_card_le (semiprimeFullSupport X i)
    (by positivity : 0 ≤ 2*semiprimePartitionScale i)
    (fun p hp => ⟨(semiprimeFullSupport_bounds hX i hp).1,
      (semiprimeFullSupport_bounds hX i hp).2.2⟩)
  exact h.trans_eq (by ring)

lemma semiprime_pair_norm_bound {X M : ℝ} (hX : 0 < X) (hM : 0 ≤ M)
    (i j : ℕ) (F : Eisenstein → Eisenstein → ℂ)
    (hF : ∀ p ∈ semiprimeFullSupport X i, ∀ q ∈ semiprimeFullSupport X j, ‖F p q‖ ≤ M) :
    ‖∑ p ∈ semiprimeFullSupport X i, ∑ q ∈ semiprimeFullSupport X j,
      semiprimePartitionCoefficient X i p*semiprimePartitionCoefficient X j q*F p q‖ ≤
      1296*M*(semiprimePartitionScale i*semiprimePartitionScale j) := by
  have hAi := semiprimePartitionScale_pos i
  have hBj := semiprimePartitionScale_pos j
  have hsum : ‖∑ p ∈ semiprimeFullSupport X i, ∑ q ∈ semiprimeFullSupport X j,
      semiprimePartitionCoefficient X i p*semiprimePartitionCoefficient X j q*F p q‖ ≤
      ∑ _p ∈ semiprimeFullSupport X i, ∑ _q ∈ semiprimeFullSupport X j, M := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro p hp
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro q hq
    rw [norm_mul,norm_mul]
    calc
      _ ≤ 1*1*M := mul_le_mul
        (mul_le_mul (semiprimeSmoothWeight_norm _ _) (semiprimeSmoothWeight_norm _ _)
          (_root_.norm_nonneg _) (by norm_num)) (hF p hp q hq)
        (_root_.norm_nonneg _) (by norm_num)
      _ = _ := by ring
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  apply hsum.trans
  calc
    _ ≤ (36*semiprimePartitionScale i)*((36*semiprimePartitionScale j)*M) :=
      mul_le_mul (semiprimeFullSupport_card hX i)
        (mul_le_mul_of_nonneg_right (semiprimeFullSupport_card hX j) hM)
        (by positivity) (by positivity)
    _ = _ := by ring

lemma semiprimeGaussPolynomial_bound {X : ℝ} (hX : 0 < X) (i j : ℕ) (u : ℝ) :
    ‖semiprimeGaussPolynomial X i j u‖ ≤
      1296*(semiprimePartitionScale i*semiprimePartitionScale j) := by
  have hb := semiprime_pair_norm_bound hX (by norm_num : (0:ℝ) ≤ 1) i j
    (fun p q => gauss (p*q)*normTwist u (p*q)) (by
      intro p hp q hq
      rw [norm_mul,norm_normTwist,mul_one]
      exact norm_gauss_le_one (primary_mul
        (semiprimeFullSupport_bounds hX i hp).1 (semiprimeFullSupport_bounds hX j hq).1))
  simpa only [semiprimeGaussPolynomial,semiprimeFullSupport,
    semiprimePartitionCoefficient,mul_one,mul_assoc] using hb

def semiprimeModelPolynomial (X : ℝ) (i j : ℕ) (u : ℝ) : ℂ :=
  ∑ p ∈ semiprimeFullSupport X i, ∑ q ∈ semiprimeFullSupport X j,
    semiprimePartitionCoefficient X i p*semiprimePartitionCoefficient X j q*
      ((cStar:ℂ)*(idealMoebius (p*q):ℂ)^2*((norm (p*q)^(-1/6:ℝ):ℝ):ℂ)*normTwist u (p*q))

lemma semiprime_centered_polynomial (X : ℝ) (i j : ℕ) (u : ℝ) :
    semiprimeBlockPolynomial X i j u =
      semiprimeGaussPolynomial X i j u-semiprimeModelPolynomial X i j u := by
  unfold semiprimeBlockPolynomial semiprimeGaussPolynomial semiprimeModelPolynomial
  simp only [semiprimeFullSupport,semiprimePartitionCoefficient,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  unfold centeredGauss
  ring

lemma semiprimeModelPolynomial_bound {X : ℝ} (hX : 0 < X) (i j : ℕ) (u : ℝ) :
    ‖semiprimeModelPolynomial X i j u‖ ≤
      1296*cStar*(semiprimePartitionScale i*semiprimePartitionScale j)^(5/6:ℝ) := by
  let D := semiprimePartitionScale i*semiprimePartitionScale j
  have hD : 0 < D := mul_pos (semiprimePartitionScale_pos i) (semiprimePartitionScale_pos j)
  have hcs := cStar_pos
  have hAi := semiprimePartitionScale_pos i
  have hBj := semiprimePartitionScale_pos j
  have hb := semiprime_pair_norm_bound hX
    (by positivity : 0 ≤ cStar*D^(-1/6:ℝ)) i j
    (fun p q => (cStar:ℂ)*(idealMoebius (p*q):ℂ)^2*
      ((norm (p*q)^(-1/6:ℝ):ℝ):ℂ)*normTwist u (p*q)) (by
      intro p hp q hq
      have hn : D ≤ norm (p*q) := by
        rw [norm_mul_eq]
        exact mul_le_mul (semiprimeFullSupport_bounds hX i hp).2.1
          (semiprimeFullSupport_bounds hX j hq).2.1
          (by positivity) (norm_nonneg p)
      have hm : ‖(idealMoebius (p*q):ℂ)^2‖ ≤ 1 := by
        rw [norm_pow]
        simpa only [one_pow] using pow_le_pow_left₀ (_root_.norm_nonneg _)
          (norm_idealMoebius_le_one (p*q)) 2
      simp only [norm_mul,norm_normTwist,mul_one,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos cStar_pos,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (p*q)) (-1/6:ℝ))]
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm cStar_pos.le)
        (Real.rpow_nonneg (norm_nonneg (p*q)) (-1/6:ℝ))).trans
        (by
          have hr := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hD hn (by norm_num : (-1/6:ℝ) ≤ 0)) cStar_pos.le
          simpa only [mul_one] using hr))
  change ‖semiprimeModelPolynomial X i j u‖ ≤ 1296*(cStar*D^(-1/6:ℝ))*D at hb
  have he : D^(-1/6:ℝ)*D = D^(5/6:ℝ) := by
    calc
      _ = D^(-1/6:ℝ)*D^(1:ℝ) := by rw [Real.rpow_one]
      _ = D^((-1/6:ℝ)+1) := (Real.rpow_add hD _ _).symm
      _ = _ := by norm_num
  exact hb.trans_eq (by dsimp [D] at he ⊢; rw [show
    1296*(cStar*(semiprimePartitionScale i*semiprimePartitionScale j)^(-1/6:ℝ))*
        (semiprimePartitionScale i*semiprimePartitionScale j) =
      1296*cStar*((semiprimePartitionScale i*semiprimePartitionScale j)^(-1/6:ℝ)*
        (semiprimePartitionScale i*semiprimePartitionScale j)) by ring,he])

lemma continuous_semiprimeGaussPolynomial (X : ℝ) (i j : ℕ) :
    Continuous (semiprimeGaussPolynomial X i j) := by
  unfold semiprimeGaussPolynomial normTwist
  fun_prop

lemma semiprimeGaussPolynomial_bound_of_piece {X : ℝ} (hX : 0 < X)
    {H T : ℝ} {i j : ℕ} (hne : semiprimePartitionPiece 0 H T X i j ≠ 0) (u : ℝ) :
    ‖semiprimeGaussPolynomial X i j u‖ ≤ 3888*X := by
  have hAB := (semiprimePartitionPiece_nonzero_lengths 0 H T hX hne).2.1
  exact (semiprimeGaussPolynomial_bound hX i j u).trans (by nlinarith)

lemma semiprimeModelPolynomial_bound_of_piece {X : ℝ} (hX : 0 < X)
    {H T : ℝ} {i j : ℕ} (hne : semiprimePartitionPiece 0 H T X i j ≠ 0) (u : ℝ) :
    ‖semiprimeModelPolynomial X i j u‖ ≤
      (1296*cStar*3^(5/6:ℝ))*X^(5/6:ℝ) := by
  have hAB := (semiprimePartitionPiece_nonzero_lengths 0 H T hX hne).2.1
  have hcs := cStar_pos
  have hAi := semiprimePartitionScale_pos i
  have hBj := semiprimePartitionScale_pos j
  apply (semiprimeModelPolynomial_bound hX i j u).trans
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ semiprimePartitionScale i*semiprimePartitionScale j)
    hAB (by norm_num : (0:ℝ) ≤ 5/6)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hX.le] at hh
  nlinarith [mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 1296*cStar)]

end CubicFirstMoment

end

end OAI
