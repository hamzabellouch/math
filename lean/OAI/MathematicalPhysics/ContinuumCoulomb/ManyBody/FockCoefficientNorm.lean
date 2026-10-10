import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockNorm

namespace OAI

/-! Coefficient perturbations of the actual one- and two-body CAR
operators. The bounds depend polynomially on the number of modes and
not on the exponentially large dimension of the exterior algebra. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

variable {Q : ℕ}

def oneBodyOperator (K : Fin (Q + 1) → Fin (Q + 1) → ℂ) : Module.End ℂ (Space Q) :=
  ∑ i, ∑ j, K i j • transfer i j

def twoBodyOperator (W : Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    Module.End ℂ (Space Q) :=
  (2 : ℂ)⁻¹ • ∑ i, ∑ j, ∑ k, ∑ l,
    W i j k l • (create i * create j * annihilate l * annihilate k)

private lemma fockOperator_mul_norm_one (S T : Module.End ℂ (Space Q))
    (hS : ‖fockOperator S‖ ≤ 1) (hT : ‖fockOperator T‖ ≤ 1) :
    ‖fockOperator (S * T)‖ ≤ 1 := by
  rw [fockOperator_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hS hT (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

lemma fockOperator_quartic_norm (i j k l : Fin (Q + 1)) :
    ‖fockOperator (create i * create j * annihilate l * annihilate k)‖ ≤ 1 := by
  apply fockOperator_mul_norm_one _ _
  · apply fockOperator_mul_norm_one _ _
    · exact fockOperator_mul_norm_one _ _
        (fockOperator_create_norm i) (fockOperator_create_norm j)
    · exact fockOperator_annihilate_norm l
  · exact fockOperator_annihilate_norm k

lemma oneBodyOperator_norm (K : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    ‖fockOperator (oneBodyOperator K)‖ ≤ ∑ i, ∑ j, ‖K i j‖ := by
  simp only [oneBodyOperator, fockOperator_sum, fockOperator_smul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (fockOperator_transfer_norm i j) (norm_nonneg _)).trans_eq
    (mul_one _)

lemma twoBodyOperator_norm
    (W : Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    ‖fockOperator (twoBodyOperator W)‖ ≤ (1 / 2 : ℝ) * ∑ i, ∑ j, ∑ k, ∑ l, ‖W i j k l‖ := by
  simp only [twoBodyOperator, fockOperator_smul, fockOperator_sum]
  rw [norm_smul]
  have hhalf : ‖(2 : ℂ)⁻¹‖ = (1 / 2 : ℝ) := by
    norm_num [norm_inv, Complex.norm_def, Complex.normSq]
  rw [hhalf]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro l _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (fockOperator_quartic_norm i j k l) (norm_nonneg _)).trans_eq
    (mul_one _)

lemma oneBodyOperator_sub (K L : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    oneBodyOperator K - oneBodyOperator L = oneBodyOperator (fun i j => K i j - L i j) := by
  ext x
  simp [oneBodyOperator, Finset.sum_sub_distrib, sub_smul]

lemma twoBodyOperator_sub
    (W V : Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    twoBodyOperator W - twoBodyOperator V =
      twoBodyOperator (fun i j k l => W i j k l - V i j k l) := by
  ext x
  simp [twoBodyOperator, Finset.sum_sub_distrib, sub_smul, smul_sub]

lemma oneBodyOperator_error (K L : Fin (Q + 1) → Fin (Q + 1) → ℂ) {ε : ℝ}
    (h : ∀ i j, ‖K i j - L i j‖ ≤ ε) :
    ‖fockOperator (oneBodyOperator K - oneBodyOperator L)‖ ≤ (Q + 1 : ℝ) ^ 2 * ε := by
  rw [oneBodyOperator_sub]
  apply (oneBodyOperator_norm _).trans
  calc
    _ ≤ ∑ _i : Fin (Q + 1), ∑ _j : Fin (Q + 1), ε :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]
      ring

lemma twoBodyOperator_error
    (W V : Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → ℂ) {ε : ℝ}
    (h : ∀ i j k l, ‖W i j k l - V i j k l‖ ≤ ε) :
    ‖fockOperator (twoBodyOperator W - twoBodyOperator V)‖ ≤ (1 / 2 : ℝ) * (Q + 1 : ℝ) ^ 4 * ε := by
  rw [twoBodyOperator_sub]
  apply (twoBodyOperator_norm _).trans
  calc
    _ ≤ (1 / 2 : ℝ) * ∑ _i : Fin (Q + 1), ∑ _j : Fin (Q + 1),
        ∑ _k : Fin (Q + 1), ∑ _l : Fin (Q + 1), ε :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => h i j k l) (by norm_num)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
        Nat.cast_one]
      ring

lemma electronicOperator_error
    (K L : Fin (Q + 1) → Fin (Q + 1) → ℂ)
    (W V : Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → Fin (Q + 1) → ℂ)
    {ε η : ℝ} (hK : ∀ i j, ‖K i j - L i j‖ ≤ ε)
    (hW : ∀ i j k l, ‖W i j k l - V i j k l‖ ≤ η) :
    ‖fockOperator ((oneBodyOperator K + twoBodyOperator W) -
      (oneBodyOperator L + twoBodyOperator V))‖ ≤
        (Q + 1 : ℝ) ^ 2 * ε + (1 / 2 : ℝ) * (Q + 1 : ℝ) ^ 4 * η := by
  rw [show (oneBodyOperator K + twoBodyOperator W) -
      (oneBodyOperator L + twoBodyOperator V) =
      (oneBodyOperator K - oneBodyOperator L) + (twoBodyOperator W - twoBodyOperator V) by abel]
  rw [fockOperator_add]
  exact (norm_add_le _ _).trans (add_le_add (oneBodyOperator_error K L hK)
    (twoBodyOperator_error W V hW))

end ContinuumCoulomb.HubbardGlobal

end

end OAI
