import OAI.LinearAlgebra.Hadamard.Basic

namespace OAI

/-! Fourier identities and the entrywise square of a Hadamard matrix. -/

open scoped BigOperators Matrix

namespace HadamardSix

lemma alpha_balanced : Balanced alpha := by
  norm_num [Balanced, alpha, Fin.sum_univ_succ]

lemma Balanced.permute {a : Charge} (ha : Balanced a) (p : Equiv.Perm Index) :
    Balanced (permuteCharge p a) := by
  unfold Balanced permuteCharge
  rw [Equiv.sum_comp]
  exact ha

lemma character_zero (x : Index → ℂ) : character x 0 = 1 := by
  simp [character]

lemma character_add (x : Index → ℂ) (hx : ∀ i, x i ≠ 0) (a b : Charge) :
    character x (a + b) = character x a * character x b := by
  simp only [character, Pi.add_apply]
  simp_rw [zpow_add₀ (hx _)]
  exact Finset.prod_mul_distrib

lemma character_mul (x y : Index → ℂ) (a : Charge) :
    character (fun i => x i * y i) a = character x a * character y a := by
  simp only [character, mul_zpow, Finset.prod_mul_distrib]

lemma character_perm (x : Index → ℂ) (a : Charge) (p : Equiv.Perm Index) :
    character (fun i => x (p i)) (permuteCharge p a) = character x a := by
  exact Equiv.prod_comp p (fun i => x i ^ a i)

lemma character_norm (x : Index → ℂ) (hx : ∀ i, ‖x i‖ = 1) (a : Charge) :
    ‖character x a‖ = 1 := by
  simp [character, norm_prod, norm_zpow, hx]

lemma character_neg (x : Index → ℂ) (hx : ∀ i, ‖x i‖ = 1) (a : Charge) :
    character x (-a) = star (character x a) := by
  simp only [character, Pi.neg_apply, star_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [zpow_neg, ← inv_zpow, unit_inv (hx i)]
  exact (map_zpow₀ (starRingEnd ℂ) (x i) (a i)).symm

lemma character_constant {z : ℂ} (hz : z ≠ 0) {a : Charge} (ha : Balanced a) :
    character (fun _ => z) a = 1 := by
  have hp : ∀ s : Finset Index, ∏ i ∈ s, z ^ a i = z ^ ∑ i ∈ s, a i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hz]
  calc
    character (fun _ => z) a = z ^ ∑ i, a i := hp Finset.univ
    _ = 1 := by rw [ha, zpow_zero]

lemma g_zero (H : Matrix6) : g H 0 = 1 := by
  norm_num [g, character_zero]

lemma g_neg {H : Matrix6} (hH : Unimodular H) (a : Charge) :
    g H (-a) = star (g H a) := by
  simp only [g, character_neg _ (fun i => hH i _) a, star_mul, star_sum,
    star_inv₀, star_ofNat]
  ring

lemma g_norm_le_one {H : Matrix6} (hH : Unimodular H) (a : Charge) : ‖g H a‖ ≤ 1 := by
  calc
    ‖g H a‖ = (6 : ℝ)⁻¹ * ‖∑ k, character (fun i => H i k) a‖ := by
      simp [g]
    _ ≤ (6 : ℝ)⁻¹ * ∑ k, ‖character (fun i => H i k) a‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = 1 := by simp [character_norm _ (fun i => hH i _)]

lemma g_permuteCharge (H : Matrix6) (a : Charge) (p : Equiv.Perm Index) :
    g H (permuteCharge p a) = g (fun i k => H (p.symm i) k) a := by
  unfold g
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simpa using (character_perm (fun i => H (p.symm i) k) a p)

lemma g_permute_columns (H : Matrix6) (a : Charge) (p : Equiv.Perm Index) :
    g (fun i k => H i (p k)) a = g H a := by
  unfold g
  rw [Equiv.sum_comp p (fun k => character (fun i => H i k) a)]

lemma g_row_phases (H : Matrix6) (a : Charge) (u : Index → ℂ) :
    g (fun i k => u i * H i k) a = character u a * g H a := by
  simp only [g, character_mul, ← Finset.mul_sum]
  ring

lemma g_column_phases (H : Matrix6) {a : Charge} (ha : Balanced a)
    (v : Index → ℂ) (hv : ∀ k, v k ≠ 0) :
    g (fun i k => H i k * v k) a = g H a := by
  simp only [g, character_mul, character_constant (hv _) ha, mul_one]

def differenceCharge (n : ℤ) (i j : Index) : Charge :=
  Pi.single i n - Pi.single j n

lemma differenceCharge_balanced (n : ℤ) (i j : Index) :
    Balanced (differenceCharge n i j) := by
  simp [Balanced, differenceCharge, Finset.sum_sub_distrib]

lemma character_single (x : Index → ℂ) (n : ℤ) (i : Index) :
    character x (Pi.single i n) = x i ^ n := by
  classical
  unfold character
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

lemma character_difference (x : Index → ℂ) (hx : ∀ i, ‖x i‖ = 1)
    (n : ℤ) (i j : Index) :
    character x (differenceCharge n i j) = x i ^ n * star (x j ^ n) := by
  rw [differenceCharge, sub_eq_add_neg,
    character_add x (fun k => unit_ne_zero (hx k)), character_neg x hx,
    character_single, character_single]

lemma g_difference {H : Matrix6} (hH : IsComplexHadamard H) {i j : Index} (hij : i ≠ j) :
    g H (differenceCharge 1 i j) = 0 := by
  simp only [g, character_difference _ (fun k => hH.1 k _) 1 i j, zpow_one]
  rw [hH.row_orthogonality, ite_eq_right hij, mul_zero]

def entrywiseSquare (H : Matrix6) : Matrix6 := fun i j => H i j ^ 2

lemma Unimodular.entrywiseSquare {H : Matrix6} (hH : Unimodular H) :
    Unimodular (entrywiseSquare H) := by
  intro i j
  simp [HadamardSix.entrywiseSquare, norm_pow, hH i j]

lemma six_mul_g_double_difference {H : Matrix6} (hH : Unimodular H) (i j : Index) :
    (6 : ℂ) * g H (differenceCharge 2 i j) =
      ∑ k, (H i k ^ 2) * star (H j k ^ 2) := by
  simp [g, character_difference _ (fun l => hH l _) 2 i j, zpow_ofNat]

lemma square_hadamard_iff {H : Matrix6} (hH : Unimodular H) :
    IsComplexHadamard (entrywiseSquare H) ↔
      ∀ i j : Index, i ≠ j → g H (differenceCharge 2 i j) = 0 := by
  constructor
  · intro hs i j hij
    have hz := hs.row_orthogonality i j
    rw [ite_eq_right hij] at hz
    have hzero : (6 : ℂ) * g H (differenceCharge 2 i j) = 0 := by
      rw [six_mul_g_double_difference hH]
      exact hz
    exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
  · intro hg
    refine isComplexHadamard_of_rows hH.entrywiseSquare ?_
    intro i j
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      have hu (k : Index) : entrywiseSquare H i k * star (entrywiseSquare H i k) = 1 :=
        unit_mul_star (hH.entrywiseSquare i k)
      simp only [hu, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
    · rw [ite_eq_right hij]
      change ∑ k, (H i k ^ 2) * star (H j k ^ 2) = 0
      rw [← six_mul_g_double_difference hH, hg i j hij, mul_zero]

end HadamardSix

end OAI
