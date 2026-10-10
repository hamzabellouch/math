import OAI.LinearAlgebra.Hadamard.Fourier

namespace OAI

/-! Rephasing, permutation equivalence and dephasing. -/

open scoped BigOperators Matrix

namespace HadamardSix

def rephase (H : Matrix6) (u v : Index → ℂ) : Matrix6 :=
  fun i j => u i * H i j * v j

lemma IsComplexHadamard.rephase {H : Matrix6} (hH : IsComplexHadamard H)
    (u v : Index → ℂ) (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ j, ‖v j‖ = 1) :
    IsComplexHadamard (HadamardSix.rephase H u v) := by
  refine isComplexHadamard_of_rows ?_ ?_
  · intro i j
    simp [HadamardSix.rephase, hu, hv, hH.1 i j]
  · intro i j
    have hf (k : Index) :
        HadamardSix.rephase H u v i k * star (HadamardSix.rephase H u v j k) =
          (u i * star (u j)) * (H i k * star (H j k)) := by
      calc
        _ = (u i * star (u j)) * (H i k * star (H j k)) * (v k * star (v k)) := by
          simp only [HadamardSix.rephase, star_mul]
          ring
        _ = _ := by rw [unit_mul_star (hv k), mul_one]
    simp only [hf, ← Finset.mul_sum, hH.row_orthogonality i j]
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, unit_mul_star (hu i), one_mul]
    · rw [ite_eq_right hij, mul_zero]

lemma IsComplexHadamard.permute_rows {H : Matrix6} (hH : IsComplexHadamard H)
    (p : Equiv.Perm Index) : IsComplexHadamard (fun i k => H (p i) k) := by
  apply isComplexHadamard_of_rows (fun i j => hH.1 (p i) j)
  intro i j
  simpa only [Equiv.apply_eq_iff_eq] using hH.row_orthogonality (p i) (p j)

lemma IsComplexHadamard.permute_columns {H : Matrix6} (hH : IsComplexHadamard H)
    (p : Equiv.Perm Index) : IsComplexHadamard (fun i k => H i (p k)) := by
  apply isComplexHadamard_of_rows (fun i j => hH.1 i (p j))
  intro i j
  rw [Equiv.sum_comp p (fun k => H i k * star (H j k))]
  exact hH.row_orthogonality i j

lemma HadamardEquivalent.refl (H : Matrix6) : HadamardEquivalent H H := by
  refine ⟨Equiv.refl _, Equiv.refl _, fun _ => 1, fun _ => 1, ?_, ?_, ?_⟩ <;> simp

lemma HadamardEquivalent.symm {H K : Matrix6} (h : HadamardEquivalent H K) :
    HadamardEquivalent K H := by
  obtain ⟨r, c, u, v, hu, hv, he⟩ := h
  refine ⟨r.symm, c.symm, fun i => (u (r.symm i))⁻¹,
    fun j => (v (c.symm j))⁻¹, ?_, ?_, ?_⟩
  · intro i
    simp [norm_inv, hu]
  · intro j
    simp [norm_inv, hv]
  · intro i j
    rw [he, r.apply_symm_apply, c.apply_symm_apply]
    have hune := unit_ne_zero (hu (r.symm i))
    have hvne := unit_ne_zero (hv (c.symm j))
    field_simp

lemma HadamardEquivalent.trans {H K L : Matrix6}
    (hHK : HadamardEquivalent H K) (hKL : HadamardEquivalent K L) :
    HadamardEquivalent H L := by
  obtain ⟨r, c, u, v, hu, hv, hHK⟩ := hHK
  obtain ⟨r', c', u', v', hu', hv', hKL⟩ := hKL
  refine ⟨r'.trans r, c'.trans c, fun i => u' i * u (r' i),
    fun j => v (c' j) * v' j, ?_, ?_, ?_⟩
  · intro i
    simp [hu', hu]
  · intro j
    simp [hv', hv]
  · intro i j
    rw [hKL, hHK]
    simp only [Equiv.trans_apply]
    ring

lemma HadamardEquivalent.hadamard {H K : Matrix6} (h : HadamardEquivalent H K)
    (hH : IsComplexHadamard H) : IsComplexHadamard K := by
  obtain ⟨r, c, u, v, hu, hv, he⟩ := h
  have hK : K = rephase (fun i j => H (r i) (c j)) u v := by
    ext i j
    exact he i j
  rw [hK]
  exact ((hH.permute_rows r).permute_columns c).rephase u v hu hv

noncomputable def dephase (H : Matrix6) : Matrix6 :=
  rephase H (fun i => star (H i 0)) (fun j => H 0 0 * star (H 0 j))

lemma dephase_equivalent {H : Matrix6} (hH : Unimodular H) :
    HadamardEquivalent H (dephase H) := by
  refine ⟨Equiv.refl _, Equiv.refl _, fun i => star (H i 0),
    fun j => H 0 0 * star (H 0 j), ?_, ?_, ?_⟩
  · intro i
    simpa using hH i 0
  · intro j
    simp [hH 0 0, hH 0 j]
  · intro i j
    rfl

lemma dephase_first_row {H : Matrix6} (hH : Unimodular H) (j : Index) :
    dephase H 0 j = 1 := by
  calc
    dephase H 0 j = (star (H 0 0) * H 0 0) * (H 0 j * star (H 0 j)) := by
      unfold dephase rephase
      ring
    _ = 1 := by rw [unit_star_mul (hH 0 0), unit_mul_star (hH 0 j), mul_one]

lemma dephase_first_column {H : Matrix6} (hH : Unimodular H) (i : Index) :
    dephase H i 0 = 1 := by
  dsimp [dephase, rephase]
  erw [unit_star_mul (hH i 0), unit_mul_star (hH 0 0), mul_one]

lemma IsComplexHadamard.dephase {H : Matrix6} (hH : IsComplexHadamard H) :
    IsComplexHadamard (dephase H) := (dephase_equivalent hH.1).hadamard hH

lemma entrywiseSquare_rephase (H : Matrix6) (u v : Index → ℂ) :
    entrywiseSquare (rephase H u v) =
      rephase (entrywiseSquare H) (fun i => u i ^ 2) (fun j => v j ^ 2) := by
  ext i j
  simp [entrywiseSquare, rephase, mul_pow]

lemma HadamardEquivalent.entrywiseSquare {H K : Matrix6} (h : HadamardEquivalent H K) :
    HadamardEquivalent (entrywiseSquare H) (entrywiseSquare K) := by
  obtain ⟨r, c, u, v, hu, hv, he⟩ := h
  refine ⟨r, c, fun i => u i ^ 2, fun j => v j ^ 2, ?_, ?_, ?_⟩
  · intro i
    simp [norm_pow, hu]
  · intro j
    simp [norm_pow, hv]
  · intro i j
    simp only [HadamardSix.entrywiseSquare, he, mul_pow]

lemma dephase_square_hadamard {H : Matrix6} (hu : Unimodular H)
    (hs : IsComplexHadamard (entrywiseSquare H)) :
    IsComplexHadamard (entrywiseSquare (dephase H)) :=
  (dephase_equivalent hu).entrywiseSquare.hadamard hs

lemma permuteCharge_trans (p q : Equiv.Perm Index) (a : Charge) :
    permuteCharge p (permuteCharge q a) = permuteCharge (p.trans q) a := rfl

lemma g_equivalence_covariance (H : Matrix6) {a : Charge} (ha : Balanced a)
    (r c : Equiv.Perm Index) (u v : Index → ℂ) (hv : ∀ j, v j ≠ 0) :
    g (fun i j => u i * H (r i) (c j) * v j) a =
      character u a * g H (permuteCharge r.symm a) := by
  calc
    _ = g (fun i j => u i * H (r i) (c j)) a :=
      g_column_phases (fun i j => u i * H (r i) (c j)) ha v hv
    _ = character u a * g (fun i j => H (r i) (c j)) a :=
      g_row_phases (fun i j => H (r i) (c j)) a u
    _ = character u a * g (fun i j => H (r i) j) a := by
      rw [g_permute_columns (fun i j => H (r i) j) a c]
    _ = _ := by rw [g_permuteCharge]; rfl

lemma HadamardEquivalent.fourier_vanishing_iff {H K : Matrix6}
    (hHK : HadamardEquivalent H K) :
    (∀ p : Equiv.Perm Index, g H (permuteCharge p alpha) = 0) ↔
      (∀ p : Equiv.Perm Index, g K (permuteCharge p alpha) = 0) := by
  have himpl {M N : Matrix6} (hMN : HadamardEquivalent M N)
      (hM : ∀ p : Equiv.Perm Index, g M (permuteCharge p alpha) = 0) :
      ∀ p : Equiv.Perm Index, g N (permuteCharge p alpha) = 0 := by
    obtain ⟨r, c, u, v, hu, hv, he⟩ := hMN
    have hN : N = fun i j => u i * M (r i) (c j) * v j := by
      ext i j
      exact he i j
    intro p
    rw [hN, g_equivalence_covariance M (alpha_balanced.permute p) r c u v
      (fun j => unit_ne_zero (hv j)), permuteCharge_trans, hM, mul_zero]
  exact ⟨himpl hHK, himpl hHK.symm⟩

end HadamardSix

end OAI
