import OAI.LinearAlgebra.Hadamard.Polynomials

namespace OAI

/-! Cubic values, their multiplicities, and cancellation on each fibre. -/

open scoped BigOperators Matrix

namespace HadamardSix

noncomputable def cubeFiber (v : Index → ℂ) (z : ℂ) : Finset Index := by
  classical
  exact Finset.univ.filter (fun i => v i ^ 3 = z)

@[simp] lemma mem_cubeFiber (v : Index → ℂ) (z : ℂ) (i : Index) :
    i ∈ cubeFiber v z ↔ v i ^ 3 = z := by
  classical
  simp [cubeFiber]

lemma sum_cubes_of_two_values (v : Index → ℂ) (a b : ℂ)
    (hab : ∀ i, v i ^ 3 = a ∨ v i ^ 3 = b) :
    (∑ i, v i ^ 3) = (cubeFiber v a).card * a +
      (6 - ((cubeFiber v a).card : ℂ)) * b := by
  classical
  have hfirst : (∑ i ∈ cubeFiber v a, v i ^ 3) = (cubeFiber v a).card * a := by
    calc
      _ = ∑ _i ∈ cubeFiber v a, a := Finset.sum_congr rfl (fun i hi => (mem_cubeFiber v a i).mp hi)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hlast : (∑ i ∈ (cubeFiber v a)ᶜ, v i ^ 3) = ((cubeFiber v a)ᶜ).card * b := by
    calc
      _ = ∑ _i ∈ (cubeFiber v a)ᶜ, b := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hab i).resolve_left (by simpa using hi)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hle : (cubeFiber v a).card ≤ 6 :=
    (Finset.card_le_card (Finset.subset_univ (cubeFiber v a)))
  rw [← Finset.sum_add_sum_compl (cubeFiber v a), hfirst, hlast,
    Finset.card_compl, Fintype.card_fin, Nat.cast_sub hle, Nat.cast_ofNat]

lemma cubeFiber_card_three (v : Index → ℂ) (a b : ℂ) (hne : a ≠ b)
    (hab : ∀ i, v i ^ 3 = a ∨ v i ^ 3 = b)
    (hsum : ∑ i, v i ^ 3 = 3 * (a + b)) : (cubeFiber v a).card = 3 := by
  have hprod : (((cubeFiber v a).card : ℂ) - 3) * (a - b) = 0 := by
    linear_combination hsum - sum_cubes_of_two_values v a b hab
  have hcast : ((cubeFiber v a).card : ℂ) = 3 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hne))
  exact_mod_cast hcast

lemma ratio_cube_multiplicities (v : Index → ℂ) (hv : ∀ i, ‖v i‖ = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    (∀ i, v i ^ 3 = v 0 ^ 3) ∨
      ∃ b : ℂ, b ≠ v 0 ^ 3 ∧ (∀ i, v i ^ 3 = v 0 ^ 3 ∨ v i ^ 3 = b) ∧
        (cubeFiber v (v 0 ^ 3)).card = 3 ∧ (cubeFiber v b).card = 3 := by
  let a := v 0 ^ 3
  let b := elementary v 3 - a
  have hab (i : Index) : v i ^ 3 = a ∨ v i ^ 3 = b :=
    ratio_cubes_two_values v hv h1 h2 i
  by_cases heq : a = b
  · left
    intro i
    exact (hab i).elim id (fun hi => hi.trans heq.symm)
  · right
    have hsum : ∑ i, v i ^ 3 = 3 * (a + b) := by
      rw [← three_mul_elementary_three v h1 h2]
      dsimp [b]
      ring
    refine ⟨b, Ne.symm heq, hab, cubeFiber_card_three v a b heq hab hsum, ?_⟩
    exact cubeFiber_card_three v b a (Ne.symm heq) (fun i => (hab i).symm)
      (by simpa only [add_comm] using hsum)

lemma ratio_cubeFiber_sum_zero (v : Index → ℂ) (hv : ∀ i, ‖v i‖ = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0)
    (a b : ℂ) (hne : a ≠ b) (hab : ∀ i, v i ^ 3 = a ∨ v i ^ 3 = b) :
    ∑ i ∈ cubeFiber v a, v i = 0 := by
  classical
  have hf : (∑ i ∈ cubeFiber v a, v i ^ 4) = a * ∑ i ∈ cubeFiber v a, v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← (mem_cubeFiber v a i).mp hi]
    ring
  have hl : (∑ i ∈ (cubeFiber v a)ᶜ, v i ^ 4) = b * ∑ i ∈ (cubeFiber v a)ᶜ, v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← (hab i).resolve_left (by simpa using hi)]
    ring
  have h4 := fourth_power_sum_zero v hv h1 h2
  rw [← Finset.sum_add_sum_compl (cubeFiber v a), hf, hl] at h4
  rw [← Finset.sum_add_sum_compl (cubeFiber v a)] at h1
  have he : (a - b) * ∑ i ∈ cubeFiber v a, v i = 0 := by
    linear_combination h4 - b * h1
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne)

noncomputable def rowRatio (H : Matrix6) (i j : Index) : Index → ℂ :=
  fun k => H i k * star (H j k)

lemma rowRatio_norm {H : Matrix6} (hu : Unimodular H) (i j k : Index) :
    ‖rowRatio H i j k‖ = 1 := by simp [rowRatio, hu i k, hu j k]

lemma rowRatio_first_sum {H : Matrix6} (hH : IsComplexHadamard H)
    {i j : Index} (hij : i ≠ j) : ∑ k, rowRatio H i j k = 0 := by
  simpa only [rowRatio, ite_eq_right hij] using hH.row_orthogonality i j

lemma rowRatio_second_sum {H : Matrix6} (hs : IsComplexHadamard (entrywiseSquare H))
    {i j : Index} (hij : i ≠ j) : ∑ k, rowRatio H i j k ^ 2 = 0 := by
  simpa only [rowRatio, entrywiseSquare, mul_pow, star_pow, ite_eq_right hij]
    using hs.row_orthogonality i j

lemma rowRatio_polynomial {H : Matrix6} (hH : IsComplexHadamard H)
    (hs : IsComplexHadamard (entrywiseSquare H)) {i j : Index} (hij : i ≠ j) :
    ratioPolynomial (rowRatio H i j) = Polynomial.X ^ 6 -
      Polynomial.C (elementary (rowRatio H i j) 3) * Polynomial.X ^ 3 +
      Polynomial.C (elementary (rowRatio H i j) 6) :=
  ratioPolynomial_of_power_sums (rowRatio H i j) (rowRatio_norm hH.1 i j)
    (rowRatio_first_sum hH hij) (rowRatio_second_sum hs hij)

lemma rowRatio_cube_multiplicities {H : Matrix6} (hH : IsComplexHadamard H)
    (hs : IsComplexHadamard (entrywiseSquare H)) {i j : Index} (hij : i ≠ j) :
    (∀ k, rowRatio H i j k ^ 3 = rowRatio H i j 0 ^ 3) ∨
      ∃ b : ℂ, b ≠ rowRatio H i j 0 ^ 3 ∧
        (∀ k, rowRatio H i j k ^ 3 = rowRatio H i j 0 ^ 3 ∨ rowRatio H i j k ^ 3 = b) ∧
        (cubeFiber (rowRatio H i j) (rowRatio H i j 0 ^ 3)).card = 3 ∧
        (cubeFiber (rowRatio H i j) b).card = 3 :=
  ratio_cube_multiplicities (rowRatio H i j) (rowRatio_norm hH.1 i j)
    (rowRatio_first_sum hH hij) (rowRatio_second_sum hs hij)

def IsDephased (H : Matrix6) : Prop := (∀ j, H 0 j = 1) ∧ (∀ i, H i 0 = 1)

lemma dephase_isDephased {H : Matrix6} (hH : Unimodular H) : IsDephased (dephase H) :=
  ⟨dephase_first_row hH, dephase_first_column hH⟩

lemma dephased_row_cube_multiplicities {H : Matrix6} (hH : IsComplexHadamard H)
    (hs : IsComplexHadamard (entrywiseSquare H)) (hd : IsDephased H) (i : Index) :
    (∀ k, H i k ^ 3 = 1) ∨
      ∃ x : ℂ, x ≠ 1 ∧ (∀ k, H i k ^ 3 = 1 ∨ H i k ^ 3 = x) ∧
        (cubeFiber (H i) 1).card = 3 ∧ (cubeFiber (H i) x).card = 3 := by
  by_cases hi : i = 0
  · subst i
    exact Or.inl (fun k => by rw [hd.1, one_pow])
  · have hr := rowRatio_cube_multiplicities hH hs hi
    have heq : rowRatio H i 0 = H i := by
      funext k
      simp only [rowRatio, hd.1, star_one, mul_one]
    rw [heq] at hr
    simpa only [hd.2, one_pow] using hr

lemma dephased_column_cube_multiplicities {H : Matrix6} (hH : IsComplexHadamard H)
    (hs : IsComplexHadamard (entrywiseSquare H)) (hd : IsDephased H) (j : Index) :
    (∀ i, H i j ^ 3 = 1) ∨
      ∃ x : ℂ, x ≠ 1 ∧ (∀ i, H i j ^ 3 = 1 ∨ H i j ^ 3 = x) ∧
        (cubeFiber (fun i => H i j) 1).card = 3 ∧
        (cubeFiber (fun i => H i j) x).card = 3 := by
  have hsT : IsComplexHadamard (entrywiseSquare H.transpose) := hs.transpose
  exact dephased_row_cube_multiplicities hH.transpose hsT ⟨hd.2, hd.1⟩ j

lemma dephased_row_cube_support {H : Matrix6} (hH : IsComplexHadamard H)
    (hs : IsComplexHadamard (entrywiseSquare H)) (hd : IsDephased H)
    (i : Index) (hn : ¬ ∀ k, H i k ^ 3 = 1) :
    ∃ (S : Finset Index) (x : ℂ), S.card = 3 ∧ 0 ∉ S ∧ x ≠ 1 ∧
      ∀ k, H i k ^ 3 = if k ∈ S then x else 1 := by
  classical
  obtain ⟨x, hx, hc, _, hsx⟩ := (dephased_row_cube_multiplicities hH hs hd i).resolve_left hn
  refine ⟨cubeFiber (H i) x, x, hsx, ?_, hx, ?_⟩
  · simpa only [mem_cubeFiber, hd.2, one_pow, ne_eq, eq_comm] using hx
  · intro k
    split_ifs with hk
    · exact (mem_cubeFiber (H i) x k).mp hk
    · exact (hc k).resolve_right ((mem_cubeFiber (H i) x k).not.mp hk)

lemma rowRatio_cubeFiber_sum_zero {H : Matrix6} (hH : IsComplexHadamard H)
    (hs : IsComplexHadamard (entrywiseSquare H)) {i j : Index} (hij : i ≠ j)
    (a b : ℂ) (hne : a ≠ b)
    (hab : ∀ k, rowRatio H i j k ^ 3 = a ∨ rowRatio H i j k ^ 3 = b) :
    ∑ k ∈ cubeFiber (rowRatio H i j) a, H i k * star (H j k) = 0 :=
  ratio_cubeFiber_sum_zero (rowRatio H i j) (rowRatio_norm hH.1 i j)
    (rowRatio_first_sum hH hij) (rowRatio_second_sum hs hij) a b hne hab

end HadamardSix

end OAI
