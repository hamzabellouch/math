import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Invariant233.TowerCyclicShift

variable {R : Type*} [Ring R] [StarRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def diagonalSum (e : ι → ι → R) : R := ∑ i, e i i

def permutationSum (e : ι → ι → R) (π : Equiv.Perm ι) : R :=
  ∑ i, e (π i) i

omit [DecidableEq ι] in
theorem star_permutationSum (e : ι → ι → R) (π : Equiv.Perm ι)
    (hstar : ∀ i j, star (e i j) = e j i) :
    star (permutationSum e π) = ∑ i, e i (π i) := by
  simp only [permutationSum, star_sum, hstar]

theorem star_permutationSum_mul (e : ι → ι → R) (π : Equiv.Perm ι)
    (hstar : ∀ i j, star (e i j) = e j i)
    (hmul : ∀ i j k l, e i j * e k l = if j = k then e i l else 0) :
    star (permutationSum e π) * permutationSum e π = diagonalSum e := by
  rw [star_permutationSum e π hstar]
  simp only [permutationSum, Finset.sum_mul_sum, hmul, π.injective.eq_iff]
  simp [diagonalSum]

theorem permutationSum_mul_star (e : ι → ι → R) (π : Equiv.Perm ι)
    (hstar : ∀ i j, star (e i j) = e j i)
    (hmul : ∀ i j k l, e i j * e k l = if j = k then e i l else 0) :
    permutationSum e π * star (permutationSum e π) = diagonalSum e := by
  rw [star_permutationSum e π hstar]
  simp only [permutationSum, Finset.sum_mul_sum, hmul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Equiv.sum_comp π (fun i ↦ e i i)

omit [StarRing R] in
theorem permutationSum_mul_diagonal (e : ι → ι → R) (π : Equiv.Perm ι)
    (hmul : ∀ i j k l, e i j * e k l = if j = k then e i l else 0)
    (i : ι) :
    permutationSum e π * e i i = e (π i) i := by
  simp [permutationSum, Finset.sum_mul, hmul]

omit [StarRing R] in
theorem diagonalSum_mul_diagonal (e : ι → ι → R)
    (hmul : ∀ i j k l, e i j * e k l = if j = k then e i l else 0)
    (i : ι) : diagonalSum e * e i i = e i i := by
  simp [diagonalSum, Finset.sum_mul, hmul]

section Blocks

variable {β : Type*} [Fintype β] [DecidableEq β]
variable {κ : β → Type*} [∀ b, Fintype (κ b)] [∀ b, DecidableEq (κ b)]

def blockPermutationSum (e : ∀ b, κ b → κ b → R)
    (π : ∀ b, Equiv.Perm (κ b)) : R := ∑ b, permutationSum (e b) (π b)

omit [Fintype β] [DecidableEq β] [∀ b, DecidableEq (κ b)] in
theorem star_permutationSum_mul_other
    (e : ∀ b, κ b → κ b → R) (π : ∀ b, Equiv.Perm (κ b))
    (hstar : ∀ b i j, star (e b i j) = e b j i)
    (hcross : ∀ b c, b ≠ c → ∀ i j k l, e b i j * e c k l = 0)
    {b c : β} (hbc : b ≠ c) :
    star (permutationSum (e b) (π b)) * permutationSum (e c) (π c) = 0 := by
  rw [star_permutationSum _ _ (hstar b)]
  simp only [permutationSum, Finset.sum_mul_sum, hcross b c hbc,
    Finset.sum_const_zero]

omit [Fintype β] [DecidableEq β] [∀ b, DecidableEq (κ b)] in
theorem permutationSum_mul_star_other
    (e : ∀ b, κ b → κ b → R) (π : ∀ b, Equiv.Perm (κ b))
    (hstar : ∀ b i j, star (e b i j) = e b j i)
    (hcross : ∀ b c, b ≠ c → ∀ i j k l, e b i j * e c k l = 0)
    {b c : β} (hbc : b ≠ c) :
    permutationSum (e b) (π b) * star (permutationSum (e c) (π c)) = 0 := by
  rw [star_permutationSum _ _ (hstar c)]
  simp only [permutationSum, Finset.sum_mul_sum, hcross b c hbc,
    Finset.sum_const_zero]

theorem star_blockPermutationSum_mul
    (e : ∀ b, κ b → κ b → R) (π : ∀ b, Equiv.Perm (κ b))
    (hstar : ∀ b i j, star (e b i j) = e b j i)
    (hmul : ∀ b i j k l, e b i j * e b k l = if j = k then e b i l else 0)
    (hcross : ∀ b c, b ≠ c → ∀ i j k l, e b i j * e c k l = 0) :
    star (blockPermutationSum e π) * blockPermutationSum e π =
      ∑ b, diagonalSum (e b) := by
  simp only [blockPermutationSum, star_sum, Finset.sum_mul_sum]
  calc
    _ = ∑ b, ∑ c, if b = c then diagonalSum (e b) else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hbc : b = c
      · subst c
        simp [star_permutationSum_mul _ _ (hstar b) (hmul b)]
      · simp only [ite_eq_right hbc, star_permutationSum_mul_other e π hstar hcross hbc]
    _ = _ := by simp

theorem blockPermutationSum_mul_star
    (e : ∀ b, κ b → κ b → R) (π : ∀ b, Equiv.Perm (κ b))
    (hstar : ∀ b i j, star (e b i j) = e b j i)
    (hmul : ∀ b i j k l, e b i j * e b k l = if j = k then e b i l else 0)
    (hcross : ∀ b c, b ≠ c → ∀ i j k l, e b i j * e c k l = 0) :
    blockPermutationSum e π * star (blockPermutationSum e π) =
      ∑ b, diagonalSum (e b) := by
  simp only [blockPermutationSum, star_sum, Finset.sum_mul_sum]
  calc
    _ = ∑ b, ∑ c, if b = c then diagonalSum (e b) else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hbc : b = c
      · subst c
        simp [permutationSum_mul_star _ _ (hstar b) (hmul b)]
      · simp only [ite_eq_right hbc, permutationSum_mul_star_other e π hstar hcross hbc]
    _ = _ := by simp

theorem blockPermutationSum_mem_unitary
    (e : ∀ b, κ b → κ b → R) (π : ∀ b, Equiv.Perm (κ b))
    (hstar : ∀ b i j, star (e b i j) = e b j i)
    (hmul : ∀ b i j k l, e b i j * e b k l = if j = k then e b i l else 0)
    (hcross : ∀ b c, b ≠ c → ∀ i j k l, e b i j * e c k l = 0)
    (hcomplete : ∑ b, diagonalSum (e b) = 1) :
    blockPermutationSum e π ∈ unitary R := by
  exact ⟨(star_blockPermutationSum_mul e π hstar hmul hcross).trans hcomplete,
    (blockPermutationSum_mul_star e π hstar hmul hcross).trans hcomplete⟩

omit [StarRing R] [DecidableEq β] in
theorem blockPermutationSum_mul_diagonal
    (e : ∀ b, κ b → κ b → R) (π : ∀ b, Equiv.Perm (κ b))
    (hmul : ∀ b i j k l, e b i j * e b k l = if j = k then e b i l else 0)
    (hcross : ∀ b c, b ≠ c → ∀ i j k l, e b i j * e c k l = 0)
    (b : β) (i : κ b) :
    blockPermutationSum e π * e b i i = e b (π b i) i := by
  classical
  rw [blockPermutationSum, Finset.sum_mul]
  rw [Finset.sum_eq_single b]
  · exact permutationSum_mul_diagonal _ _ (hmul b) i
  · intro c hc hcb
    simp only [permutationSum, Finset.sum_mul, hcross c b hcb,
      Finset.sum_const_zero]
  · simp

end Blocks

omit [StarRing R] [DecidableEq ι] in

theorem sub_eq_sub_mul_sum_of_agree (U A : R) (p : ι → R) (tops : Finset ι)
    (hcomplete : ∑ i, p i = 1)
    (hagree : ∀ i, i ∉ tops → U * p i = A * p i) :
    U - A = (U - A) * ∑ i ∈ tops, p i := by
  have hzero (i : ι) (hi : i ∉ tops) : (U - A) * p i = 0 := by
    rw [sub_mul, hagree i hi, sub_self]
  calc
    U - A = (U - A) * ∑ i, p i := by rw [hcomplete, mul_one]
    _ = ∑ i, (U - A) * p i := Finset.mul_sum _ _ _
    _ = ∑ i ∈ tops, (U - A) * p i := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi ↦ hzero i hi)
    _ = (U - A) * ∑ i ∈ tops, p i := (Finset.mul_sum _ _ _).symm

section Cyclic

variable {β : Type*} [Fintype β] [DecidableEq β]

def topSum (height : β → ℕ)
    (e : ∀ b, Fin (height b + 1) → Fin (height b + 1) → R) : R :=
  ∑ b, e b (Fin.last (height b)) (Fin.last (height b))

def cyclicSum (height : β → ℕ)
    (e : ∀ b, Fin (height b + 1) → Fin (height b + 1) → R) : R :=
  blockPermutationSum e (fun b ↦ finRotate (height b + 1))

theorem finRotate_castSucc {n : ℕ} (i : Fin n) :
    finRotate (n + 1) i.castSucc = i.succ := by
  exact finRotate_of_lt i.isLt

omit [StarRing R] [DecidableEq β] in

theorem cyclicSum_eq (height : β → ℕ)
    (e : ∀ b, Fin (height b + 1) → Fin (height b + 1) → R) :
    cyclicSum height e = ∑ b,
      ((∑ i : Fin (height b), e b i.succ i.castSucc) +
        e b 0 (Fin.last (height b))) := by
  simp only [cyclicSum, blockPermutationSum, permutationSum,
    Fin.sum_univ_castSucc, finRotate_castSucc, finRotate_last]

theorem topSum_isStarProjection (height : β → ℕ)
    (e : ∀ b, Fin (height b + 1) → Fin (height b + 1) → R)
    (hstar : ∀ b i j, star (e b i j) = e b j i)
    (hmul : ∀ b i j k l, e b i j * e b k l = if j = k then e b i l else 0)
    (hcross : ∀ b c, b ≠ c → ∀ i j k l, e b i j * e c k l = 0) :
    IsStarProjection (topSum height e) := by
  refine ⟨?_, ?_⟩
  · change topSum height e * topSum height e = topSum height e
    simp only [topSum, Finset.sum_mul_sum]
    calc
      _ = ∑ b, ∑ c, if b = c then
          e b (Fin.last (height b)) (Fin.last (height b)) else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hbc : b = c
        · subst c
          simp [hmul]
        · simp [hcross b c hbc, hbc]
      _ = _ := by simp
  · change star (topSum height e) = topSum height e
    simp only [topSum, star_sum, hstar]

omit [DecidableEq β] in
theorem cyclicSum_mem {𝕜 : Type*} [CommSemiring 𝕜] [StarRing 𝕜]
    [Algebra 𝕜 R] [StarModule 𝕜 R] (S : StarSubalgebra 𝕜 R)
    (height : β → ℕ)
    (e : ∀ b, Fin (height b + 1) → Fin (height b + 1) → R)
    (he : ∀ b i j, e b i j ∈ S) : cyclicSum height e ∈ S := by
  exact sum_mem fun b _ ↦ sum_mem fun i _ ↦ he b _ i

omit [DecidableEq β] in
theorem topSum_mem {𝕜 : Type*} [CommSemiring 𝕜] [StarRing 𝕜]
    [Algebra 𝕜 R] [StarModule 𝕜 R] (S : StarSubalgebra 𝕜 R)
    (height : β → ℕ)
    (e : ∀ b, Fin (height b + 1) → Fin (height b + 1) → R)
    (he : ∀ b i j, e b i j ∈ S) : topSum height e ∈ S := by
  exact sum_mem fun b _ ↦ he b _ _

theorem cyclicSum_mem_unitary (height : β → ℕ)
    (e : ∀ b, Fin (height b + 1) → Fin (height b + 1) → R)
    (hstar : ∀ b i j, star (e b i j) = e b j i)
    (hmul : ∀ b i j k l, e b i j * e b k l = if j = k then e b i l else 0)
    (hcross : ∀ b c, b ≠ c → ∀ i j k l, e b i j * e c k l = 0)
    (hcomplete : ∑ b, diagonalSum (e b) = 1) :
    cyclicSum height e ∈ unitary R :=
  blockPermutationSum_mem_unitary e _ hstar hmul hcross hcomplete

omit [StarRing R] [DecidableEq β] in

theorem sub_cyclicSum_eq_mul_topSum (height : β → ℕ)
    (e : ∀ b, Fin (height b + 1) → Fin (height b + 1) → R) (U : R)
    (hmul : ∀ b i j k l, e b i j * e b k l = if j = k then e b i l else 0)
    (hcross : ∀ b c, b ≠ c → ∀ i j k l, e b i j * e c k l = 0)
    (hcomplete : ∑ b, diagonalSum (e b) = 1)
    (hshift : ∀ b i, i ≠ Fin.last (height b) →
      U * e b i i = e b (finRotate (height b + 1) i) i) :
    U - cyclicSum height e = (U - cyclicSum height e) * topSum height e := by
  have hzero (b : β) (i : Fin (height b + 1)) (hi : i ≠ Fin.last (height b)) :
      (U - cyclicSum height e) * e b i i = 0 := by
    rw [sub_mul, hshift b i hi]
    rw [cyclicSum, blockPermutationSum_mul_diagonal e _ hmul hcross]
    exact sub_self _
  calc
    U - cyclicSum height e =
        (U - cyclicSum height e) * ∑ b, diagonalSum (e b) := by
      rw [hcomplete, mul_one]
    _ = ∑ b, ∑ i, (U - cyclicSum height e) * e b i i := by
      simp only [diagonalSum, Finset.mul_sum]
    _ = ∑ b, (U - cyclicSum height e) *
        e b (Fin.last (height b)) (Fin.last (height b)) := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_eq_single (Fin.last (height b))
      · intro i hi hne
        exact hzero b i hne
      · simp
    _ = (U - cyclicSum height e) * topSum height e := by
      rw [topSum, Finset.mul_sum]

theorem towerEntry_below_top_shift (U p : R) {n : ℕ} (i : Fin (n + 1))
    (hi : i ≠ Fin.last n) :
    U * (U ^ (i : ℕ) * p * star (U ^ (i : ℕ))) =
      U ^ (finRotate (n + 1) i : ℕ) * p * star (U ^ (i : ℕ)) := by
  rw [coe_finRotate_of_ne_last hi, pow_succ']
  simp only [mul_assoc]

omit [DecidableEq β] in
theorem sub_cyclicSum_eq_mul_topSum_of_towerEntries (height : β → ℕ)
    (e : ∀ b, Fin (height b + 1) → Fin (height b + 1) → R)
    (U : R) (p : β → R)
    (he : ∀ b i j, e b i j = U ^ (i : ℕ) * p b * star (U ^ (j : ℕ)))
    (hmul : ∀ b i j k l, e b i j * e b k l = if j = k then e b i l else 0)
    (hcross : ∀ b c, b ≠ c → ∀ i j k l, e b i j * e c k l = 0)
    (hcomplete : ∑ b, diagonalSum (e b) = 1) :
    U - cyclicSum height e = (U - cyclicSum height e) * topSum height e := by
  apply sub_cyclicSum_eq_mul_topSum height e U hmul hcross hcomplete
  intro b i hi
  simp only [he]
  exact towerEntry_below_top_shift U (p b) i hi

end Cyclic

section Norm

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [Nontrivial A]
variable {β : Type*} [Fintype β] [DecidableEq β]

theorem norm_sub_cyclicSum_le_two (height : β → ℕ)
    (e : ∀ b, Fin (height b + 1) → Fin (height b + 1) → A) (U : A)
    (hU : U ∈ unitary A)
    (hstar : ∀ b i j, star (e b i j) = e b j i)
    (hmul : ∀ b i j k l, e b i j * e b k l = if j = k then e b i l else 0)
    (hcross : ∀ b c, b ≠ c → ∀ i j k l, e b i j * e c k l = 0)
    (hcomplete : ∑ b, diagonalSum (e b) = 1) :
    ‖U - cyclicSum height e‖ ≤ 2 := by
  calc
    ‖U - cyclicSum height e‖ ≤ ‖U‖ + ‖cyclicSum height e‖ := norm_sub_le _ _
    _ = 2 := by
      rw [CStarRing.norm_of_mem_unitary hU,
        CStarRing.norm_of_mem_unitary
          (cyclicSum_mem_unitary height e hstar hmul hcross hcomplete)]
      norm_num

end Norm

end Invariant233.TowerCyclicShift

end

end OAI
