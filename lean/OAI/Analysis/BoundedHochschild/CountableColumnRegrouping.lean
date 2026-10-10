import OAI.Analysis.BoundedHochschild.InfiniteMatrixColumns

namespace OAI

/-! Finite unital matrix columns by regrouping a countable column system. -/

noncomputable section

open Filter

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma projection_eq_one_of_column_bounds (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) atTop 1)
    {p : M} (hp : IsStarProjection p) (h : ∀ i, (c i).final ≤ p) : p = 1 := by
  have hh := orthogonal_projection_sum_annihilator e (fun i => (c i).final) (1 - p) 1 ht
    (fun i => by
      rw [mul_sub, mul_one, ((c i).final_proj.le_iff_mul_eq_left hp).mp (h i), sub_self])
  rw [one_mul, sub_eq_zero] at hh
  exact hh.symm

/-- Splitting countably many columns into `n` infinite classes gives `n`
unital orthogonal isometries. The proof uses actual sums of transitions. -/
theorem finite_columns_of_countable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) atTop 1)
    (n : ℕ) [NeZero n] :
    ∃ v : Fin n → PartialIso M, (∀ j, (v j).initial = 1) ∧
      (∀ j k, j ≠ k → (v j).final * (v k).final = 0) ∧ ∑ j, (v j).final = 1 := by
  classical
  let σ := (Nat.divModEquiv n).symm
  let a (j : Fin n) (i : ℕ) := columnTransition (c (σ (i, j))) (c i)
    ((hi _).trans (hi _).symm)
  have hai (j i) : (a j i).initial = (c i).final := columnTransition_initial ..
  have haf (j i) : (a j i).final = (c (σ (i, j))).final := columnTransition_final ..
  have haI (j : Fin n) (i k : ℕ) (hik : i ≠ k) :
      (a j i).initial * (a j k).initial = 0 := by
    rw [hai, hai]
    exact ho i k hik
  have haF (j : Fin n) (i k : ℕ) (hik : i ≠ k) :
      (a j i).final * (a j k).final = 0 := by
    rw [haf, haf]
    exact ho _ _ (fun h => hik (congrArg Prod.fst (σ.injective h)))
  choose v hvi hvf hvi_min hvf_min using fun j => exists_countable_partialIso_sum e
    (a j) (haI j) (haF j)
  have hinit (j : Fin n) : (v j).initial = 1 := by
    apply projection_eq_one_of_column_bounds e c ht (v j).initial_proj
    intro i
    rw [← hai j i]
    exact hvi j i
  have hcross (j k : Fin n) (hjk : j ≠ k) (i l : ℕ) :
      (a j i).final * (a k l).final = 0 := by
    rw [haf, haf]
    exact ho _ _ (fun h => hjk (congrArg Prod.snd (σ.injective h)))
  have horth (j k : Fin n) (hjk : j ≠ k) : (v j).final * (v k).final = 0 := by
    have hfirst (i : ℕ) : (a j i).final * (v k).final = 0 := by
      have hb : (v k).final ≤ 1 - (a j i).final := by
        apply hvf_min k _ (a j i).final_proj.one_sub
        intro l
        apply projection_le_complement_of_mul_zero (a k l).final_proj (a j i).final_proj
        simpa only [star_mul, (a j i).final_proj.isSelfAdjoint.star_eq,
          (a k l).final_proj.isSelfAdjoint.star_eq, star_zero] using
          congrArg star (hcross j k hjk i l)
      exact HochschildTypeII.projection_orthogonal_of_le_complement (a j i).final_proj
        (v k).final_proj hb
    have hb : (v j).final ≤ 1 - (v k).final := hvf_min j _ (v k).final_proj.one_sub
      (fun i => projection_le_complement_of_mul_zero (a j i).final_proj (v k).final_proj (hfirst i))
    have h := ((v j).final_proj.le_iff_mul_eq_left (v k).final_proj.one_sub).mp hb
    rw [mul_sub, mul_one] at h
    exact sub_eq_self.mp h
  have hp : IsStarProjection (∑ j, (v j).final) :=
    orthogonal_projection_finset_sum (fun j => (v j).final) (fun j => (v j).final_proj)
      horth Finset.univ
  have hsum : (∑ j, (v j).final) = 1 := by
    apply projection_eq_one_of_column_bounds e c ht hp
    intro i
    let t := Nat.divModEquiv n i
    have hti : σ t = i := (Nat.divModEquiv n).symm_apply_apply i
    have hh : (c i).final ≤ (v t.2).final := by
      have h := hvf t.2 t.1
      rw [haf] at h
      change (c (σ t)).final ≤ _ at h
      simpa only [hti] using h
    exact hh.trans (Finset.single_le_sum (fun j _ => (v j).final_proj.nonneg) (Finset.mem_univ t.2))
  exact ⟨v, hinit, horth, hsum⟩

/-- Arbitrary finite unital column systems inside a properly infinite algebra. -/
theorem exists_properlyInfinite_matrix_columns (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) (n : ℕ) [NeZero n] :
    ∃ v : Fin n → PartialIso M, (∀ j, (v j).initial = 1) ∧
      (∀ j k, j ≠ k → (v j).final * (v k).final = 0) ∧ ∑ j, (v j).final = 1 := by
  obtain ⟨c, hi, ho, ht⟩ := exists_countable_isometries e hno
  exact finite_columns_of_countable e c hi ho ht n

end BoundedHochschild.KadisonRingrose

end

end OAI
