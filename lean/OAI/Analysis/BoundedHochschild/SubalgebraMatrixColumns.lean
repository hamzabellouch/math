import OAI.Analysis.BoundedHochschild.CountableColumnRegrouping

namespace OAI

/-! Regrouping a countable matrix system inside a specified von Neumann
subalgebra. Only the matrix transitions, not the original ambient columns,
are required to belong to that subalgebra. -/

noncomputable section

open Filter

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X Y : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

theorem finite_columns_in_subalgebra (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (R : StarSubalgebra ℂ M) [IsClosed (R : Set M)] (eR : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] R)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) atTop 1)
    (hc : ∀ i j, (c i : M) * star (c j : M) ∈ R) (n : ℕ) [NeZero n] :
    ∃ v : Fin n → PartialIso M, (∀ j, (v j).initial = 1) ∧
      (∀ j k, j ≠ k → (v j).final * (v k).final = 0) ∧
      (∑ j, (v j).final = 1) ∧ ∀ j, (v j : M) ∈ R := by
  classical
  let σ := (Nat.divModEquiv n).symm
  let aM (j : Fin n) (i : ℕ) := columnTransition (c (σ (i, j))) (c i)
    ((hi _).trans (hi _).symm)
  let a (j : Fin n) (i : ℕ) : PartialIso R :=
    ⟨⟨(aM j i : M), hc _ _⟩, Subtype.ext (aM j i).mul_star_mul⟩
  have hai (j i) : ((a j i).initial : M) = (c i).final :=
    columnTransition_initial (c (σ (i, j))) (c i) ((hi _).trans (hi _).symm)
  have haf (j i) : ((a j i).final : M) = (c (σ (i, j))).final :=
    columnTransition_final (c (σ (i, j))) (c i) ((hi _).trans (hi _).symm)
  have haI (j : Fin n) (i k : ℕ) (hik : i ≠ k) :
      (a j i).initial * (a j k).initial = 0 := by
    apply Subtype.ext
    change ((a j i).initial : M) * ((a j k).initial : M) = 0
    rw [hai, hai]
    exact ho i k hik
  have haF (j : Fin n) (i k : ℕ) (hik : i ≠ k) :
      (a j i).final * (a j k).final = 0 := by
    apply Subtype.ext
    change ((a j i).final : M) * ((a j k).final : M) = 0
    rw [haf, haf]
    exact ho _ _ (fun h => hik (congrArg Prod.fst (σ.injective h)))
  choose v hvi hvf hvi_min hvf_min using fun j =>
    exists_countable_partialIso_sum eR (a j) (haI j) (haF j)
  have hinit (j : Fin n) : (v j).initial = 1 := by
    apply Subtype.ext
    apply projection_eq_one_of_column_bounds e c ht
      ((v j).initial_proj.map R.subtype)
    intro i
    have h := hvi j i
    change ((a j i).initial : M) ≤ ((v j).initial : M) at h
    rwa [hai] at h
  have hcross (j k : Fin n) (hjk : j ≠ k) (i l : ℕ) :
      (a j i).final * (a k l).final = 0 := by
    apply Subtype.ext
    change ((a j i).final : M) * ((a k l).final : M) = 0
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
  have hproj : IsStarProjection (∑ j, (v j).final) :=
    orthogonal_projection_finset_sum (fun j => (v j).final) (fun j => (v j).final_proj)
      horth Finset.univ
  have hsum : (∑ j, (v j).final) = 1 := by
    apply Subtype.ext
    apply projection_eq_one_of_column_bounds e c ht (hproj.map R.subtype)
    intro i
    let t := Nat.divModEquiv n i
    have hti : σ t = i := (Nat.divModEquiv n).symm_apply_apply i
    have hh : (c i).final ≤ ((v t.2).final : M) := by
      have h := hvf t.2 t.1
      change ((a t.2 t.1).final : M) ≤ ((v t.2).final : M) at h
      rw [haf] at h
      simpa only [hti] using h
    apply hh.trans
    exact show (v t.2).final ≤ ∑ j, (v j).final from
      Finset.single_le_sum (fun j _ => (v j).final_proj.nonneg) (Finset.mem_univ t.2)
  let w (j : Fin n) : PartialIso M :=
    ⟨((v j : R) : M), congrArg Subtype.val (v j).mul_star_mul⟩
  refine ⟨w, fun j => congrArg Subtype.val (hinit j), ?_, ?_, fun j => (v j : R).property⟩
  · intro j k hjk
    exact congrArg Subtype.val (horth j k hjk)
  · change (∑ j, ((v j).final : M)) = 1
    simpa using congrArg (fun z : R => (z : M)) hsum

end BoundedHochschild.KadisonRingrose

end

end OAI
