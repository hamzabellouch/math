import OAI.Analysis.BoundedHochschild.InfinitePairChains

namespace OAI

/-! A maximal properly infinite projection has finite complement. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma projection_mul_zero_of_bounds {p q r s : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hr : IsStarProjection r) (hs : IsStarProjection s)
    (hpq : p * q = 0) (hrp : r ≤ p) (hsq : s ≤ q) : r * s = 0 := by
  calc
    r * s = (r * p) * (q * s) := by
      rw [(hr.le_iff_mul_eq_left hp).mp hrp, (hs.le_iff_mul_eq_right hq).mp hsq]
    _ = r * (p * q) * s := by simp only [mul_assoc]
    _ = 0 := by rw [hpq, mul_zero, zero_mul]

/-- A von Neumann algebra contains a properly infinite projection with finite
complement. This includes the zero projection when the algebra is finite. -/
theorem exists_properlyInfinite_with_finite_complement (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    ∃ p : M, IsStarProjection p ∧ ProperlyInfiniteProjection p ∧ FiniteCorner (1 - p) := by
  classical
  let S : Set (PartialIso M × PartialIso M) := {a | IsInfinitePair a}
  have hzero : ((0, 0) : PartialIso M × PartialIso M) ∈ S := by
    simp only [S, Set.mem_ofPred_eq, IsInfinitePair, PartialIso.initial_zero,
      PartialIso.final_zero, le_refl, mul_zero, and_self]
  obtain ⟨a, _, hm⟩ := zorn_le_nonempty₀ S (fun C hC hchain b hb => by
    obtain ⟨c, hc, hu⟩ := infinitePair_chain_upper e C (fun a ha => hC ha) hchain ⟨b, hb⟩
    exact ⟨c, hc, hu⟩) (0, 0) hzero
  have ha : IsInfinitePair a := hm.1
  let p := a.1.initial
  have hp : IsStarProjection p := a.1.initial_proj
  refine ⟨p, hp, ⟨a.1, a.2, rfl, ha.1.symm, ha.2.1, ha.2.2.1, ha.2.2.2⟩, ?_⟩
  by_contra hn
  obtain ⟨q, hq, hqp, hq0, u, w, hui, hwi, huf, hwf, huw⟩ :=
    exists_properlyInfinite_subprojection e hp.one_sub hn
  have hpq : p * q = 0 := HochschildTypeII.projection_orthogonal_of_le_complement hp hq hqp
  have hi1 : a.1.initial * u.initial = 0 := by rw [hui]; exact hpq
  have hi2 : a.2.initial * w.initial = 0 := by rw [← ha.1, hwi]; exact hpq
  have hf1 : a.1.final * u.final = 0 :=
    projection_mul_zero_of_bounds hp hq a.1.final_proj u.final_proj hpq ha.2.1 huf
  have hf2 : a.2.final * w.final = 0 :=
    projection_mul_zero_of_bounds hp hq a.2.final_proj w.final_proj hpq ha.2.2.1 hwf
  let b := (a.1.orthogonalSum u hi1 hf1, a.2.orthogonalSum w hi2 hf2)
  have hbi : b.1.initial = p + q := by rw [PartialIso.orthogonalSum_initial, hui]
  have hbii : b.2.initial = p + q := by rw [PartialIso.orthogonalSum_initial, ← ha.1, hwi]
  have hbf : b.1.final = a.1.final + u.final := by
    exact PartialIso.orthogonalSum_final a.1 u hi1 hf1
  have hbff : b.2.final = a.2.final + w.final := by
    exact PartialIso.orthogonalSum_final a.2 w hi2 hf2
  have hb : b ∈ S := by
    refine ⟨hbi.trans hbii.symm, ?_, ?_, ?_⟩
    · rw [hbf, hbi]
      exact add_le_add ha.2.1 huf
    · rw [hbff, hbi]
      exact add_le_add ha.2.2.1 hwf
    · have hcross1 : a.1.final * w.final = 0 :=
        projection_mul_zero_of_bounds hp hq a.1.final_proj w.final_proj hpq ha.2.1 hwf
      have hcross2 : u.final * a.2.final = 0 := by
        have h := projection_mul_zero_of_bounds hp hq a.2.final_proj u.final_proj
          hpq ha.2.2.1 huf
        simpa only [star_mul, a.2.final_proj.isSelfAdjoint.star_eq,
          u.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star h
      rw [hbf, hbff]
      simp only [add_mul, mul_add, ha.2.2.2, huw, hcross1, hcross2, zero_add]
  have hab : a ≤ b := ⟨a.1.le_orthogonalSum u hi1 hf1, a.2.le_orthogonalSum w hi2 hf2⟩
  have he := le_antisymm (hm.2 hb hab) hab
  have hip : p + q = p := by
    have h := congrArg (fun b : PartialIso M × PartialIso M => b.1.initial) he
    exact hbi.symm.trans h
  exact hq0 (add_eq_left.mp hip)

end BoundedHochschild.KadisonRingrose

end

end OAI
