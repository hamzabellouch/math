import OAI.Analysis.FactorGeneration.NormalDimension

namespace OAI

/-! # Schroeder--Bernstein for concrete projection equivalence

The proof constructs the unilateral shift on the iterated defect of a
partial isometry, then adds the identity on its orthogonal complement.
The construction uses the existing strong sums of partial isometries;
no finiteness or trace assumption occurs.
-/

namespace Generator.Tracial

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

namespace PartialIsometry

private theorem power_initial (v : PartialIsometry M) (h : v.target ≤ v.support)
    {n : ℕ} (hn : 0 < n) : star (v.val ^ n) * v.val ^ n = v.support.val := by
  have hleft : v.support.val * v.val = v.val := (v.target_le_iff_mul _).mp h
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hz : n = 0
    · subst n
      simpa only [zero_add, pow_one] using v.initial
    · rw [pow_succ, star_mul]
      calc
        _ = star v.val * (star (v.val ^ n) * v.val ^ n) * v.val := by
          simp only [mul_assoc]
        _ = v.support.val := by
          rw [ih (Nat.pos_of_ne_zero hz), mul_assoc, hleft, v.initial]

private theorem defect_mul (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) :
    (AlgebraProjection.remainder p v.support hp).val * v.val = 0 := by
  change (v.support.val - p.val) * v.val = 0
  rw [sub_mul, (v.target_le_iff_mul _).mp (ht.trans hp),
    (v.target_le_iff_mul _).mp ht, sub_self]

private theorem defect_mul_pow (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) {n : ℕ} (hn : 0 < n) :
    (AlgebraProjection.remainder p v.support hp).val * v.val ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ', ← mul_assoc, defect_mul v p ht hp, zero_mul]

private def defectOrbit (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) (n : ℕ) : PartialIsometry M where
  support := AlgebraProjection.remainder p v.support hp
  val := v.val ^ n * (AlgebraProjection.remainder p v.support hp).val
  initial := by
    let d := AlgebraProjection.remainder p v.support hp
    have hd : d ≤ v.support := AlgebraProjection.remainder_le _ _ hp
    change star (v.val ^ n * d.val) * (v.val ^ n * d.val) = d.val
    rw [star_mul, d.property.isSelfAdjoint.star_eq]
    by_cases hn : n = 0
    · subst n
      simp only [pow_zero, star_one, mul_one, one_mul,
        d.property.isIdempotentElem.eq]
    · calc
        _ = d.val * (star (v.val ^ n) * v.val ^ n) * d.val := by
          simp only [mul_assoc]
        _ = d.val := by
          rw [power_initial v (ht.trans hp) (Nat.pos_of_ne_zero hn),
            projection_mul_of_le hd, d.property.isIdempotentElem.eq]

private theorem defectOrbit_target_le (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) (n : ℕ) :
    (defectOrbit v p ht hp n).target ≤ v.support := by
  apply ((defectOrbit v p ht hp n).target_le_iff_mul _).mpr
  change v.support.val * (v.val ^ n * (AlgebraProjection.remainder p v.support hp).val) =
    v.val ^ n * (AlgebraProjection.remainder p v.support hp).val
  cases n with
  | zero =>
    simp only [pow_zero, one_mul]
    exact AlgebraProjection.remainder_le p v.support hp
  | succ n =>
    rw [pow_succ']
    calc
      _ = ((v.support.val * v.val) * v.val ^ n) *
          (AlgebraProjection.remainder p v.support hp).val := by simp only [mul_assoc]
      _ = _ := by rw [(v.target_le_iff_mul _).mp (ht.trans hp)]

private theorem defectOrbit_zero (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) :
    (defectOrbit v p ht hp 0).target = AlgebraProjection.remainder p v.support hp := by
  apply Subtype.ext
  change (v.val ^ 0 * _) * star (v.val ^ 0 * _) = _
  simp only [pow_zero, one_mul,
    (AlgebraProjection.remainder p v.support hp).property.isSelfAdjoint.star_eq,
    (AlgebraProjection.remainder p v.support hp).property.isIdempotentElem.eq]

private theorem defectOrbit_cross (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) {i j : ℕ} (hij : i < j) :
    star (defectOrbit v p ht hp i).val * (defectOrbit v p ht hp j).val = 0 := by
  let d := AlgebraProjection.remainder p v.support hp
  have hd : d ≤ v.support := AlgebraProjection.remainder_le _ _ hp
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hij)
  have hk : 0 < k := by omega
  change star (v.val ^ i * d.val) * (v.val ^ (i + k) * d.val) = 0
  rw [star_mul, d.property.isSelfAdjoint.star_eq, pow_add]
  calc
    _ = (d.val * (star (v.val ^ i) * v.val ^ i)) * v.val ^ k * d.val := by
      simp only [mul_assoc]
    _ = d.val * v.val ^ k * d.val := by
      by_cases hi : i = 0
      · subst i
        simp only [pow_zero, star_one, mul_one]
      · rw [power_initial v (ht.trans hp) (Nat.pos_of_ne_zero hi),
          projection_mul_of_le hd]
    _ = 0 := by rw [defect_mul_pow v p ht hp hk, zero_mul]

private theorem defectOrbit_orthogonal (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) :
    Pairwise (fun i j => (defectOrbit v p ht hp i).target.val *
      (defectOrbit v p ht hp j).target.val = 0) := by
  have hforward {i j : ℕ} (hij : i < j) :
      (defectOrbit v p ht hp i).target.val *
        (defectOrbit v p ht hp j).target.val = 0 := by
    change ((defectOrbit v p ht hp i).val * star (defectOrbit v p ht hp i).val) *
      ((defectOrbit v p ht hp j).val * star (defectOrbit v p ht hp j).val) = 0
    calc
      _ = (defectOrbit v p ht hp i).val *
          (star (defectOrbit v p ht hp i).val * (defectOrbit v p ht hp j).val) *
          star (defectOrbit v p ht hp j).val := by simp only [mul_assoc]
      _ = 0 := by rw [defectOrbit_cross v p ht hp hij, mul_zero, zero_mul]
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hforward h
  · exact orthogonal_reverse _ _ (hforward h)

/-- A partial isometry whose range lies in its source has orthogonal copies
of its defect, all lying under the original source projection. -/
theorem defect_copies (v : PartialIsometry M) (h : v.target ≤ v.support) :
    ∃ a : ℕ → PartialIsometry M,
      (∀ n, (a n).support = AlgebraProjection.remainder v.target v.support h) ∧
      (∀ n, (a n).target ≤ v.support) ∧
      Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) :=
  ⟨defectOrbit v v.target le_rfl h, fun _ => rfl,
    defectOrbit_target_le v v.target le_rfl h, defectOrbit_orthogonal v v.target le_rfl h⟩

/-- A projection between the initial and final projections of a partial
isometry is equivalent to the initial projection. This is the shift form
of projection Schroeder--Bernstein. -/
theorem equivalent_intermediate (v : PartialIsometry M) (p : AlgebraProjection M)
    (ht : v.target ≤ p) (hp : p ≤ v.support) : v.support.Equivalent p := by
  let a := defectOrbit v p ht hp
  let d := AlgebraProjection.remainder p v.support hp
  have ho : Pairwise (fun i j => (a i).target.val * (a j).target.val = 0) :=
    defectOrbit_orthogonal v p ht hp
  let b (i : ℕ) := rangeLink (a i) (a (i + 1)) rfl
  have hbs (i : ℕ) : (b i).support = (a i).target := rfl
  have hbt (i : ℕ) : (b i).target = (a (i + 1)).target := rangeLink_target _ _ _
  obtain ⟨s, _, hs, hs'⟩ := traceFree_orthogonal_sum b
    (by intro i j hij; rw [hbs, hbs]; exact ho hij)
    (by intro i j hij; rw [hbt, hbt]; exact ho (by omega))
  have hsle : s.support ≤ v.support := (hs _).mpr (fun i => by
    rw [hbs]
    exact defectOrbit_target_le v p ht hp i)
  have hst : s.target ≤ s.support := (hs' _).mpr (fun i => by
    rw [hbt, ← hbs (i + 1)]
    exact (hs s.support).mp le_rfl (i + 1))
  have hd0 : (a 0).target = d := defectOrbit_zero v p ht hp
  have hds : d ≤ s.support := by
    rw [← hd0, ← hbs 0]
    exact (hs s.support).mp le_rfl 0
  let c : AlgebraProjection M := ⟨1 - d.val, d.property.one_sub⟩
  have hsc : s.target ≤ c := (hs' c).mpr (fun i => by
    rw [hbt]
    change (1 - d.val) * (a (i + 1)).target.val = (a (i + 1)).target.val
    rw [sub_mul, one_mul, ← hd0, ho (by omega), sub_zero])
  have hdo : d.val * s.target.val = 0 := by
    change (1 - d.val) * s.target.val = s.target.val at hsc
    rw [sub_mul, one_mul] at hsc
    exact sub_eq_self.mp hsc
  have hsplit : s.support = orthogonalSum d s.target hdo := by
    apply le_antisymm
    · apply (hs _).mpr
      intro i
      rw [hbs]
      cases i with
      | zero => rw [hd0]; exact le_orthogonalSum_left _ _ hdo
      | succ i =>
        rw [← hbt i]
        exact ((hs' s.target).mp le_rfl i).trans
          (le_orthogonalSum_right _ _ hdo)
    · exact orthogonalSum_le hdo hds hst
  let e := AlgebraProjection.remainder s.support v.support hsle
  have hse : s.support.val * e.val = 0 :=
    AlgebraProjection.remainder_orthogonal _ _ hsle
  have hte : s.target.val * e.val = 0 :=
    projection_orthogonal_of_le hse hst le_rfl
  let z := s.patch (onProjection e) hse (by
    rw [onProjection_target]
    exact hte)
  refine ⟨z, ?_, ?_⟩
  · apply Subtype.ext
    change s.support.val + e.val = v.support.val
    change s.support.val + (v.support.val - s.support.val) = v.support.val
    abel
  · apply Subtype.ext
    have hz := s.patch_target (onProjection e) hse (by
      rw [onProjection_target]
      exact hte)
    have he := congrArg (fun q : AlgebraProjection M => s.target.val + q.val)
      (onProjection_target e)
    have hz' : z.target.val = s.target.val + e.val := hz.trans he
    refine hz'.trans ?_
    change s.target.val + (v.support.val - s.support.val) = p.val
    rw [hsplit]
    change s.target.val + (v.support.val - (d.val + s.target.val)) = p.val
    change s.target.val + (v.support.val - ((v.support.val - p.val) + s.target.val)) = p.val
    abel

end PartialIsometry

namespace AlgebraProjection

/-- Comparable projections satisfy Schroeder--Bernstein without any finite
trace or finite-isometry assumption. -/
theorem equivalent_of_le_of_subequivalent {p q : AlgebraProjection M}
    (hpq : p ≤ q) (hqp : q.Subequivalent p) : p.Equivalent q := by
  obtain ⟨v, hv, ht⟩ := hqp
  exact equivalent_symm (by
    rw [← hv] at hpq ⊢
    exact v.equivalent_intermediate p ht hpq)

/-- Murray--von Neumann Schroeder--Bernstein in the concrete algebra. -/
theorem schroederBernstein {p q : AlgebraProjection M}
    (hpq : p.Subequivalent q) (hqp : q.Subequivalent p) : p.Equivalent q := by
  obtain ⟨v, hv, ht⟩ := hpq
  have hpr : p.Equivalent v.target := ⟨v, hv, rfl⟩
  have hqr : q.Subequivalent v.target := subequivalent_trans hqp hpr.subequivalent
  exact equivalent_trans hpr (equivalent_of_le_of_subequivalent ht hqr)

end AlgebraProjection

end

end Generator.Tracial

end OAI
