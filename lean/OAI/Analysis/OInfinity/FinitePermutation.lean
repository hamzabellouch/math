import OAI.Analysis.OInfinity.CocycleFlip

namespace OAI

/-! # Finite row permutations

Permutations of a coisometric finite row give genuine unitaries after adding
the ambient complement. Coordinate cycles factor into two reflections, so
these cycle unitaries have uniform controlled paths. This applies to finite
block permutations, not to the original nonzero-gauge row cocycle itself.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

def finiteRowPermutation (r : I → E) (σ : Equiv.Perm I) : E :=
  ∑ i, r (σ i) * star (r i)

omit [DecidableEq I] in
lemma finiteRowPermutation_star (r : I → E) (σ : Equiv.Perm I) :
    star (finiteRowPermutation r σ) = finiteRowPermutation r σ⁻¹ := by
  simp only [finiteRowPermutation, star_sum, star_mul, star_star]
  apply Fintype.sum_equiv σ
  intro i
  simp

lemma finiteRowPermutation_mul_row (q : E) (r : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hr : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (σ : Equiv.Perm I) (j : I) :
    finiteRowPermutation r σ * r j = r (σ j) := by
  rw [finiteRowPermutation, Finset.sum_mul]
  have hterm (i : I) : (r (σ i) * star (r i)) * r j =
      if i = j then r (σ j) else 0 := by
    rw [mul_assoc, hr]
    split_ifs with h
    · subst i
      exact finiteRow_right_support q r hqstar hqq hr _
    · exact mul_zero _
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma finiteRowPermutation_mul (q : E) (r : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hr : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (σ τ : Equiv.Perm I) :
    finiteRowPermutation r σ * finiteRowPermutation r τ = finiteRowPermutation r (σ * τ) := by
  change finiteRowPermutation r σ * (∑ i, r (τ i) * star (r i)) = _
  rw [Finset.mul_sum]
  simp only [← mul_assoc, finiteRowPermutation_mul_row q r hqstar hqq hr]
  rfl

omit [DecidableEq I] in
lemma finiteRowPermutation_one (q : E) (r : I → E)
    (hsum : (∑ i, r i * star (r i)) = q) : finiteRowPermutation r 1 = q := by
  simpa only [finiteRowPermutation, Equiv.Perm.one_apply] using hsum

lemma finiteRowPermutation_support (q : E) (r : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hr : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (hsum : (∑ i, r i * star (r i)) = q) (σ : Equiv.Perm I) :
    q * finiteRowPermutation r σ = finiteRowPermutation r σ ∧
      finiteRowPermutation r σ * q = finiteRowPermutation r σ := by
  have hstar (i : I) : star (r i) * q = star (r i) := by
    simpa only [star_mul, hqstar] using
      congrArg star (finiteRow_left_support q r hqstar hqq hr hsum i)
  constructor
  · simp only [finiteRowPermutation, Finset.mul_sum, ← mul_assoc,
      finiteRow_left_support q r hqstar hqq hr hsum]
  · simp only [finiteRowPermutation, Finset.sum_mul, mul_assoc, hstar]

lemma finiteRowPermutation_gram (q : E) (r : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hr : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (hsum : (∑ i, r i * star (r i)) = q) (σ : Equiv.Perm I) :
    star (finiteRowPermutation r σ) * finiteRowPermutation r σ = q ∧
      finiteRowPermutation r σ * star (finiteRowPermutation r σ) = q := by
  constructor
  · rw [finiteRowPermutation_star, finiteRowPermutation_mul q r hqstar hqq hr,
      inv_mul_cancel, finiteRowPermutation_one q r hsum]
  · rw [finiteRowPermutation_star, finiteRowPermutation_mul q r hqstar hqq hr,
      mul_inv_cancel, finiteRowPermutation_one q r hsum]

def finiteRowPermutationUnitary (q : E) (r : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hr : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (hsum : (∑ i, r i * star (r i)) = q) (σ : Equiv.Perm I) : unitary E :=
  ⟨relativeUnitaryExtension q (finiteRowPermutation r σ),
    relativeUnitaryExtension_mem q _ hqstar hqq
      (finiteRowPermutation_support q r hqstar hqq hr hsum σ).1
      (finiteRowPermutation_support q r hqstar hqq hr hsum σ).2
      (finiteRowPermutation_gram q r hqstar hqq hr hsum σ).1
      (finiteRowPermutation_gram q r hqstar hqq hr hsum σ).2⟩

lemma finiteRowPermutationUnitary_mul (q : E) (r : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hr : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (hsum : (∑ i, r i * star (r i)) = q) (σ τ : Equiv.Perm I) :
    finiteRowPermutationUnitary q r hqstar hqq hr hsum (σ * τ) =
      finiteRowPermutationUnitary q r hqstar hqq hr hsum σ *
        finiteRowPermutationUnitary q r hqstar hqq hr hsum τ := by
  apply Subtype.ext
  have hσ := finiteRowPermutation_support q r hqstar hqq hr hsum σ
  have hτ := finiteRowPermutation_support q r hqstar hqq hr hsum τ
  change finiteRowPermutation r (σ * τ) + (1 - q) =
    (finiteRowPermutation r σ + (1 - q)) * (finiteRowPermutation r τ + (1 - q))
  rw [← finiteRowPermutation_mul q r hqstar hqq hr σ τ]
  noncomm_ring [hσ.2, hτ.1, hqq]

lemma finiteRowPermutationUnitary_involution (q : E) (r : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hr : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (hsum : (∑ i, r i * star (r i)) = q) (σ : Equiv.Perm I) (hσ : σ * σ = 1) :
    star (finiteRowPermutationUnitary q r hqstar hqq hr hsum σ : E) =
      (finiteRowPermutationUnitary q r hqstar hqq hr hsum σ : E) := by
  have hinv : σ⁻¹ = σ := by
    calc
      σ⁻¹ = σ⁻¹ * (σ * σ) := by rw [hσ, mul_one]
      _ = σ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  change star (finiteRowPermutation r σ + (1 - q)) = finiteRowPermutation r σ + (1 - q)
  rw [star_add, star_sub, star_one, hqstar, finiteRowPermutation_star, hinv]

/-- A selfadjoint unitary has a two-piece path with a fixed speed bound. -/
lemma exists_controlled_selfadjoint_unitary_path [Nontrivial E] (u : unitary E)
    (hu : star (u : E) = (u : E)) :
    ∃ p : Path (1 : unitary E) u,
      ∀ t s, ‖(p t : E) - p s‖ ≤ (2 * Real.pi) * |(t : ℝ) - s| := by
  have hI : Complex.I ∈ unitary ℂ := by constructor <;> simp
  let v : unitary E := ⟨Complex.I • (u : E), Unitary.smul_mem_of_mem hI u.property⟩
  have huu : (u : E) * (u : E) = 1 := by simpa only [hu] using u.property.1
  have hs1 : star ((v : E) - 1) * ((v : E) - 1) = (2 : ℂ) • (1 : E) := by
    change star (Complex.I • (u : E) - 1) * (Complex.I • (u : E) - 1) = _
    simp only [star_sub, star_smul, star_one, Complex.star_def, Complex.conj_I, hu,
      sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, huu]
    module_nf
    norm_num [Complex.I_sq]
  have hs2 : star ((u : E) - v) * ((u : E) - v) = (2 : ℂ) • (1 : E) := by
    change star ((u : E) - Complex.I • (u : E)) * ((u : E) - Complex.I • (u : E)) = _
    simp only [star_sub, star_smul, Complex.star_def, Complex.conj_I, hu, sub_mul,
      mul_sub, smul_mul_assoc, mul_smul_comm, huu]
    module_nf
    norm_num [Complex.I_sq]
  have hn1 : ‖(v : E) - 1‖ < 2 := by
    have h := congrArg norm hs1
    rw [CStarRing.norm_star_mul_self, norm_smul, norm_one] at h
    norm_num at h
    nlinarith [norm_nonneg ((v : E) - 1)]
  have hn2 : ‖(u : E) - v‖ < 2 := by
    have h := congrArg norm hs2
    rw [CStarRing.norm_star_mul_self, norm_smul, norm_one] at h
    norm_num at h
    nlinarith [norm_nonneg ((u : E) - v)]
  let p := Unitary.path 1 v hn1
  let r := Unitary.path v u hn2
  exact ⟨p.trans r, unitaryPath_trans_sub_norm_le p r Real.pi
    (unitary_shortPath_sub_norm_le 1 v hn1) (unitary_shortPath_sub_norm_le v u hn2)⟩

/-- Reflection of the coordinate positions of a finite word. -/
def finiteCoordinateReflection (m : ℕ) (c : ZMod m) : Equiv.Perm (ZMod m → I) where
  toFun w i := w (c - i)
  invFun w i := w (c - i)
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

def finiteCoordinateCycle (m : ℕ) : Equiv.Perm (ZMod m → I) where
  toFun w i := w (i + 1)
  invFun w i := w (i - 1)
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

omit [Fintype I] [DecidableEq I] in
lemma finiteCoordinateReflection_sq (m : ℕ) (c : ZMod m) :
    finiteCoordinateReflection (I := I) m c * finiteCoordinateReflection m c = 1 := by
  ext w i
  change w (c - (c - i)) = w i
  congr 1
  ring

omit [Fintype I] [DecidableEq I] in
lemma finiteCoordinateCycle_factor (m : ℕ) :
    finiteCoordinateCycle (I := I) m =
      finiteCoordinateReflection m 0 * finiteCoordinateReflection m 1 := by
  ext w i
  change w (i + 1) = w (1 - (0 - i))
  congr 1
  ring

/-- The cycle on a finite word row is a product of two actual selfadjoint
row-permutation unitaries, so its path bound is independent of word length. -/
lemma exists_controlled_coordinateCycle_path [Nontrivial E] (m : ℕ) [NeZero m]
    (q : E) (r : (ZMod m → I) → E) (hqstar : star q = q) (hqq : q * q = q)
    (hr : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (hsum : (∑ i, r i * star (r i)) = q) :
    ∃ p : Path (1 : unitary E)
        (finiteRowPermutationUnitary q r hqstar hqq hr hsum (finiteCoordinateCycle m)),
      ∀ t s, ‖(p t : E) - p s‖ ≤ (4 * Real.pi) * |(t : ℝ) - s| := by
  let a := finiteRowPermutationUnitary q r hqstar hqq hr hsum (finiteCoordinateReflection m 0)
  let b := finiteRowPermutationUnitary q r hqstar hqq hr hsum (finiteCoordinateReflection m 1)
  obtain ⟨p, hp⟩ := exists_controlled_selfadjoint_unitary_path a
    (finiteRowPermutationUnitary_involution q r hqstar hqq hr hsum _ (finiteCoordinateReflection_sq m 0))
  obtain ⟨u, hu⟩ := exists_controlled_selfadjoint_unitary_path b
    (finiteRowPermutationUnitary_involution q r hqstar hqq hr hsum _ (finiteCoordinateReflection_sq m 1))
  have hab : finiteRowPermutationUnitary q r hqstar hqq hr hsum (finiteCoordinateCycle m) = a * b := by
    rw [finiteCoordinateCycle_factor, finiteRowPermutationUnitary_mul]
  let result : Path (1 : unitary E)
      (finiteRowPermutationUnitary q r hqstar hqq hr hsum (finiteCoordinateCycle m)) :=
    (p.mul u).cast (by simp) hab
  refine ⟨result, ?_⟩
  intro t s
  change ‖((p.mul u) t : E) - (p.mul u) s‖ ≤ _
  simpa only [show 2 * Real.pi + 2 * Real.pi = 4 * Real.pi by ring] using
    unitaryPath_mul_sub_norm_le p u (2 * Real.pi) (2 * Real.pi) hp hu t s

end WeakPureInfiniteness

end

end OAI
