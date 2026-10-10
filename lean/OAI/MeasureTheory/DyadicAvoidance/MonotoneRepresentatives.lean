import Mathlib

namespace OAI

universe u_α u_ι

noncomputable section

open scoped BigOperators

namespace Problem310.ScaleDiscretization

/-- On a chain of integer vectors, the sum of the coordinates determines the vector. -/
lemma vector_eq_of_sum_eq {α : Type u_α} {ι : Type u_ι} [LinearOrder α] [Fintype ι]
    {s : Set α} {f : α → ι → ℤ} (hf : MonotoneOn f s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    (hs : (∑ i, f x i) = ∑ i, f y i) : f x = f y := by
  classical
  rcases le_total x y with hxy | hyx
  · funext i
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hf hx hy hxy i)).mp hs i
      (Finset.mem_univ i)
  · funext i
    exact ((Finset.sum_eq_sum_iff_of_le (fun i _ => hf hy hx hyx i)).mp hs.symm i
      (Finset.mem_univ i)).symm

/-- A monotone family of finitely many integer-valued functions has a small common
representative set. Unlike a breakpoint construction, this also handles every boundary
value without a separate endpoint convention. -/
theorem exists_monotone_representatives {α : Type u_α} {ι : Type u_ι} [LinearOrder α] [Fintype ι]
    (a b : α) (hab : a ≤ b) (f : α → ι → ℤ)
    (hf : MonotoneOn f (Set.Icc a b)) :
    ∃ R : Finset α,
      (∀ t ∈ R, t ∈ Set.Icc a b) ∧
      R.card ≤ ((∑ i, f b i) + 1 - ∑ i, f a i).toNat ∧
      ∀ t ∈ Set.Icc a b, ∃ t' ∈ R, f t' = f t := by
  classical
  let rank : α → ℤ := fun t => ∑ i, f t i
  let rep : ℤ → α := fun k =>
    if h : ∃ t, t ∈ Set.Icc a b ∧ rank t = k then Classical.choose h else a
  have rep_mem (k : ℤ) : rep k ∈ Set.Icc a b := by
    dsimp [rep]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact ⟨le_rfl, hab⟩
  have rep_rank {k : ℤ} (h : ∃ t, t ∈ Set.Icc a b ∧ rank t = k) :
      rank (rep k) = k := by
    dsimp [rep]
    rw [dite_eq_left h]
    exact (Classical.choose_spec h).2
  refine ⟨(Finset.Icc (rank a) (rank b)).image rep, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    exact rep_mem k
  · exact (Finset.card_image_le).trans_eq (Int.card_Icc _ _)
  · intro t ht
    have hlow : rank a ≤ rank t := by
      exact Finset.sum_le_sum fun i _ => hf ⟨le_rfl, hab⟩ ht ht.1 i
    have hhigh : rank t ≤ rank b := by
      exact Finset.sum_le_sum fun i _ => hf ht ⟨hab, le_rfl⟩ ht.2 i
    refine ⟨rep (rank t), Finset.mem_image.mpr ⟨rank t, ?_, rfl⟩, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hlow, hhigh⟩
    · exact vector_eq_of_sum_eq hf (rep_mem _) ht (rep_rank ⟨t, ht, rfl⟩)

/-- An integer floor can increase by at most the ceiling of the displacement. -/
lemma floor_sub_floor_le_ceil (x y : ℝ) : ⌊y⌋ - ⌊x⌋ ≤ ⌈y - x⌉ := by
  have hy := Int.floor_le y
  have hx := Int.lt_floor_add_one x
  have hc := Int.le_ceil (y - x)
  have h : ((⌊y⌋ - ⌊x⌋ : ℤ) : ℝ) < (⌈y - x⌉ : ℝ) + 1 := by
    push_cast
    linarith
  have hi : ⌊y⌋ - ⌊x⌋ < ⌈y - x⌉ + 1 := by exact_mod_cast h
  omega

/-- Simultaneous floor keys on an affine path admit at most one plus the sum of
their (rounded-up) displacements many representatives. -/
theorem exists_affine_floor_representatives {ι : Type u_ι} [Fintype ι]
    (a b : ℝ) (hab : a ≤ b) (u v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc a b) ∧
      R.card ≤ (1 + ∑ i, ⌈v i * (b - a)⌉).toNat ∧
      ∀ t ∈ Set.Icc a b, ∃ t' ∈ R,
        ∀ i, ⌊u i + v i * t'⌋ = ⌊u i + v i * t⌋ := by
  classical
  let f : ℝ → ι → ℤ := fun t i => ⌊u i + v i * t⌋
  have hf : MonotoneOn f (Set.Icc a b) := by
    intro x hx y hy hxy i
    apply Int.floor_le_floor
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy (hv i))
  obtain ⟨R, hR, hcard, hrep⟩ := exists_monotone_representatives a b hab f hf
  refine ⟨R, hR, hcard.trans ?_, ?_⟩
  · apply Int.toNat_le_toNat
    have hi (i : ι) : f b i - f a i ≤ ⌈v i * (b - a)⌉ := by
      have h := floor_sub_floor_le_ceil (u i + v i * a) (u i + v i * b)
      convert h using 1
      congr 1
      ring
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    rw [Finset.sum_sub_distrib] at hs
    linarith
  · intro t ht
    obtain ⟨t', ht', heq⟩ := hrep t ht
    exact ⟨t', ht', fun i => congrFun heq i⟩

/-- A uniform displacement bound gives a particularly convenient natural-valued
cardinality estimate for the normalized scale interval. -/
theorem exists_unit_affine_floor_representatives {ι : Type u_ι} [Fintype ι]
    (u v : ι → ℝ) (D : ℕ) (hv : ∀ i, 0 ≤ v i) (hD : ∀ i, v i ≤ (D : ℝ)) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + Fintype.card ι * D ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ i, ⌊u i + v i * t'⌋ = ⌊u i + v i * t⌋ := by
  classical
  obtain ⟨R, hR, hcard, hrep⟩ :=
    exists_affine_floor_representatives 1 2 (by norm_num) u v hv
  refine ⟨R, hR, hcard.trans ?_, hrep⟩
  have hi (i : ι) : ⌈v i * (2 - 1)⌉ ≤ (D : ℤ) := by
    apply Int.ceil_le.mpr
    norm_num
    exact hD i
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have hsum : 1 + ∑ i, ⌈v i * (2 - 1)⌉ ≤ (1 + Fintype.card ι * D : ℕ) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    push_cast
    linarith
  exact (Int.toNat_le_toNat hsum).trans_eq (Int.toNat_natCast _)

/-- The padding bound controls the scale-parameter slope of each finest grid key. -/
lemma dyadic_grid_slope_le (B n L : ℕ) (h : B ≤ n + L) :
    (2 : ℝ) ^ B * ((2 : ℝ)⁻¹) ^ n ≤ (2 : ℝ) ^ L := by
  rw [inv_pow, ← div_eq_mul_inv]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mpr
  rw [← pow_add]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)

/-- Simultaneous representatives for the finest dyadic grid keys in a family of
local routing tests. Only the padding inequalities are needed. -/
theorem exists_dyadic_grid_representatives {ι : Type u_ι} [Fintype ι]
    (x : ℝ) (B n : ι → ℕ) (L : ℕ) (hspan : ∀ i, B i ≤ n i + L) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + Fintype.card ι * 2 ^ L ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ i, ⌊(2 : ℝ) ^ B i * (x + t' * ((2 : ℝ)⁻¹) ^ n i)⌋ =
          ⌊(2 : ℝ) ^ B i * (x + t * ((2 : ℝ)⁻¹) ^ n i)⌋ := by
  let u : ι → ℝ := fun i => (2 : ℝ) ^ B i * x
  let v : ι → ℝ := fun i => (2 : ℝ) ^ B i * ((2 : ℝ)⁻¹) ^ n i
  have hv (i : ι) : 0 ≤ v i := by dsimp [v]; positivity
  have hD (i : ι) : v i ≤ ((2 ^ L : ℕ) : ℝ) := by
    simpa [v] using dyadic_grid_slope_le (B i) (n i) L (hspan i)
  obtain ⟨R, hR, hcard, hrep⟩ :=
    exists_unit_affine_floor_representatives u v (2 ^ L) hv hD
  refine ⟨R, hR, hcard, ?_⟩
  intro t ht
  obtain ⟨t', ht', heq⟩ := hrep t ht
  refine ⟨t', ht', ?_⟩
  intro i
  convert heq i using 1 <;> congr 1 <;> dsimp [u, v] <;> ring

/-- Passing from a real-line dyadic cell to its periodic key loses no information. -/
lemma periodic_floor_eq_of_floor_eq (q : ℕ) {y z : ℝ}
    (h : ⌊(2 : ℝ) ^ q * y⌋ = ⌊(2 : ℝ) ^ q * z⌋) :
    ⌊(2 : ℝ) ^ q * Int.fract y⌋ = ⌊(2 : ℝ) ^ q * Int.fract z⌋ := by
  have hcancel (w : ℝ) : ⌊(2 : ℝ) ^ q * w⌋ / (2 : ℤ) ^ q = ⌊w⌋ := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      Int.natCast_mul_floor_div_cancel (n := 2 ^ q) (by positivity) w
  have hfloor : ⌊y⌋ = ⌊z⌋ := by
    rw [← hcancel y, ← hcancel z, h]
  have hkey (w : ℝ) : ⌊(2 : ℝ) ^ q * Int.fract w⌋ =
      ⌊(2 : ℝ) ^ q * w⌋ - (2 : ℤ) ^ q * ⌊w⌋ := by
    rw [Int.fract]
    have heq : (2 : ℝ) ^ q * (w - (⌊w⌋ : ℝ)) =
        (2 : ℝ) ^ q * w - (((2 : ℤ) ^ q * ⌊w⌋ : ℤ) : ℝ) := by
      push_cast
      ring
    rw [heq, Int.floor_sub_intCast]
  rw [hkey, hkey, h, hfloor]

/-- Periodic versions of all finest keys agree at one of the same representatives. -/
theorem exists_periodic_dyadic_representatives {ι : Type u_ι} [Fintype ι]
    (x : ℝ) (B n : ι → ℕ) (L : ℕ) (hspan : ∀ i, B i ≤ n i + L) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + Fintype.card ι * 2 ^ L ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ i, ⌊(2 : ℝ) ^ B i * Int.fract (x + t' * ((2 : ℝ)⁻¹) ^ n i)⌋ =
          ⌊(2 : ℝ) ^ B i * Int.fract (x + t * ((2 : ℝ)⁻¹) ^ n i)⌋ := by
  obtain ⟨R, hR, hcard, hrep⟩ := exists_dyadic_grid_representatives x B n L hspan
  refine ⟨R, hR, hcard, ?_⟩
  intro t ht
  obtain ⟨t', ht', heq⟩ := hrep t ht
  exact ⟨t', ht', fun i => periodic_floor_eq_of_floor_eq (B i) (heq i)⟩

/-- Deterministic representatives simultaneously work for every assignment of local
predicates that factors through the indicated periodic keys. In particular the
representatives do not depend on the random selector or terminal tables. -/
theorem exists_local_predicate_representatives {ι : Type u_ι} [Fintype ι]
    (x : ℝ) (B n : ι → ℕ) (L : ℕ) (hspan : ∀ i, B i ≤ n i + L) :
    ∃ R : Finset ℝ,
      (∀ t ∈ R, t ∈ Set.Icc (1 : ℝ) 2) ∧
      R.card ≤ 1 + Fintype.card ι * 2 ^ L ∧
      ∀ t ∈ Set.Icc (1 : ℝ) 2, ∃ t' ∈ R,
        ∀ Q : ι → ℝ → Bool,
          (∀ i y z, ⌊(2 : ℝ) ^ B i * Int.fract y⌋ =
            ⌊(2 : ℝ) ^ B i * Int.fract z⌋ → Q i y = Q i z) →
          ∀ i, Q i (x + t' * ((2 : ℝ)⁻¹) ^ n i) =
            Q i (x + t * ((2 : ℝ)⁻¹) ^ n i) := by
  obtain ⟨R, hR, hcard, hrep⟩ := exists_periodic_dyadic_representatives x B n L hspan
  refine ⟨R, hR, hcard, ?_⟩
  intro t ht
  obtain ⟨t', ht', heq⟩ := hrep t ht
  exact ⟨t', ht', fun Q hQ i => hQ i _ _ (heq i)⟩

/-- The stronger monotone-key estimate is within the entropy budget. -/
lemma representative_card_budget (M r D : ℕ) (hM : 1 ≤ M) (hr : 1 ≤ r) :
    1 + (M - 1) * r * D ≤ 20 * M * r * (1 + D) := by
  have hMr : 1 ≤ M * r := by nlinarith
  calc
    1 + (M - 1) * r * D ≤ M * r + M * r * D := by
      exact Nat.add_le_add hMr
        (Nat.mul_le_mul_right D (Nat.mul_le_mul_right r (Nat.sub_le M 1)))
    _ = M * r * (1 + D) := by ring
    _ ≤ 20 * M * r * (1 + D) := by nlinarith

end Problem310.ScaleDiscretization

end

end OAI
