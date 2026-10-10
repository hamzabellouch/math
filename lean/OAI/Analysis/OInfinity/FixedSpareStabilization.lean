import OAI.Analysis.OInfinity.FixedSparePath

namespace OAI

/-! # Sampled-path stabilization in a fixed spare corner

A cyclic permutation converts a diagonal of path samples into adjacent
increments. The finite matrix corner and its complement remain explicit.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

section Diagonal
variable (q : E) (r : I → E) (hqstar : star q = q) (hqq : q * q = q)
variable (hr : ∀ i j, star (r i) * r j = if i = j then q else 0)

include hqstar hqq hr in
lemma fixedSpareDiagonalUnitary_one :
    fixedSpareDiagonalUnitary q r hqstar hqq hr (fun _ => 1)
      (fun _ => Commute.one_right _) = 1 := by
  apply Subtype.ext
  rw [fixedSpareDiagonalUnitary_deviation]
  change 1 + fixedSpareBlock r (fun _ => (1 : E) - 1) = 1
  simp only [sub_self, fixedSpareBlock, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]

include hqstar hqq hr in
lemma fixedSpareDiagonalUnitary_star (x : I → unitary E)
    (hx : ∀ i, Commute q (x i : E)) :
    star (fixedSpareDiagonalUnitary q r hqstar hqq hr x hx) =
      fixedSpareDiagonalUnitary q r hqstar hqq hr (fun i => star (x i))
        (fun i => by
          change Commute q (star (x i : E))
          simpa only [hqstar] using (hx i).star_star) := by
  apply Subtype.ext
  change star (fixedSpareBlock r (fun i => (x i : E)) + (1 - fixedSpareRange r)) = _
  rw [star_add, fixedSpareBlock_star, star_sub, star_one, fixedSpareRange_star]
  rfl

include hqstar hqq hr in
lemma fixedSpareDiagonalUnitary_sub_norm_le (x y : I → unitary E)
    (hx : ∀ i, Commute q (x i : E)) (hy : ∀ i, Commute q (y i : E))
    (C : ℝ) (hC : 0 ≤ C) (hxy : ∀ i, ‖(x i : E) - y i‖ ≤ C) :
    ‖(fixedSpareDiagonalUnitary q r hqstar hqq hr x hx : E) -
      fixedSpareDiagonalUnitary q r hqstar hqq hr y hy‖ ≤ C := by
  change ‖(fixedSpareBlock r (fun i => (x i : E)) + (1 - fixedSpareRange r)) -
    (fixedSpareBlock r (fun i => (y i : E)) + (1 - fixedSpareRange r))‖ ≤ C
  rw [add_sub_add_right_eq_sub]
  exact fixedSpareBlock_sub_norm_le q r hqstar hqq hr _ _ C hC hxy

include hqstar hqq hr in
lemma fixedSparePermutation_conjugate_diagonal (σ : Equiv.Perm I)
    (x : I → unitary E) (hx : ∀ i, Commute q (x i : E)) :
    fixedSparePermutationUnitary q r hqstar hqq hr σ *
      fixedSpareDiagonalUnitary q r hqstar hqq hr x hx *
        star (fixedSparePermutationUnitary q r hqstar hqq hr σ) =
      fixedSpareDiagonalUnitary q r hqstar hqq hr (fun i => x (σ.symm i))
        (fun i => hx (σ.symm i)) := by
  apply Subtype.ext
  change (fixedSparePermutationUnitary q r hqstar hqq hr σ : E) *
    (fixedSpareDiagonalUnitary q r hqstar hqq hr x hx : E) *
    star (fixedSparePermutationUnitary q r hqstar hqq hr σ : E) = _
  rw [fixedSpareDiagonalUnitary_deviation, fixedSpareDiagonalUnitary_deviation]
  rw [mul_add, add_mul, mul_one,
    (fixedSparePermutationUnitary q r hqstar hqq hr σ).prop.2,
    fixedSparePermutation_conjugate_block]

include hqstar hqq hr in
/-- Exact diagonal entries of the stabilized commutator. -/
lemma fixedSpareDiagonal_commutator (σ : Equiv.Perm I)
    (x y : I → unitary E) (hx : ∀ i, Commute q (x i : E))
    (hy : ∀ i, Commute q (y i : E)) :
    let d := fixedSpareDiagonalUnitary q r hqstar hqq hr x hx
    let c := fixedSparePermutationUnitary q r hqstar hqq hr σ
    fixedSpareDiagonalUnitary q r hqstar hqq hr y hy * (d * c * star d * star c) =
      fixedSpareDiagonalUnitary q r hqstar hqq hr
        (fun i => y i * (x i * star (x (σ.symm i))))
        (fun i => (hy i).mul_right ((hx i).mul_right
          (by
            change Commute q (star (x (σ.symm i) : E))
            simpa only [hqstar] using (hx (σ.symm i)).star_star))) := by
  dsimp only
  rw [show fixedSpareDiagonalUnitary q r hqstar hqq hr x hx *
      fixedSparePermutationUnitary q r hqstar hqq hr σ *
      star (fixedSpareDiagonalUnitary q r hqstar hqq hr x hx) *
      star (fixedSparePermutationUnitary q r hqstar hqq hr σ) =
      fixedSpareDiagonalUnitary q r hqstar hqq hr x hx *
        (fixedSparePermutationUnitary q r hqstar hqq hr σ *
        star (fixedSpareDiagonalUnitary q r hqstar hqq hr x hx) *
        star (fixedSparePermutationUnitary q r hqstar hqq hr σ)) by group]
  rw [fixedSpareDiagonalUnitary_star, fixedSparePermutation_conjugate_diagonal,
    fixedSpareDiagonalUnitary_mul, fixedSpareDiagonalUnitary_mul]

end Diagonal

/-- Every increment of size at most one gives a `9π` path after finite cyclic
stabilization. This estimate is independent of the number of samples. -/
lemma exists_fixedSpareDiagonal_path [Nontrivial E] (N : ℕ) [NeZero N]
    (q : E) (r : ZMod N → E) (hqstar : star q = q) (hqq : q * q = q)
    (hr : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (x y : ZMod N → unitary E) (hx : ∀ i, Commute q (x i : E))
    (hy : ∀ i, Commute q (y i : E))
    (hstep : ∀ i, ‖(y i : E) * ((x i : E) * star (x (i - 1) : E)) - 1‖ ≤ 1) :
    ∃ p : Path (1 : unitary E) (fixedSpareDiagonalUnitary q r hqstar hqq hr y hy),
      ∀ a b, ‖(p a : E) - p b‖ ≤ (9 * Real.pi) * |(a : ℝ) - b| := by
  let σ : Equiv.Perm (ZMod N) := Equiv.addRight 1
  let d := fixedSpareDiagonalUnitary q r hqstar hqq hr x hx
  let c := fixedSparePermutationUnitary q r hqstar hqq hr σ
  let u := fixedSpareDiagonalUnitary q r hqstar hqq hr y hy
  have he := fixedSpareDiagonal_commutator q r hqstar hqq hr σ x y hx hy
  have hnear : ‖((u * (d * c * star d * star c) : unitary E) : E) - 1‖ < 2 := by
    rw [he]
    have hone : (fixedSpareDiagonalUnitary q r hqstar hqq hr (fun _ => 1)
        (fun _ => Commute.one_right _) : E) = 1 :=
      congrArg Subtype.val (fixedSpareDiagonalUnitary_one q r hqstar hqq hr)
    rw [← hone]
    apply lt_of_le_of_lt (fixedSpareDiagonalUnitary_sub_norm_le q r hqstar hqq hr
      _ _ _ _ 1 zero_le_one ?_) (by norm_num)
    intro i
    change ‖(y i : E) * ((x i : E) * star (x (σ.symm i) : E)) - 1‖ ≤ 1
    have hprev : σ.symm i = i - 1 := by
      change i + -1 = i - 1
      exact (sub_eq_add_neg i 1).symm
    rw [hprev]
    exact hstep i
  obtain ⟨pc, hpc⟩ := exists_fixedSpareCycle_path N q r hqstar hqq hr
  obtain ⟨p, hp⟩ := exists_controlled_path_of_near_commutator u d c
    (4 * Real.pi) pc hpc hnear
  refine ⟨p, ?_⟩
  intro a b
  simpa only [show Real.pi + 2 * (4 * Real.pi) = 9 * Real.pi by ring] using hp a b

/-- Complement of the fixed isometry's range. -/
def fixedSpareProjection (z : E) : E := 1 - z * star z

lemma fixedSpareProjection_star (z : E) :
    star (fixedSpareProjection z) = fixedSpareProjection z := by
  simp only [fixedSpareProjection, star_sub, star_one, star_mul, star_star]

lemma fixedSpareProjection_sq (z : E) (hz : star z * z = 1) :
    fixedSpareProjection z * fixedSpareProjection z = fixedSpareProjection z := by
  have hp : (z * star z) * (z * star z) = z * star z := by
    calc
      _ = z * (star z * z) * star z := by noncomm_ring
      _ = _ := by rw [hz, mul_one]
  unfold fixedSpareProjection
  noncomm_ring [hp]

lemma fixedSpareProjection_mul (z : E) (hz : star z * z = 1) :
    fixedSpareProjection z * z = 0 := by
  unfold fixedSpareProjection
  rw [sub_mul, one_mul, mul_assoc, hz, mul_one, sub_self]

lemma fixedSpareUnitary_support (z : E)
    (u : unitary E) (hu : (u : E) * z = z) :
    Commute (fixedSpareProjection z) (u : E) ∧
      fixedSpareProjection z * ((u : E) - 1) = (u : E) - 1 ∧
      ((u : E) - 1) * fixedSpareProjection z = (u : E) - 1 := by
  have hus : star (u : E) * z = z := by
    have he := congrArg (fun x : E => star (u : E) * x) hu
    simpa only [← mul_assoc, u.prop.1, one_mul] using he.symm
  have hsu : star z * (u : E) = star z := by
    simpa only [star_mul, star_star] using congrArg star hus
  have hpu : (z * star z) * (u : E) = z * star z := by rw [mul_assoc, hsu]
  have hup : (u : E) * (z * star z) = z * star z := by rw [← mul_assoc, hu]
  have hqp : fixedSpareProjection z * (u : E) = (u : E) - z * star z := by
    rw [fixedSpareProjection, sub_mul, one_mul, hpu]
  have huq : (u : E) * fixedSpareProjection z = (u : E) - z * star z := by
    rw [fixedSpareProjection, mul_sub, mul_one, hup]
  refine ⟨hqp.trans huq.symm, ?_, ?_⟩
  · rw [mul_sub, mul_one, hqp, fixedSpareProjection]
    abel
  · rw [sub_mul, one_mul, huq, fixedSpareProjection]
    abel

/-- The zeroth copy is the original corner; all other copies lie inside
its fixed complement. No equality between the total range and one is used. -/
def fixedSpareCopies (z : E) (s : I → E) (i₀ i : I) : E :=
  if i = i₀ then fixedSpareProjection z else z * s i * fixedSpareProjection z

omit [Fintype I] in
lemma fixedSpareCopies_gram (z : E) (hz : star z * z = 1)
    (s : I → E) (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (i₀ : I) :
    ∀ i j, star (fixedSpareCopies z s i₀ i) * fixedSpareCopies z s i₀ j =
      if i = j then fixedSpareProjection z else 0 := by
  let q := fixedSpareProjection z
  have hqstar : star q = q := fixedSpareProjection_star z
  have hqq : q * q = q := fixedSpareProjection_sq z hz
  have hqz : q * z = 0 := fixedSpareProjection_mul z hz
  have hzq : star z * q = 0 := by
    simpa only [star_mul, hqstar, star_zero] using congrArg star hqz
  intro i j
  by_cases hi : i = i₀
  · subst i
    by_cases hj : j = i₀
    · subst j
      simp only [fixedSpareCopies, ite_true]
      change star q * q = q
      rw [hqstar, hqq]
    · simp only [fixedSpareCopies, ite_true, ite_eq_right hj, ite_eq_right (Ne.symm hj)]
      change star q * (z * s j * q) = 0
      rw [hqstar]
      calc
        _ = (q * z) * s j * q := by noncomm_ring
        _ = 0 := by rw [hqz, zero_mul, zero_mul]
  · by_cases hj : j = i₀
    · subst j
      simp only [fixedSpareCopies, ite_eq_right hi, ite_true]
      change star (z * s i * q) * q = 0
      rw [star_mul, star_mul, hqstar]
      calc
        _ = q * star (s i) * (star z * q) := by noncomm_ring
        _ = 0 := by rw [hzq, mul_zero]
    · simp only [fixedSpareCopies, ite_eq_right hi, ite_eq_right hj]
      change star (z * s i * q) * (z * s j * q) = if i = j then q else 0
      rw [star_mul, star_mul, hqstar]
      calc
        _ = q * star (s i) * (star z * z) * s j * q := by noncomm_ring
        _ = q * (star (s i) * s j) * q := by rw [hz, mul_one]; noncomm_ring
        _ = if i = j then q else 0 := by
          rw [hs]
          split_ifs <;> simp only [mul_one, hqq, mul_zero, zero_mul]

lemma fixedSpareCopies_diagonal (z : E) (hz : star z * z = 1)
    (s : I → E) (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (i₀ : I) (u : unitary E) (hu : (u : E) * z = z) :
    fixedSpareDiagonalUnitary (fixedSpareProjection z) (fixedSpareCopies z s i₀)
      (fixedSpareProjection_star z) (fixedSpareProjection_sq z hz)
      (fixedSpareCopies_gram z hz s hs i₀) (fun i => if i = i₀ then u else 1)
      (fun i => by
        split_ifs
        · exact (fixedSpareUnitary_support z u hu).1
        · exact Commute.one_right _) = u := by
  apply Subtype.ext
  rw [fixedSpareDiagonalUnitary_deviation]
  have he : (fun i => ((if i = i₀ then u else 1 : unitary E) : E) - 1) =
      (fun i => if i = i₀ then (u : E) - 1 else 0) := by
    funext i
    split_ifs
    · rfl
    · exact sub_self (1 : E)
  rw [he]
  simp only [fixedSpareBlock, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, fixedSpareCopies]
  rw [fixedSpareProjection_star,
    (fixedSpareUnitary_support z u hu).2.1,
    (fixedSpareUnitary_support z u hu).2.2]
  abel

/-- Equal mesh on a cyclic index set, with its last point strictly below one. -/
def fixedSpareMesh (N : ℕ) [NeZero N] (i : ZMod N) : unitInterval :=
  ⟨(i.val : ℝ) / N, by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast NeZero.pos N : (0 : ℝ) < N)).mpr
      exact_mod_cast (ZMod.val_lt i).le⟩

lemma fixedSpareMesh_zero (N : ℕ) [NeZero N] : fixedSpareMesh N 0 = 0 := by
  apply Subtype.ext
  change ((0 : ZMod N).val : ℝ) / N = 0
  simp only [ZMod.val_zero, Nat.cast_zero, zero_div]

lemma fixedSpareMesh_step (M : ℕ) (i : ZMod (M + 2)) (hi : i ≠ 0) :
    |(fixedSpareMesh (M + 2) i : ℝ) - fixedSpareMesh (M + 2) (i - 1)| =
      1 / (M + 2 : ℝ) := by
  let _ : Fact (1 < M + 2) := ⟨by omega⟩
  have hi1 : 1 ≤ i.val := Nat.succ_le_of_lt (ZMod.val_pos.mpr hi)
  have hp : (i - 1).val = i.val - 1 := ZMod.val_sub (by simpa only [ZMod.val_one] using hi1)
  change |(i.val : ℝ) / (M + 2 : ℕ) - ((i - 1).val : ℝ) / (M + 2 : ℕ)| = _
  rw [hp, Nat.cast_sub hi1, Nat.cast_one, ← sub_div]
  have he : (i.val : ℝ) - ((i.val : ℝ) - 1) = 1 := by ring
  rw [he, Nat.cast_add, Nat.cast_ofNat, abs_of_pos (by positivity)]

lemma fixedSpareMesh_last (M : ℕ) :
    |1 - (fixedSpareMesh (M + 2) (-1) : ℝ)| = 1 / (M + 2 : ℝ) := by
  change |1 - (((-1 : ZMod (M + 2)).val : ℝ) / (M + 2 : ℕ))| = _
  rw [show (-1 : ZMod (M + 2)).val = M + 1 from ZMod.val_neg_one (M + 1)]
  push_cast
  have he : (1 : ℝ) - (M + 1) / (M + 2) = 1 / (M + 2) := by
    field_simp
    ring
  rw [he, abs_of_pos (by positivity)]

lemma fixedSpare_mul_star_sub_one_norm (u v : unitary E) :
    ‖(u : E) * star (v : E) - 1‖ = ‖(u : E) - v‖ := by
  have he : (u : E) * star (v : E) - 1 = ((u : E) - v) * star (v : E) := by
    rw [sub_mul, v.prop.2]
  rw [he, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem v.prop)]

/-- A connected unitary that fixes one isometry has a uniformly controlled
path, using actual finite spare copies and actual samples of the given path. -/
lemma exists_uniform_fixedSpare_path [Nontrivial E]
    (s : ℕ → E) (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (z : E) (hz : star z * z = 1) (u : unitary E)
    (p : Path (1 : unitary E) u) (hfix : ∀ t, (p t : E) * z = z)
    (L : ℝ) (hp : ∀ a b, ‖(p a : E) - p b‖ ≤ L * |(a : ℝ) - b|) :
    ∃ v : Path (1 : unitary E) u,
      ∀ a b, ‖(v a : E) - v b‖ ≤ (9 * Real.pi) * |(a : ℝ) - b| := by
  obtain ⟨M, hM⟩ := exists_nat_gt L
  let N := M + 2
  let _ : NeZero N := ⟨by dsimp only [N]; omega⟩
  let a : ZMod N → E := fun i => s i.val
  have ha : ∀ i j, star (a i) * a j = if i = j then 1 else 0 := by
    intro i j
    dsimp only [a]
    rw [hs]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
    · rw [ite_eq_right hij, ite_eq_right (fun h => hij (ZMod.val_injective N h))]
  let q := fixedSpareProjection z
  let r := fixedSpareCopies z a (0 : ZMod N)
  have hqstar : star q = q := fixedSpareProjection_star z
  have hqq : q * q = q := fixedSpareProjection_sq z hz
  have hr := fixedSpareCopies_gram z hz a ha (0 : ZMod N)
  let x : ZMod N → unitary E := fun i => p (fixedSpareMesh N i)
  let y : ZMod N → unitary E := fun i => if i = 0 then u else 1
  have hx : ∀ i, Commute q (x i : E) := fun i =>
    (fixedSpareUnitary_support z (p (fixedSpareMesh N i)) (hfix _)).1
  have huz : (u : E) * z = z := by simpa only [p.target] using hfix 1
  have hy : ∀ i, Commute q (y i : E) := by
    intro i
    dsimp only [y]
    split_ifs
    · exact (fixedSpareUnitary_support z u huz).1
    · exact Commute.one_right _
  have hsmall : L / (M + 2 : ℝ) ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < M + 2)).mpr
    exact le_trans hM.le (by linarith)
  have hstep : ∀ i, ‖(y i : E) * ((x i : E) * star (x (i - 1) : E)) - 1‖ ≤ 1 := by
    intro i
    by_cases hi : i = 0
    · subst i
      have hx0 : x 0 = 1 := by dsimp only [x]; rw [fixedSpareMesh_zero, p.source]
      change ‖(u : E) * ((x 0 : E) * star (x (0 - 1) : E)) - 1‖ ≤ 1
      rw [hx0]
      change ‖(u : E) * (1 * star (x (0 - 1) : E)) - 1‖ ≤ 1
      rw [one_mul, fixedSpare_mul_star_sub_one_norm]
      have hb := hp 1 (fixedSpareMesh N (-1))
      rw [p.target] at hb
      change ‖(u : E) - x (-1)‖ ≤ L * |1 - (fixedSpareMesh N (-1) : ℝ)| at hb
      have hm := fixedSpareMesh_last M
      change |1 - (fixedSpareMesh N (-1) : ℝ)| = 1 / (M + 2 : ℝ) at hm
      rw [hm, ← div_eq_mul_one_div] at hb
      simpa only [zero_sub] using hb.trans hsmall
    · have hyi : y i = 1 := ite_eq_right hi
      rw [hyi]
      change ‖(1 : E) * ((x i : E) * star (x (i - 1) : E)) - 1‖ ≤ 1
      rw [one_mul, fixedSpare_mul_star_sub_one_norm]
      have hb := hp (fixedSpareMesh N i) (fixedSpareMesh N (i - 1))
      have hm := fixedSpareMesh_step M i hi
      change |(fixedSpareMesh N i : ℝ) - fixedSpareMesh N (i - 1)| =
        1 / (M + 2 : ℝ) at hm
      rw [hm, ← div_eq_mul_one_div] at hb
      exact hb.trans hsmall
  obtain ⟨v, hv⟩ := exists_fixedSpareDiagonal_path N q r hqstar hqq hr x y hx hy hstep
  have hend : fixedSpareDiagonalUnitary q r hqstar hqq hr y hy = u :=
    fixedSpareCopies_diagonal z hz a ha 0 u huz
  let w : Path (1 : unitary E) u := v.cast rfl hend.symm
  refine ⟨w, ?_⟩
  intro b c
  exact hv b c

end WeakPureInfiniteness

end

end OAI
