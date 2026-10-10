import OAI.Analysis.OInfinity.ClockFragmentation
import OAI.Analysis.OInfinity.ConnectedCocycleGluing

namespace OAI

/-! # The finite permutation cocycle of the canonical binary shift

The one-step cocycle swaps the first two letters. Its iterates are the
right cyclic permutations of finite words. This balanced finite-matrix
formula is separate from the nonzero-gauge cocycles of incomplete rows.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma finiteCoordinateCycle_inv_eq_cons {I : Type*} (n : ℕ) (w : Fin (n + 1) → I) :
    (finiteCoordinateCycle (n + 1))⁻¹ w = Fin.cons (w (Fin.last n)) (Fin.init w) := by
  have h : finiteCoordinateCycle (n + 1) (Fin.cons (w (Fin.last n)) (Fin.init w)) = w := by
    rw [finiteCoordinateCycle_eq_snoc, Fin.tail_cons, Fin.cons_zero, Fin.snoc_init_self]
  let σ : Equiv.Perm (Fin (n + 1) → I) := finiteCoordinateCycle (n + 1)
  change σ.symm w = _
  calc
    σ.symm w = σ.symm (σ (Fin.cons (w (Fin.last n)) (Fin.init w))) := congrArg σ.symm h.symm
    _ = _ := σ.symm_apply_apply _

lemma finiteJointWord_right_cycle (s : Fin 2 → E) (n : ℕ)
    (w : Fin (n + 2) → Fin 2) :
    finiteJointWord s s (n + 1) ((finiteCoordinateCycle (n + 2))⁻¹ w) =
      s (w (Fin.last (n + 1))) * finiteJointWord s s n (Fin.init w) := by
  rw [finiteCoordinateCycle_inv_eq_cons]
  rfl

/-- The right cycle on all words of length `n+1`. -/
def canonicalShiftCycle (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) (n : ℕ) : unitary E :=
  finiteRowPermutationUnitary 1 (finiteJointWord s s n) (by simp) (by simp)
    (finiteJointWord_gram 1 s s (by simp) (by simp) hs hs hsum hsum n)
    (finiteJointWord_sum 1 s s (by simp) (by simp) hs hsum hsum n)
    (finiteCoordinateCycle (n + 1))⁻¹

lemma canonicalShiftCycle_mul_word (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) (n : ℕ)
    (w : Fin (n + 1) → Fin 2) :
    (canonicalShiftCycle s hs hsum n : E) * finiteJointWord s s n w =
      finiteJointWord s s n ((finiteCoordinateCycle (n + 1))⁻¹ w) := by
  change (finiteRowPermutation _ _ + (1 - 1)) * _ = _
  rw [sub_self, add_zero]
  exact finiteRowPermutation_mul_row 1 (finiteJointWord s s n) (by simp) (by simp)
    (finiteJointWord_gram 1 s s (by simp) (by simp) hs hs hsum hsum n) _ w

lemma canonicalShiftCycle_zero (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) : canonicalShiftCycle s hs hsum 0 = 1 := by
  apply Subtype.ext
  apply finiteRow_eq_of_mul_row_eq 1 s hsum _ _ (mul_one _) (mul_one _)
  intro i
  have h := canonicalShiftCycle_mul_word s hs hsum 0 (fun _ => i)
  change (canonicalShiftCycle s hs hsum 0 : E) * s i = s i at h
  change (canonicalShiftCycle s hs hsum 0 : E) * s i = 1 * s i
  simpa only [one_mul] using h

lemma canonicalShiftCycle_one_mul (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) (i j : Fin 2) :
    (canonicalShiftCycle s hs hsum 1 : E) * (s i * s j) = s j * s i := by
  have h := canonicalShiftCycle_mul_word s hs hsum 1 ![i, j]
  rw [finiteJointWord_right_cycle] at h
  change (canonicalShiftCycle s hs hsum 1 : E) * (s i * s j) = s j * s i at h
  exact h

lemma canonicalShiftCycle_one_generator (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) (i : Fin 2) :
    (canonicalShiftCycle s hs hsum 1 : E) * s i = finiteRowShift s (s i) := by
  apply finiteRow_eq_of_mul_row_eq 1 s hsum _ _ (mul_one _) (mul_one _)
  intro j
  rw [mul_assoc, canonicalShiftCycle_one_mul,
    finiteRowShift_mul_row 1 s hs _ (mul_one _)]

/-- The finite cyclic permutation is the actual group cocycle of the
one-step flip, with its orientation retained. -/
lemma canonicalShiftCycle_succ (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) (n : ℕ) :
    canonicalShiftCycle s hs hsum (n + 1) =
      canonicalShiftCycle s hs hsum 1 *
        binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
          (by simpa using hs 1 1) (by simpa using hs 0 1)
          (canonicalShiftCycle s hs hsum n) := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, binarySplitHom_coe s hs hsum]
  apply finiteRow_eq_of_mul_row_eq 1 (finiteJointWord s s (n + 1))
    (finiteJointWord_sum 1 s s (by simp) (by simp) hs hsum hsum (n + 1)) _ _
    (mul_one _) (mul_one _)
  intro w
  rw [canonicalShiftCycle_mul_word, finiteJointWord_right_cycle]
  rw [mul_assoc (canonicalShiftCycle s hs hsum 1 : E)]
  cases n with
  | zero =>
    rw [canonicalShiftCycle_zero]
    have hφ : finiteRowShift s 1 = 1 := by simpa only [finiteRowShift, mul_one] using hsum
    change s (w (Fin.last 1)) * finiteJointWord s s 0 (Fin.init w) =
      (canonicalShiftCycle s hs hsum 1 : E) * (finiteRowShift s 1 * finiteJointWord s s 1 w)
    rw [hφ, one_mul]
    change s (w (Fin.last 1)) * s ((Fin.init w) 0) =
      (canonicalShiftCycle s hs hsum 1 : E) * (s (w 0) * s ((Fin.tail w) 0))
    rw [canonicalShiftCycle_one_mul]
    rfl
  | succ n =>
    change s (w (Fin.last (n + 2))) * finiteJointWord s s (n + 1) (Fin.init w) =
      (canonicalShiftCycle s hs hsum 1 : E) *
        (finiteRowShift s (canonicalShiftCycle s hs hsum (n + 1)) *
          (s (w 0) * finiteJointWord s s (n + 1) (Fin.tail w)))
    rw [← mul_assoc (finiteRowShift s _), finiteRowShift_mul_row 1 s hs _ (mul_one _),
      mul_assoc (s (w 0)), canonicalShiftCycle_mul_word, finiteJointWord_right_cycle]
    change s (w (Fin.last (n + 2))) *
        (s ((Fin.init w) 0) * finiteJointWord s s n (Fin.tail (Fin.init w))) =
      (canonicalShiftCycle s hs hsum 1 : E) *
        (s (w 0) * (s ((Fin.tail w) (Fin.last (n + 1))) *
          finiteJointWord s s n (Fin.init (Fin.tail w))))
    rw [← mul_assoc (s (w 0)), ← mul_assoc (canonicalShiftCycle s hs hsum 1 : E),
      canonicalShiftCycle_one_mul, Fin.tail_init_eq_init_tail, mul_assoc]
    rfl

lemma canonicalShiftCycle_eq_cocycle (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) (n : ℕ) :
    canonicalShiftCycle s hs hsum n =
      finiteGroupCocycle
        (binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
          (by simpa using hs 1 1) (by simpa using hs 0 1))
        (canonicalShiftCycle s hs hsum 1) n := by
  induction n with
  | zero => exact canonicalShiftCycle_zero s hs hsum
  | succ n ih => rw [canonicalShiftCycle_succ, ih]; rfl

/-- The two affine reflection paths stay inside the balanced word algebra,
so a single-row cyclic partition controls every point of the path. -/
lemma canonicalShiftCycle_control {N : ℕ} (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (e : ZMod N → E) (he : ∀ j, star (e j) = e j)
    (η : ℝ) (hη : 0 ≤ η)
    (hS : ∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ ≤ η) (n : ℕ) :
    ∃ p : Path (1 : unitary E) (canonicalShiftCycle s hs hsum n),
      ClockPathControl p e (2 * Real.pi) 0
        (2 * (Fintype.card (Fin (n + 1) → Fin 2) : ℝ) * (5 * (((n : ℝ) + 1) * η))) := by
  let r := finiteJointWord s s n
  have hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0 :=
    finiteJointWord_gram 1 s s (by simp) (by simp) hs hs hsum hsum n
  have hrs : (∑ i, r i * star (r i)) = 1 :=
    finiteJointWord_sum 1 s s (by simp) (by simp) hs hsum hsum n
  let σ : Equiv.Perm (Fin (n + 1) → Fin 2) := finiteCoordinateReflection (n + 1) 0
  let τ : Equiv.Perm (Fin (n + 1) → Fin 2) := finiteCoordinateReflection (n + 1) 1
  have hσσ : σ * σ = 1 := finiteCoordinateReflection_sq (n + 1) 0
  have hττ : τ * τ = 1 := finiteCoordinateReflection_sq (n + 1) 1
  have hσ : σ⁻¹ = σ := by
    calc
      σ⁻¹ = σ⁻¹ * (σ * σ) := by rw [hσσ, mul_one]
      _ = σ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hτ : τ⁻¹ = τ := by
    calc
      τ⁻¹ = τ⁻¹ * (τ * τ) := by rw [hττ, mul_one]
      _ = τ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  let a := finiteRowPermutationUnitary 1 r (by simp) (by simp) hr hrs σ
  let b := finiteRowPermutationUnitary 1 r (by simp) (by simp) hr hrs τ
  have ha : star (a : E) = (a : E) :=
    finiteRowPermutationUnitary_involution 1 r (by simp) (by simp) hr hrs _
      (finiteCoordinateReflection_sq (n + 1) 0)
  have hb : star (b : E) = (b : E) :=
    finiteRowPermutationUnitary_involution 1 r (by simp) (by simp) hr hrs _
      (finiteCoordinateReflection_sq (n + 1) 1)
  have hc : canonicalShiftCycle s hs hsum n = b * a := by
    let c : Equiv.Perm (Fin (n + 1) → Fin 2) := finiteCoordinateCycle (n + 1)
    have hfac : c = σ * τ := finiteCoordinateCycle_factor (n + 1)
    have hfactor : c⁻¹ = τ * σ := by rw [hfac, mul_inv_rev, hσ, hτ]
    have hh := congrArg
      (fun π : Equiv.Perm (Fin (n + 1) → Fin 2) =>
        finiteRowPermutationUnitary 1 r (by simp) (by simp) hr hrs π) hfactor
    exact hh.trans (finiteRowPermutationUnitary_mul 1 r (by simp) (by simp) hr hrs τ σ)
  let H := (Fintype.card (Fin (n + 1) → Fin 2) : ℝ) * (5 * (((n : ℝ) + 1) * η))
  have hcomm (ρ : Equiv.Perm (Fin (n + 1) → Fin 2)) (j : ZMod N) :
      ‖(finiteRowPermutationUnitary 1 r (by simp) (by simp) hr hrs ρ : E) * e j -
        e j * (finiteRowPermutationUnitary 1 r (by simp) (by simp) hr hrs ρ : E)‖ ≤ H := by
    change ‖(finiteRowPermutation r ρ + (1 - 1)) * e j -
      e j * (finiteRowPermutation r ρ + (1 - 1))‖ ≤ H
    simpa only [sub_self, add_zero] using
      finiteJointPermutation_commutator_le s s hs hs e he η hη hS hS n ρ j
  have hpa : ClockPathControl (affineReflectionPath a ha) e Real.pi 0 H := by
    constructor
    · intro x y
      simpa only [add_zero] using affineReflectionPath_sub_norm_le a ha x y
    · intro x j
      exact (affineReflectionPath_commutator_bound a ha x (e j)).trans (hcomm σ j)
  have hpb : ClockPathControl (affineReflectionPath b hb) e Real.pi 0 H := by
    constructor
    · intro x y
      simpa only [add_zero] using affineReflectionPath_sub_norm_le b hb x y
    · intro x j
      exact (affineReflectionPath_commutator_bound b hb x (e j)).trans (hcomm τ j)
  refine ⟨((affineReflectionPath b hb).mul (affineReflectionPath a ha)).cast (by simp) hc, ?_⟩
  simpa only [H, add_zero, show Real.pi + Real.pi = 2 * Real.pi by ring,
    show 2 * (Fintype.card (Fin (n + 1) → Fin 2) : ℝ) *
        (5 * (((n : ℝ) + 1) * η)) =
      (Fintype.card (Fin (n + 1) → Fin 2) : ℝ) * (5 * (((n : ℝ) + 1) * η)) +
      (Fintype.card (Fin (n + 1) → Fin 2) : ℝ) * (5 * (((n : ℝ) + 1) * η)) by ring]
    using (hpb.mul hpa).cast (by simp) hc

private def canonicalShiftCost (n : ℕ) : ℝ :=
  2 * (Fintype.card (Fin (n + 1) → Fin 2) : ℝ) * (5 * ((n : ℝ) + 1))

private lemma canonicalShiftCost_nonneg (n : ℕ) : 0 ≤ canonicalShiftCost n := by
  unfold canonicalShiftCost
  positivity

/-- All finite cocycle paths use one actual cyclic partition. The height
and finite family bound are chosen before the partition accuracy. -/
lemma exists_canonicalShift_cocycle_family [Nontrivial E]
    (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (m N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    let α := binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
      (by simpa using hs 1 1) (by simpa using hs 0 1)
    ∃ e : ZMod (2 ^ m) → E,
      (∀ j, IsStarProjection (e j)) ∧ (∑ j, e j) = 1 ∧
      (∀ j k, j ≠ k → e j * e k = 0) ∧
      (∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ < ε) ∧
      ∀ n, n ≤ N → ∃ p : Path (finiteGroupCocycle α (canonicalShiftCycle s hs hsum 1) n) 1,
        ClockPathControl p e (2 * Real.pi) 0 ε := by
  intro α
  let B : ℝ := 1 + ∑ k : Fin (N + 1), canonicalShiftCost k
  have hB1 : 1 ≤ B := by
    have hsum0 := Finset.sum_nonneg (s := Finset.univ)
      (fun (k : Fin (N + 1)) _ => canonicalShiftCost_nonneg k)
    dsimp only [B]
    linarith
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  let η := ε / B
  have hη : 0 < η := div_pos hε hB
  have hηε : η ≤ ε := by
    apply (div_le_iff₀ hB).mpr
    nlinarith
  let : IsClosed (((⊤ : StarSubalgebra ℂ E)) : Set E) := by
    change IsClosed (Set.univ : Set E)
    exact isClosed_univ
  obtain ⟨e, _hemem, he, hes, heo, hshift⟩ :=
    exists_binary_cyclic_partition_in (⊤ : StarSubalgebra ℂ E) s hs hsum
      (fun _ => by trivial) m η hη
  refine ⟨e, he, hes, heo, fun j => (hshift j).trans_le hηε, ?_⟩
  intro n hn
  obtain ⟨p, hp⟩ := canonicalShiftCycle_control s hs hsum e
    (fun j => (he j).isSelfAdjoint.star_eq) η hη.le (fun j => (hshift j).le) n
  have hcost : canonicalShiftCost n ≤ B := by
    have hsingle := Finset.single_le_sum
      (fun (i : Fin (N + 1)) _ => canonicalShiftCost_nonneg i)
      (Finset.mem_univ (⟨n, by omega⟩ : Fin (N + 1)))
    change canonicalShiftCost n ≤ 1 + ∑ k : Fin (N + 1), canonicalShiftCost k
    linarith
  have hbound : 2 * (Fintype.card (Fin (n + 1) → Fin 2) : ℝ) *
      (5 * (((n : ℝ) + 1) * η)) ≤ ε := by
    calc
      _ = canonicalShiftCost n * η := by unfold canonicalShiftCost; ring
      _ ≤ B * η := mul_le_mul_of_nonneg_right hcost hη.le
      _ = ε := by dsimp only [η]; field_simp
  refine ⟨p.symm.cast (canonicalShiftCycle_eq_cocycle s hs hsum n).symm rfl, ?_⟩
  exact (hp.symm.mono le_rfl le_rfl hbound).cast
    (canonicalShiftCycle_eq_cocycle s hs hsum n).symm rfl

/-- The actual canonical-shift cocycle has a connected approximate
coboundary; its only height-dependent error is the finite mesh term. -/
lemma exists_canonicalShift_coboundary_at_height [Nontrivial E]
    (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      ‖(canonicalShiftCycle s hs hsum 1 : E) * finiteRowShift s u - u‖ ≤
        (2 * Real.pi) * Real.sqrt (2 ^ m : ℕ) / (2 ^ m : ℕ) + ε := by
  classical
  let N := 2 ^ m
  have hN : 0 < N := by dsimp only [N]; positivity
  let : NeZero N := ⟨hN.ne'⟩
  let φ := finiteCuntzDiagonalHom s hs
  let α := binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
    (by simpa using hs 1 1) (by simpa using hs 0 1)
  let w := canonicalShiftCycle s hs hsum 1
  have hco (u : unitary E) : (α u : E) = φ u := binarySplitHom_coe s hs hsum u
  have hcont : Continuous α := by
    exact (binaryCornerUnitary_continuous (s 0) (by simpa using hs 0 0)).mul
      (binaryCornerUnitary_continuous (s 1) (by simpa using hs 1 1))
  have hα (u v : unitary E) : ‖(α u : E) - α v‖ ≤ ‖(u : E) - v‖ :=
    binarySplitHom_sub_norm_le s hs hsum u v
  obtain ⟨δ, hδ, hp⟩ := exists_connected_rohlin_polar_tolerance (E := E)
    (I := ZMod N) (ε / 4) (by positivity)
  let D : ℝ := Real.sqrt N + N + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  let η := min (δ / (4 * ((N : ℝ) + 1))) (ε / (4 * D))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hsmall : 2 * η + 2 * N * η ≤ δ := by
    have hl : η ≤ δ / (4 * ((N : ℝ) + 1)) := min_le_left _ _
    have hb := (le_div_iff₀ (show 0 < 4 * ((N : ℝ) + 1) by positivity)).mp hl
    nlinarith
  have herr : (Real.sqrt N + N) * η ≤ ε / 4 := by
    have hl : η ≤ ε / (4 * D) := min_le_right _ _
    have hb := (le_div_iff₀ (show 0 < 4 * D by positivity)).mp hl
    dsimp only [D] at hb
    nlinarith [hη.le]
  obtain ⟨e, he, hes, heo, hS, hpaths⟩ :=
    exists_canonicalShift_cocycle_family s hs hsum m N η hη
  choose r hr using hpaths
  obtain ⟨u, hu, hb⟩ := connected_rohlin_cocycle_of_family hN φ α hco hcont hα w e
    he heo (2 * Real.pi) 0 η η (ε / 4) δ (by positivity) le_rfl
    (fun k => (hS k).le) r hr hsmall (hp e he hes heo)
  refine ⟨u, hu, hb.trans ?_⟩
  calc
    2 * (ε / 4) + Real.sqrt N * (2 * Real.pi / N + 0) + N * η =
        (2 * Real.pi) * Real.sqrt N / N + 2 * (ε / 4) + N * η := by ring
    _ ≤ (2 * Real.pi) * Real.sqrt N / N + ε := by
      have hh : N * η ≤ (Real.sqrt N + N) * η := by
        nlinarith [Real.sqrt_nonneg (N : ℝ), hη.le]
      linarith

/-- The canonical binary endomorphism is approximately inner through
unitaries connected to one, on its actual two generating isometries. -/
lemma exists_connected_canonicalShift_conjugacy [Nontrivial E]
    (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      ∀ i, ‖(u : E) * s i * star (u : E) - finiteRowShift s (s i)‖ < ε := by
  let L := 2 * Real.pi
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (4 * L / ε) (show (1 : ℝ) < 2 by norm_num)
  have ha : 0 < (2 : ℝ) ^ k := by positivity
  have hpow : ((2 ^ (2 * k) : ℕ) : ℝ) = ((2 : ℝ) ^ k) ^ 2 := by
    push_cast
    rw [Nat.mul_comm 2 k, pow_mul]
  have hsqrt : Real.sqrt ((2 ^ (2 * k) : ℕ) : ℝ) = (2 : ℝ) ^ k := by
    rw [hpow, Real.sqrt_sq ha.le]
  have hratio : L * Real.sqrt ((2 ^ (2 * k) : ℕ) : ℝ) /
      ((2 ^ (2 * k) : ℕ) : ℝ) < ε / 4 := by
    rw [hsqrt, hpow]
    have hid : L * (2 : ℝ) ^ k / ((2 : ℝ) ^ k) ^ 2 = L / (2 : ℝ) ^ k := by
      field_simp
    rw [hid]
    apply (div_lt_iff₀ ha).mpr
    have hh := (div_lt_iff₀ hε).mp hk
    nlinarith
  obtain ⟨u, hu, hb⟩ := exists_canonicalShift_coboundary_at_height s hs hsum
    (2 * k) (ε / 2) (half_pos hε)
  have herr : ‖(canonicalShiftCycle s hs hsum 1 : E) * finiteRowShift s u - u‖ < ε := by
    apply hb.trans_lt
    change L * Real.sqrt ((2 ^ (2 * k) : ℕ) : ℝ) /
      ((2 ^ (2 * k) : ℕ) : ℝ) + ε / 2 < ε
    linarith
  have hinter (i : Fin 2) :
      ‖(u : E) * s i - finiteRowShift s (s i) * (u : E)‖ < ε := by
    have hid : finiteRowShift s (s i) * (u : E) - (u : E) * s i =
        ((canonicalShiftCycle s hs hsum 1 : E) * finiteRowShift s u - u) * s i := by
      rw [sub_mul, mul_assoc, finiteRowShift_mul_row 1 s hs (u : E) (mul_one _) i,
        ← mul_assoc, canonicalShiftCycle_one_generator]
    have hsi : ‖s i‖ ≤ 1 := by
      have hh := congrArg norm (show star (s i) * s i = 1 by simpa using hs i i)
      rw [CStarRing.norm_star_mul_self, norm_one] at hh
      nlinarith [norm_nonneg (s i)]
    rw [norm_sub_rev, hid]
    exact (norm_mul_le _ _).trans_lt
      ((mul_le_mul_of_nonneg_left hsi (norm_nonneg _)).trans_lt (by simpa using herr))
  refine ⟨u, hu, fun i => ?_⟩
  calc
    _ = ‖((u : E) * s i - finiteRowShift s (s i) * (u : E)) *
        (star u : unitary E)‖ := by
      congr 1
      change (u : E) * s i * star (u : E) - finiteRowShift s (s i) =
        ((u : E) * s i - finiteRowShift s (s i) * (u : E)) * star (u : E)
      rw [sub_mul, mul_assoc (finiteRowShift s (s i)), u.property.2, mul_one]
    _ = ‖(u : E) * s i - finiteRowShift s (s i) * (u : E)‖ :=
      CStarRing.norm_mul_coe_unitary _ _
    _ < ε := hinter i

end WeakPureInfiniteness

end

end OAI
