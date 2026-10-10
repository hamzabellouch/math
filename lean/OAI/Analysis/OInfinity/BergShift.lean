import OAI.Analysis.OInfinity.BergSeam

namespace OAI

/-! # Finite Berg smoothing along a Cuntz corner shift

A finite family of orthogonal corner rotations can have a large angle in the
middle and zero angles at both ends. The commutator with a row generator is
controlled by adjacent angle differences. The unitary and connectedness
assertions are proved for the finite construction. Matching a terminal corner
between the two different tensor-factor rows is still a separate obligation.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- Adjoin the complementary identity to a nonunital corner map. -/
def bergCornerLift (φ : E →⋆ₙₐ[ℂ] E) (x : E) : E := 1 - φ 1 + φ x

private lemma bergCornerMap_real_smul (φ : E →⋆ₙₐ[ℂ] E) (r : ℝ) (x : E) :
    φ (r • x) = r • φ x := by
  rw [← Complex.coe_smul r x, map_smul, Complex.coe_smul]

lemma bergCornerMap_rotation_deviation (φ : E →⋆ₙₐ[ℂ] E) (a : E) (θ : ℝ) :
    φ (partialIsometryBergRotation a θ - 1) =
      partialIsometryBergRotation (φ a) θ - 1 := by
  have hs : φ (bergSupport a) = bergSupport (φ a) := by
    simp only [bergSupport, map_add, map_mul, map_star]
  have hk : φ (bergSkew a) = bergSkew (φ a) := by
    simp only [bergSkew, map_sub, map_star]
  simp only [partialIsometryBergRotation, bergRotationCore, map_sub, map_add,
    bergCornerMap_real_smul, hs, hk]
  abel

lemma bergCornerLift_finiteRotation {J : Type*} (φ : E →⋆ₙₐ[ℂ] E)
    (a : J → E) (S : Finset J) (θ : J → ℝ) :
    bergCornerLift φ (bergFiniteRotation a S θ) =
      bergFiniteRotation (fun j => φ (a j)) S θ := by
  simp only [bergCornerLift, bergFiniteRotation, map_add, map_sum,
    bergCornerMap_rotation_deviation]
  abel

/-- Angles shifted by one layer, with a zero at the new bottom. -/
def bergShiftAngles (θ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => θ k

@[simp] lemma bergShiftAngles_zero (θ : ℕ → ℝ) : bergShiftAngles θ 0 = 0 := rfl
@[simp] lemma bergShiftAngles_succ (θ : ℕ → ℝ) (k : ℕ) :
    bergShiftAngles θ (k + 1) = θ k := rfl

lemma bergFiniteRotation_pad_zero (a : ℕ → E) (θ : ℕ → ℝ) (N : ℕ)
    (hθ : θ N = 0) :
    bergFiniteRotation a (Finset.range (N + 1)) θ =
      bergFiniteRotation a (Finset.range N) θ := by
  simp only [bergFiniteRotation, Finset.sum_range_succ, hθ,
    partialIsometryBergRotation_zero, sub_self, add_zero]

lemma bergCornerLift_shift (φ : E →⋆ₙₐ[ℂ] E) (a : ℕ → E)
    (hshift : ∀ k, φ (a k) = a (k + 1)) (θ : ℕ → ℝ) (N : ℕ) :
    bergCornerLift φ (bergFiniteRotation a (Finset.range N) θ) =
      bergFiniteRotation a (Finset.range (N + 1)) (bergShiftAngles θ) := by
  rw [bergCornerLift_finiteRotation]
  simp only [bergFiniteRotation, Finset.sum_range_succ', bergShiftAngles_succ,
    bergShiftAngles_zero, partialIsometryBergRotation_zero, sub_self, add_zero, hshift]

/-- Vanishing endpoint angles leave only adjacent angular changes at the seam. -/
lemma bergFiniteRotation_shift_norm_le (φ : E →⋆ₙₐ[ℂ] E) (a : ℕ → E)
    (hshift : ∀ k, φ (a k) = a (k + 1)) (θ : ℕ → ℝ) (N : ℕ)
    (ha : ∀ k < N + 2, a k * star (a k) * a k = a k)
    (haa : ∀ k < N + 2, a k * a k = 0)
    (horth : ∀ i < N + 2, ∀ j < N + 2, i ≠ j →
      bergSupport (a i) * bergSupport (a j) = 0)
    (hzero : θ 0 = 0) (hend : θ (N + 1) = 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hstep : ∀ k ≤ N, |θ (k + 1) - θ k| ≤ δ) :
    ‖bergFiniteRotation a (Finset.range (N + 1)) θ -
      bergCornerLift φ (bergFiniteRotation a (Finset.range (N + 1)) θ)‖ ≤ 2 * δ := by
  rw [bergCornerLift_shift φ a hshift θ (N + 1),
    ← bergFiniteRotation_pad_zero a θ (N + 1) hend]
  apply bergFiniteRotation_sub_norm_le a (Finset.range (N + 2)) θ (bergShiftAngles θ)
    (fun k hk => ha k (Finset.mem_range.mp hk))
    (fun k hk => haa k (Finset.mem_range.mp hk))
    (fun i hi j hj hne => horth i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hne)
    δ hδ
  intro k hk
  cases k with
  | zero => simpa only [bergShiftAngles_zero, hzero, sub_self, abs_zero] using hδ
  | succ k =>
    rw [bergShiftAngles_succ]
    exact hstep k (by have := Finset.mem_range.mp hk; omega)

/-- Every finite orthogonal rotation lies in the identity component. -/
lemma bergFiniteRotation_joined {J : Type*} (a : J → E) (S : Finset J) (θ : J → ℝ)
    (ha : ∀ j ∈ S, a j * star (a j) * a j = a j)
    (haa : ∀ j ∈ S, a j * a j = 0)
    (horth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → bergSupport (a i) * bergSupport (a j) = 0) :
    Joined (1 : unitary E)
      ⟨bergFiniteRotation a S θ, bergFiniteRotation_mem a S θ ha haa horth⟩ := by
  let f (t : unitInterval) : unitary E :=
    ⟨bergFiniteRotation a S (fun j => (t : ℝ) * θ j),
      bergFiniteRotation_mem a S (fun j => (t : ℝ) * θ j) ha haa horth⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    change Continuous (fun t : unitInterval =>
      1 + ∑ j ∈ S, (partialIsometryBergRotation (a j) ((t : ℝ) * θ j) - 1))
    apply continuous_const.add
    apply continuous_finsetSum
    intro j hj
    exact ((partialIsometryBergRotation_continuous (a j)).comp
      (continuous_subtype_val.mul continuous_const)).sub continuous_const
  refine ⟨{ toContinuousMap := ⟨f, hf⟩, source' := ?_, target' := ?_ }⟩
  · apply Subtype.ext
    change bergFiniteRotation a S (fun j => ((0 : unitInterval) : ℝ) * θ j) = 1
    simp [bergFiniteRotation]
  · apply Subtype.ext
    change bergFiniteRotation a S (fun j => ((1 : unitInterval) : ℝ) * θ j) =
      bergFiniteRotation a S θ
    simp

/-- Iteration as an actual nonunital star homomorphism. -/
def bergCornerIterHom (φ : E →⋆ₙₐ[ℂ] E) : ℕ → E →⋆ₙₐ[ℂ] E
  | 0 => NonUnitalStarAlgHom.id ℂ E
  | n + 1 => φ.comp (bergCornerIterHom φ n)

@[simp] lemma bergCornerIterHom_zero (φ : E →⋆ₙₐ[ℂ] E) (x : E) :
    bergCornerIterHom φ 0 x = x := rfl

@[simp] lemma bergCornerIterHom_succ (φ : E →⋆ₙₐ[ℂ] E) (n : ℕ) (x : E) :
    bergCornerIterHom φ (n + 1) x = φ (bergCornerIterHom φ n x) := rfl

lemma bergCornerIterHom_layer_zero (φ : E →⋆ₙₐ[ℂ] E) (n : ℕ) :
    bergCornerIterHom φ n (bergTowerLayer φ 0) = bergTowerLayer φ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bergCornerIterHom_succ, ih, bergTowerLayer_map]

lemma bergCornerIterHom_support (φ : E →⋆ₙₐ[ℂ] E) (n : ℕ) (a : E) :
    bergCornerIterHom φ n (bergSupport a) = bergSupport (bergCornerIterHom φ n a) := by
  simp only [bergSupport, map_add, map_mul, map_star]

lemma bergCornerIterHom_partial (φ : E →⋆ₙₐ[ℂ] E) (a : E)
    (ha : a * star a * a = a) (n : ℕ) :
    bergCornerIterHom φ n a * star (bergCornerIterHom φ n a) *
      bergCornerIterHom φ n a = bergCornerIterHom φ n a := by
  simpa only [map_mul, map_star] using congrArg (bergCornerIterHom φ n) ha

lemma bergCornerIterHom_square_zero (φ : E →⋆ₙₐ[ℂ] E) (a : E)
    (haa : a * a = 0) (n : ℕ) :
    bergCornerIterHom φ n a * bergCornerIterHom φ n a = 0 := by
  simpa only [map_mul, map_zero] using congrArg (bergCornerIterHom φ n) haa

/-- A rotation supported in the bottom layer has disjoint iterated corners. -/
lemma bergCornerIterHom_orthogonal (φ : E →⋆ₙₐ[ℂ] E) (a : E)
    (hsupport : bergSupport a * bergTowerLayer φ 0 = bergSupport a)
    {n m : ℕ} (hne : n ≠ m) :
    bergSupport (bergCornerIterHom φ n a) * bergSupport (bergCornerIterHom φ m a) = 0 := by
  have hright (k : ℕ) : bergSupport (bergCornerIterHom φ k a) * bergTowerLayer φ k =
      bergSupport (bergCornerIterHom φ k a) := by
    simpa only [map_mul, bergCornerIterHom_support, bergCornerIterHom_layer_zero] using
      congrArg (bergCornerIterHom φ k) hsupport
  have hleft (k : ℕ) : bergTowerLayer φ k * bergSupport (bergCornerIterHom φ k a) =
      bergSupport (bergCornerIterHom φ k a) := by
    simpa only [star_mul, bergSupport_star, bergTowerLayer_star] using congrArg star (hright k)
  calc
    _ = (bergSupport (bergCornerIterHom φ n a) * bergTowerLayer φ n) *
        (bergTowerLayer φ m * bergSupport (bergCornerIterHom φ m a)) := by
      rw [hright n, hleft m]
    _ = bergSupport (bergCornerIterHom φ n a) *
        (bergTowerLayer φ n * bergTowerLayer φ m) *
          bergSupport (bergCornerIterHom φ m a) := by noncomm_ring
    _ = 0 := by rw [bergTowerLayer_mul_of_ne φ hne, mul_zero, zero_mul]

private lemma bergSupport_mul_star (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) :
    bergSupport a * star a = star a := by
  have hss : star a * star a = 0 := by
    simpa only [star_mul, star_zero] using congrArg star haa
  have hstar : star a * a * star a = star a := by
    simpa only [star_mul, star_star, mul_assoc] using congrArg star ha
  calc
    _ = (star a * a * star a) + a * (star a * star a) := by
      unfold bergSupport
      noncomm_ring
    _ = star a := by rw [hstar, hss, mul_zero, add_zero]

/-- At a quarter-turn peak, the assembled finite rotation transports the
specified initial corner exactly. Other tower levels do not affect it. -/
lemma bergFiniteRotation_quarter_mul_initial {J : Type*} (a : J → E) (S : Finset J)
    (θ : J → ℝ) (j : J) (hj : j ∈ S) (hθj : θ j = Real.pi / 2)
    (ha : ∀ k ∈ S, a k * star (a k) * a k = a k)
    (haa : ∀ k ∈ S, a k * a k = 0)
    (horth : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → bergSupport (a k) * bergSupport (a l) = 0) :
    bergFiniteRotation a S θ * (star (a j) * a j) = a j := by
  classical
  have hp : bergSupport (a j) * (star (a j) * a j) = star (a j) * a j := by
    rw [← mul_assoc, bergSupport_mul_star (a j) (ha j hj) (haa j hj)]
  have hz (k : J) (hk : k ∈ S) (hkj : k ≠ j) :
      (partialIsometryBergRotation (a k) (θ k) - 1) * (star (a j) * a j) = 0 := by
    have hd := (bergRotationDeviation_support (a k) (ha k hk) (haa k hk) (θ k)).2
    calc
      _ = ((partialIsometryBergRotation (a k) (θ k) - 1) * bergSupport (a k)) *
          (bergSupport (a j) * (star (a j) * a j)) := by rw [hd, hp]
      _ = (partialIsometryBergRotation (a k) (θ k) - 1) *
          (bergSupport (a k) * bergSupport (a j)) * (star (a j) * a j) := by noncomm_ring
      _ = 0 := by rw [horth k hk j hj hkj, mul_zero, zero_mul]
  unfold bergFiniteRotation
  rw [add_mul, one_mul, Finset.sum_mul, Finset.sum_eq_single j]
  · rw [sub_mul, one_mul, hθj,
      partialIsometryBergRotation_quarter_mul_initial (a j) (ha j hj) (haa j hj)]
    abel
  · intro k hk hkj
    exact hz k hk hkj
  · intro hnot
    exact (hnot hj).elim

section Row

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma bergCornerLift_mul_generator (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (x : E) (i : I) :
    bergCornerLift (finiteCuntzDiagonalHom s hs) x * s i = s i * x := by
  change (1 - finiteCuntzTransfer s s 1 + finiteCuntzTransfer s s x) * s i = _
  rw [add_mul, sub_mul, one_mul, finiteCuntzTransfer_mul s s hs,
    finiteCuntzTransfer_mul s s hs, mul_one, sub_self, zero_add]

lemma bergFiniteRotation_commutator_norm_le (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsnorm : ∀ i, ‖s i‖ ≤ 1) (a : ℕ → E)
    (hshift : ∀ k, finiteCuntzDiagonalHom s hs (a k) = a (k + 1))
    (θ : ℕ → ℝ) (N : ℕ)
    (ha : ∀ k < N + 2, a k * star (a k) * a k = a k)
    (haa : ∀ k < N + 2, a k * a k = 0)
    (horth : ∀ i < N + 2, ∀ j < N + 2, i ≠ j →
      bergSupport (a i) * bergSupport (a j) = 0)
    (hzero : θ 0 = 0) (hend : θ (N + 1) = 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hstep : ∀ k ≤ N, |θ (k + 1) - θ k| ≤ δ) (i : I) :
    ‖bergFiniteRotation a (Finset.range (N + 1)) θ * s i -
      s i * bergFiniteRotation a (Finset.range (N + 1)) θ‖ ≤ 2 * δ := by
  rw [← bergCornerLift_mul_generator s hs _ i, ← sub_mul]
  calc
    _ ≤ ‖bergFiniteRotation a (Finset.range (N + 1)) θ -
        bergCornerLift (finiteCuntzDiagonalHom s hs)
          (bergFiniteRotation a (Finset.range (N + 1)) θ)‖ * ‖s i‖ := norm_mul_le _ _
    _ ≤ (2 * δ) * 1 := mul_le_mul
      (bergFiniteRotation_shift_norm_le _ a hshift θ N ha haa horth hzero hend δ hδ hstep)
      (hsnorm i) (norm_nonneg _) (by positivity)
    _ = 2 * δ := mul_one _

/-- The canonical iterates of a bottom-supported corner satisfy the finite
Berg commutator estimate for every generator in the row. -/
lemma bergIteratedRotation_commutator_norm_le (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsnorm : ∀ i, ‖s i‖ ≤ 1) (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0)
    (hsupport : bergSupport a * bergTowerLayer (finiteCuntzDiagonalHom s hs) 0 = bergSupport a)
    (θ : ℕ → ℝ) (N : ℕ) (hzero : θ 0 = 0) (hend : θ (N + 1) = 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hstep : ∀ k ≤ N, |θ (k + 1) - θ k| ≤ δ) (i : I) :
    let b := fun k => bergCornerIterHom (finiteCuntzDiagonalHom s hs) k a
    ‖bergFiniteRotation b (Finset.range (N + 1)) θ * s i -
      s i * bergFiniteRotation b (Finset.range (N + 1)) θ‖ ≤ 2 * δ := by
  apply bergFiniteRotation_commutator_norm_le s hs hsnorm _ (fun _ => rfl) θ N
  · intro k hk
    exact bergCornerIterHom_partial _ a ha k
  · intro k hk
    exact bergCornerIterHom_square_zero _ a haa k
  · intro k hk l hl hkl
    exact bergCornerIterHom_orthogonal _ a hsupport hkl
  · exact hzero
  · exact hend
  · exact hδ
  · exact hstep

/-- A smoothed finite tower transports its peak corner by an actual connected
unitary and nearly commutes with every row generator. -/
lemma exists_connected_berg_rotation (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsnorm : ∀ i, ‖s i‖ ≤ 1) (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0)
    (hsupport : bergSupport a * bergTowerLayer (finiteCuntzDiagonalHom s hs) 0 = bergSupport a)
    (θ : ℕ → ℝ) (N K : ℕ) (hK : K < N + 1) (hpeak : θ K = Real.pi / 2)
    (hzero : θ 0 = 0) (hend : θ (N + 1) = 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hstep : ∀ k ≤ N, |θ (k + 1) - θ k| ≤ δ) :
    let b := fun k => bergCornerIterHom (finiteCuntzDiagonalHom s hs) k a
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (u : E) * (star (b K) * b K) = b K ∧
      ∀ i, ‖(u : E) * s i - s i * (u : E)‖ ≤ 2 * δ := by
  dsimp only
  let b := fun k => bergCornerIterHom (finiteCuntzDiagonalHom s hs) k a
  have hb (k : ℕ) : b k * star (b k) * b k = b k :=
    bergCornerIterHom_partial _ a ha k
  have hbb (k : ℕ) : b k * b k = 0 := bergCornerIterHom_square_zero _ a haa k
  have ho {k l : ℕ} (hkl : k ≠ l) : bergSupport (b k) * bergSupport (b l) = 0 :=
    bergCornerIterHom_orthogonal _ a hsupport hkl
  let u : unitary E := ⟨bergFiniteRotation b (Finset.range (N + 1)) θ,
    bergFiniteRotation_mem b _ θ (fun k _ => hb k) (fun k _ => hbb k)
      (fun _ _ _ _ hkl => ho hkl)⟩
  refine ⟨u, bergFiniteRotation_joined b _ θ (fun k _ => hb k) (fun k _ => hbb k)
    (fun _ _ _ _ hkl => ho hkl), ?_, ?_⟩
  · exact bergFiniteRotation_quarter_mul_initial b _ θ K (Finset.mem_range.mpr hK) hpeak
      (fun k _ => hb k) (fun k _ => hbb k) (fun _ _ _ _ hkl => ho hkl)
  · exact bergIteratedRotation_commutator_norm_le s hs hsnorm a ha haa hsupport
      θ N hzero hend δ hδ hstep

end Row

end WeakPureInfiniteness

end

end OAI
