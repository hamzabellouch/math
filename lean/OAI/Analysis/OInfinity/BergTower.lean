import OAI.Analysis.OInfinity.HalfFlipRecursion
import OAI.Analysis.OInfinity.BergRotation

namespace OAI

/-! # Finite orthogonal towers and their terminal corner

The layers of a nonunital corner endomorphism form an exact finite orthogonal
partition together with the last tail projection. For a Cuntz row, multiplication
by each generator shifts these layers. The tail remains explicit throughout;
there is no assertion that its norm becomes small as the height grows.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- The range projection of the `n`th iterate of the corner map. -/
def bergTowerTail (φ : E →⋆ₙₐ[ℂ] E) : ℕ → E
  | 0 => 1
  | n + 1 => φ (bergTowerTail φ n)

@[simp] lemma bergTowerTail_zero (φ : E →⋆ₙₐ[ℂ] E) : bergTowerTail φ 0 = 1 := rfl

@[simp] lemma bergTowerTail_succ (φ : E →⋆ₙₐ[ℂ] E) (n : ℕ) :
    bergTowerTail φ (n + 1) = φ (bergTowerTail φ n) := rfl

lemma bergTowerTail_star (φ : E →⋆ₙₐ[ℂ] E) (n : ℕ) :
    star (bergTowerTail φ n) = bergTowerTail φ n := by
  induction n with
  | zero => simp only [bergTowerTail_zero, star_one]
  | succ n ih => rw [bergTowerTail_succ, ← map_star, ih]

lemma bergTowerTail_mul_of_le (φ : E →⋆ₙₐ[ℂ] E) {n m : ℕ} (h : n ≤ m) :
    bergTowerTail φ n * bergTowerTail φ m = bergTowerTail φ m := by
  induction n generalizing m with
  | zero => simp only [bergTowerTail_zero, one_mul]
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      simp only [bergTowerTail_succ]
      rw [← map_mul, ih (Nat.le_of_succ_le_succ h)]

lemma bergTowerTail_mul_of_ge (φ : E →⋆ₙₐ[ℂ] E) {n m : ℕ} (h : m ≤ n) :
    bergTowerTail φ n * bergTowerTail φ m = bergTowerTail φ n := by
  have he := congrArg star (bergTowerTail_mul_of_le φ h)
  simpa only [star_mul, bergTowerTail_star] using he

/-- One orthogonal difference of successive range projections. -/
def bergTowerLayer (φ : E →⋆ₙₐ[ℂ] E) (n : ℕ) : E :=
  bergTowerTail φ n - bergTowerTail φ (n + 1)

lemma bergTowerLayer_star (φ : E →⋆ₙₐ[ℂ] E) (n : ℕ) :
    star (bergTowerLayer φ n) = bergTowerLayer φ n := by
  simp only [bergTowerLayer, star_sub, bergTowerTail_star]

lemma bergTowerLayer_sq (φ : E →⋆ₙₐ[ℂ] E) (n : ℕ) :
    bergTowerLayer φ n * bergTowerLayer φ n = bergTowerLayer φ n := by
  unfold bergTowerLayer
  rw [sub_mul, mul_sub, mul_sub,
    bergTowerTail_mul_of_le φ (le_refl n),
    bergTowerTail_mul_of_le φ (Nat.le_succ n),
    bergTowerTail_mul_of_ge φ (Nat.le_succ n),
    bergTowerTail_mul_of_le φ (le_refl (n + 1))]
  abel

lemma bergTowerLayer_mul_tail (φ : E →⋆ₙₐ[ℂ] E) {n m : ℕ} (h : n < m) :
    bergTowerLayer φ n * bergTowerTail φ m = 0 := by
  rw [bergTowerLayer, sub_mul,
    bergTowerTail_mul_of_le φ h.le,
    bergTowerTail_mul_of_le φ (Nat.succ_le_of_lt h), sub_self]

lemma bergTowerTail_mul_layer (φ : E →⋆ₙₐ[ℂ] E) {n m : ℕ} (h : n < m) :
    bergTowerTail φ m * bergTowerLayer φ n = 0 := by
  have he := congrArg star (bergTowerLayer_mul_tail φ h)
  simpa only [star_mul, star_zero, bergTowerTail_star, bergTowerLayer_star] using he

lemma bergTowerLayer_mul_of_lt (φ : E →⋆ₙₐ[ℂ] E) {n m : ℕ} (h : n < m) :
    bergTowerLayer φ n * bergTowerLayer φ m = 0 := by
  change bergTowerLayer φ n *
    (bergTowerTail φ m - bergTowerTail φ (m + 1)) = 0
  rw [mul_sub, bergTowerLayer_mul_tail φ h,
    bergTowerLayer_mul_tail φ (h.trans_le (Nat.le_succ m)), sub_self]

lemma bergTowerLayer_mul_of_ne (φ : E →⋆ₙₐ[ℂ] E) {n m : ℕ} (h : n ≠ m) :
    bergTowerLayer φ n * bergTowerLayer φ m = 0 := by
  rcases lt_or_gt_of_ne h with h | h
  · exact bergTowerLayer_mul_of_lt φ h
  · have he := congrArg star (bergTowerLayer_mul_of_lt φ h)
    simpa only [star_mul, star_zero, bergTowerLayer_star] using he

/-- The final tail is part of the exact partition; it is not discarded. -/
lemma bergTower_finite_partition (φ : E →⋆ₙₐ[ℂ] E) (N : ℕ) :
    (∑ n ∈ Finset.range N, bergTowerLayer φ n) + bergTowerTail φ N = 1 := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, bergTowerTail_zero, zero_add]
  | succ N ih =>
    rw [Finset.sum_range_succ, bergTowerLayer]
    calc
      _ = (∑ n ∈ Finset.range N, bergTowerLayer φ n) + bergTowerTail φ N := by abel
      _ = 1 := ih

lemma bergTowerLayer_map (φ : E →⋆ₙₐ[ℂ] E) (n : ℕ) :
    φ (bergTowerLayer φ n) = bergTowerLayer φ (n + 1) := by
  simp only [bergTowerLayer, map_sub, bergTowerTail_succ]

section CuntzRow

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A row generator shifts the tail projection by one level. -/
lemma bergTowerTail_succ_mul_generator (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n : ℕ) (i : I) :
    bergTowerTail (finiteCuntzDiagonalHom s hs) (n + 1) * s i =
      s i * bergTowerTail (finiteCuntzDiagonalHom s hs) n := by
  change finiteCuntzTransfer s s _ * s i = _
  exact finiteCuntzTransfer_mul s s hs _ i

/-- The finite layers satisfy exact covariance away from the terminal corner. -/
lemma bergTowerLayer_succ_mul_generator (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (n : ℕ) (i : I) :
    bergTowerLayer (finiteCuntzDiagonalHom s hs) (n + 1) * s i =
      s i * bergTowerLayer (finiteCuntzDiagonalHom s hs) n := by
  rw [bergTowerLayer, sub_mul, bergTowerTail_succ_mul_generator s hs n i,
    bergTowerTail_succ_mul_generator s hs (n + 1) i, bergTowerLayer, mul_sub]

lemma bergTowerLayer_zero_mul_generator (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (i : I) :
    bergTowerLayer (finiteCuntzDiagonalHom s hs) 0 * s i = 0 := by
  rw [bergTowerLayer, sub_mul, bergTowerTail_zero, one_mul,
    bergTowerTail_succ_mul_generator s hs 0 i, bergTowerTail_zero, mul_one, sub_self]

/-- Mixed Gram identities retain the coefficient in the corner map. -/
lemma bergTransfer_star_mul (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0) (x y : E) :
    star (finiteCuntzTransfer s t x) * finiteCuntzTransfer s t y =
      finiteCuntzDiagonalHom s hs (star x * y) := by
  change _ = ∑ i, s i * (star x * y) * star (s i)
  simp only [finiteCuntzTransfer, star_sum, star_mul, star_star,
    Finset.sum_mul, Finset.mul_sum]
  have hterm (i j : I) :
      (s i * (star x * star (t i))) * (t j * y * star (s j)) =
        if i = j then s i * (star x * y) * star (s i) else 0 := by
    calc
      _ = s i * star x * (star (t i) * t j) * y * star (s j) := by noncomm_ring
      _ = _ := by
        rw [ht]
        split_ifs with h
        · subst j
          simp only [mul_one, mul_assoc]
        · simp
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma bergTransfer_mul_star (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0) (x y : E) :
    finiteCuntzTransfer s t x * star (finiteCuntzTransfer s t y) =
      finiteCuntzDiagonalHom t ht (x * star y) := by
  simpa only [finiteCuntzTransfer_star, star_star] using
    bergTransfer_star_mul t s ht hs (star x) (star y)

/-- Iteration transfers an initial layer exactly to the corresponding layer. -/
lemma bergTransferIter_layer_source (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (x : E) (hx : star x * x = bergTowerLayer (finiteCuntzDiagonalHom s hs) 0)
    (n : ℕ) :
    star (finiteCuntzTransferIter s t n x) * finiteCuntzTransferIter s t n x =
      bergTowerLayer (finiteCuntzDiagonalHom s hs) n := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [finiteCuntzTransferIter_succ, bergTransfer_star_mul s t hs ht,
      ih, bergTowerLayer_map]

lemma bergTransferIter_layer_target (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (x : E) (hx : x * star x = bergTowerLayer (finiteCuntzDiagonalHom t ht) 0)
    (n : ℕ) :
    finiteCuntzTransferIter s t n x * star (finiteCuntzTransferIter s t n x) =
      bergTowerLayer (finiteCuntzDiagonalHom t ht) n := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [finiteCuntzTransferIter_succ, bergTransfer_mul_star s t hs ht,
      ih, bergTowerLayer_map]

/-- A unitary coefficient fills the whole last tail, not just a dense part. -/
lemma bergTransferIter_tail_source (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (x : unitary E) (n : ℕ) :
    star (finiteCuntzTransferIter s t n (x : E)) *
      finiteCuntzTransferIter s t n (x : E) =
      bergTowerTail (finiteCuntzDiagonalHom s hs) n := by
  induction n with
  | zero => exact x.property.1
  | succ n ih =>
    rw [finiteCuntzTransferIter_succ, bergTransfer_star_mul s t hs ht,
      ih, bergTowerTail_succ]

lemma bergTransferIter_tail_target (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (x : unitary E) (n : ℕ) :
    finiteCuntzTransferIter s t n (x : E) *
      star (finiteCuntzTransferIter s t n (x : E)) =
      bergTowerTail (finiteCuntzDiagonalHom t ht) n := by
  induction n with
  | zero => exact x.property.2
  | succ n ih =>
    rw [finiteCuntzTransferIter_succ, bergTransfer_mul_star s t hs ht,
      ih, bergTowerTail_succ]

/-- The bottom coefficient determined by an exact row extension. -/
def bergBottomCoefficient (s t : I → E) (v : unitary E) : E :=
  (v : E) - finiteCuntzTransfer s t 1

omit [Fintype I] [DecidableEq I] in
lemma bergRowExtension_star (s t : I → E) (v : unitary E)
    (hv : ∀ i, (v : E) * s i = t i) (i : I) :
    star (t i) * (v : E) = star (s i) := by
  calc
    _ = star ((v : E) * s i) * (v : E) := by rw [hv i]
    _ = star (s i) * (star (v : E) * (v : E)) := by rw [star_mul, mul_assoc]
    _ = star (s i) := by rw [v.property.1, mul_one]

lemma bergBottom_mul_generator (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (v : unitary E) (hv : ∀ i, (v : E) * s i = t i) (i : I) :
    bergBottomCoefficient s t v * s i = 0 := by
  rw [bergBottomCoefficient, sub_mul, hv, finiteCuntzTransfer_mul s t hs, mul_one,
    sub_self]

lemma bergBottom_star_generator_mul (s t : I → E)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (v : unitary E) (hv : ∀ i, (v : E) * s i = t i) (i : I) :
    star (t i) * bergBottomCoefficient s t v = 0 := by
  have h := congrArg star (finiteCuntzTransfer_mul t s ht (1 : E) i)
  simp only [star_mul, finiteCuntzTransfer_star, star_one, mul_one] at h
  rw [bergBottomCoefficient, mul_sub, bergRowExtension_star s t v hv, h, sub_self]

omit [DecidableEq I] in
private lemma bergExtension_star_transfer (s t : I → E) (v : unitary E)
    (hv : ∀ i, (v : E) * s i = t i) (x : E) :
    star (v : E) * finiteCuntzTransfer s t x = finiteCuntzTransfer s s x := by
  have hvs (i : I) : star (v : E) * t i = s i := by
    rw [← hv i, ← mul_assoc, v.property.1, one_mul]
  simp only [finiteCuntzTransfer, Finset.mul_sum, ← mul_assoc, hvs]

omit [DecidableEq I] in
private lemma bergExtension_transfer_star (s t : I → E) (v : unitary E)
    (hv : ∀ i, (v : E) * s i = t i) (x : E) :
    finiteCuntzTransfer s t x * star (v : E) = finiteCuntzTransfer t t x := by
  have hvs (i : I) : star (s i) * star (v : E) = star (t i) := by
    rw [← star_mul, hv i]
  simp only [finiteCuntzTransfer, Finset.sum_mul, mul_assoc, hvs]

lemma bergBottom_source (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (v : unitary E) (hv : ∀ i, (v : E) * s i = t i) :
    star (bergBottomCoefficient s t v) * bergBottomCoefficient s t v =
      bergTowerLayer (finiteCuntzDiagonalHom s hs) 0 := by
  have hleft := bergExtension_star_transfer s t v hv 1
  have hright : star (finiteCuntzTransfer s t 1) * (v : E) =
      finiteCuntzTransfer s s 1 := by
    simpa only [star_mul, star_star, finiteCuntzTransfer_star, star_one] using
      congrArg star hleft
  rw [bergBottomCoefficient, star_sub, sub_mul, mul_sub, mul_sub,
    v.property.1, hleft, hright, bergTransfer_star_mul s t hs ht]
  change (1 - finiteCuntzDiagonalHom s hs 1) -
    (finiteCuntzDiagonalHom s hs 1 - finiteCuntzDiagonalHom s hs (star (1 : E) * 1)) = _
  simp only [star_one, one_mul, sub_self, sub_zero, bergTowerLayer,
    bergTowerTail_zero, bergTowerTail_succ]

lemma bergBottom_target (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (v : unitary E) (hv : ∀ i, (v : E) * s i = t i) :
    bergBottomCoefficient s t v * star (bergBottomCoefficient s t v) =
      bergTowerLayer (finiteCuntzDiagonalHom t ht) 0 := by
  have hleft := bergExtension_transfer_star s t v hv 1
  have hright : (v : E) * star (finiteCuntzTransfer s t 1) =
      finiteCuntzTransfer t t 1 := by
    simpa only [star_mul, star_star, finiteCuntzTransfer_star, star_one] using
      congrArg star hleft
  rw [bergBottomCoefficient, star_sub, mul_sub, sub_mul, sub_mul,
    v.property.2, hleft, hright, bergTransfer_mul_star s t hs ht]
  change (1 - finiteCuntzDiagonalHom t ht 1) -
    (finiteCuntzDiagonalHom t ht 1 - finiteCuntzDiagonalHom t ht (1 * star (1 : E))) = _
  simp only [star_one, one_mul, sub_self, sub_zero, bergTowerLayer,
    bergTowerTail_zero, bergTowerTail_succ]

/-- Filling the complementary bottom corner makes one transfer step unitary. -/
lemma bergBottom_add_transfer_mem_unitary (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (v : unitary E) (hv : ∀ i, (v : E) * s i = t i)
    (x : E) (hx : x ∈ unitary E) :
    bergBottomCoefficient s t v + finiteCuntzTransfer s t x ∈ unitary E := by
  let c := bergBottomCoefficient s t v
  let z := finiteCuntzTransfer s t x
  have hct (i : I) : star c * t i = 0 := by
    have h := congrArg star (bergBottom_star_generator_mul s t ht v hv i)
    simpa only [star_mul, star_star, star_zero] using h
  have hcz : star c * z = 0 := by
    simp only [z, finiteCuntzTransfer, Finset.mul_sum, ← mul_assoc, hct, zero_mul,
      Finset.sum_const_zero]
  have hzc : star z * c = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hcz
  have hcz' : c * star z = 0 := by
    rw [show z = finiteCuntzTransfer s t x from rfl, finiteCuntzTransfer_star]
    simp only [finiteCuntzTransfer, Finset.mul_sum, ← mul_assoc,
      bergBottom_mul_generator s t hs v hv, zero_mul, Finset.sum_const_zero, c]
  have hzc' : z * star c = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hcz'
  apply Unitary.mem_iff.mpr
  constructor
  · change star (c + z) * (c + z) = 1
    rw [star_add, add_mul, mul_add, mul_add, hcz, hzc, add_zero, zero_add]
    rw [show star c * c = bergTowerLayer (finiteCuntzDiagonalHom s hs) 0 from
      bergBottom_source s t hs ht v hv]
    rw [show star z * z = finiteCuntzDiagonalHom s hs (star x * x) from
      bergTransfer_star_mul s t hs ht x x, hx.1]
    simp only [bergTowerLayer, bergTowerTail_zero, bergTowerTail_succ, sub_add_cancel]
  · change (c + z) * star (c + z) = 1
    rw [star_add, add_mul, mul_add, mul_add, hcz', hzc', add_zero, zero_add]
    rw [show c * star c = bergTowerLayer (finiteCuntzDiagonalHom t ht) 0 from
      bergBottom_target s t hs ht v hv]
    rw [show z * star z = finiteCuntzDiagonalHom t ht (x * star x) from
      bergTransfer_mul_star s t hs ht x x, hx.2]
    simp only [bergTowerLayer, bergTowerTail_zero, bergTowerTail_succ, sub_add_cancel]

/-- A finite tower is assembled with its entire terminal transfer coefficient. -/
def bergFiniteTower (s t : I → E) (v : unitary E) : ℕ → E → E
  | 0, x => x
  | n + 1, x => bergBottomCoefficient s t v +
      finiteCuntzTransfer s t (bergFiniteTower s t v n x)

omit [DecidableEq I] in
@[simp] lemma bergFiniteTower_zero (s t : I → E) (v : unitary E) (x : E) :
    bergFiniteTower s t v 0 x = x := rfl

omit [DecidableEq I] in
@[simp] lemma bergFiniteTower_succ (s t : I → E) (v : unitary E) (n : ℕ) (x : E) :
    bergFiniteTower s t v (n + 1) x = bergBottomCoefficient s t v +
      finiteCuntzTransfer s t (bergFiniteTower s t v n x) := rfl

/-- Every finite assembled tower is a genuine unitary, including its last corner. -/
lemma bergFiniteTower_mem_unitary (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (v : unitary E) (hv : ∀ i, (v : E) * s i = t i)
    (n : ℕ) (x : E) (hx : x ∈ unitary E) :
    bergFiniteTower s t v n x ∈ unitary E := by
  induction n with
  | zero => exact hx
  | succ n ih => exact bergBottom_add_transfer_mem_unitary s t hs ht v hv _ ih

omit [DecidableEq I] in
/-- The terminal coefficient is the only varying term in two towers with the same bottom. -/
lemma bergFiniteTower_sub (s t : I → E) (v : unitary E) (n : ℕ) (x y : E) :
    bergFiniteTower s t v n x - bergFiniteTower s t v n y =
      finiteCuntzTransferIter s t n (x - y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bergFiniteTower_succ, bergFiniteTower_succ, add_sub_add_left_eq_sub,
      finiteCuntzTransfer_sub, ih, finiteCuntzTransferIter_succ]

lemma bergFiniteTower_sub_norm_le (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (v : unitary E) (n : ℕ) (x y : E) :
    ‖bergFiniteTower s t v n x - bergFiniteTower s t v n y‖ ≤ ‖x - y‖ := by
  rw [bergFiniteTower_sub]
  exact finiteCuntzTransferIter_norm_le s t hs ht n (x - y)

omit [DecidableEq I] in
lemma bergFiniteTower_continuous (s t : I → E) (v : unitary E) (n : ℕ) :
    Continuous (bergFiniteTower s t v n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih =>
    exact continuous_const.add ((finiteCuntzTransfer_continuous s t).comp ih)

lemma bergFiniteTower_intertwining (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (v : unitary E) (hv : ∀ i, (v : E) * s i = t i)
    (n : ℕ) (x : E) (i : I) :
    bergFiniteTower s t v (n + 1) x * s i = t i * bergFiniteTower s t v n x := by
  rw [bergFiniteTower_succ, add_mul, bergBottom_mul_generator s t hs v hv,
    zero_add, finiteCuntzTransfer_mul s t hs]

lemma bergFiniteTower_residual (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (v : unitary E) (hv : ∀ i, (v : E) * s i = t i)
    (n : ℕ) (x : E) (i : I) :
    bergFiniteTower s t v (n + 1) x * s i - t i * bergFiniteTower s t v (n + 1) x =
      t i * (bergFiniteTower s t v n x - bergFiniteTower s t v (n + 1) x) := by
  rw [bergFiniteTower_intertwining s t hs v hv, mul_sub]

end CuntzRow

end WeakPureInfiniteness

end

end OAI
