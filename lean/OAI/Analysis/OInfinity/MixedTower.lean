import OAI.Analysis.OInfinity.BergTent

namespace OAI

/-! # Two commuting Cuntz rows and their finite rectangular towers

The transfer partial isometry moves one source layer into one target layer.
The source and target rectangles, and their terminal strips, remain explicit.
These identities do not yet identify the two complete terminal tails by a
unitary that intertwines both rows.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I J : Type*} [CStarAlgebra E]

/-- The tensor-factor commutation relations, including adjoints. -/
def bergRowsCommute (s : I → E) (t : J → E) : Prop :=
  ∀ i j, Commute (s i) (t j) ∧ Commute (s i) (star (t j))

lemma bergRowsCommute_symm (s : I → E) (t : J → E) (hc : bergRowsCommute s t) :
    bergRowsCommute t s := by
  intro j i
  refine ⟨(hc i j).1.symm, ?_⟩
  simpa only [star_star] using (hc i j).2.star_star.symm

/-- The finite rectangle decomposition retains both terminal strips and
 their intersection. No convergence or vanishing boundary is asserted. -/
lemma bergMixedFinitePartition (φ ψ : E →⋆ₙₐ[ℂ] E) (N M : ℕ) :
    ((∑ k ∈ Finset.range N, ∑ l ∈ Finset.range M,
        bergTowerLayer φ k * bergTowerLayer ψ l) +
      (∑ k ∈ Finset.range N, bergTowerLayer φ k * bergTowerTail ψ M)) +
      ((∑ l ∈ Finset.range M, bergTowerTail φ N * bergTowerLayer ψ l) +
        bergTowerTail φ N * bergTowerTail ψ M) = 1 := by
  have h := congrArg₂ (fun x y : E => x * y)
    (bergTower_finite_partition φ N) (bergTower_finite_partition ψ M)
  simp only [add_mul, mul_add, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_add_distrib, one_mul] at h
  rw [Finset.sum_comm] at h
  convert h using 1
  abel

variable [Fintype I] [DecidableEq I]

lemma bergTail_commutes_generators (s : I → E) (t : J → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hc : bergRowsCommute s t) (k : ℕ) (j : J) :
    Commute (bergTowerTail (finiteCuntzDiagonalHom s hs) k) (t j) ∧
      Commute (bergTowerTail (finiteCuntzDiagonalHom s hs) k) (star (t j)) := by
  induction k with
  | zero => exact ⟨Commute.one_left _, Commute.one_left _⟩
  | succ k ih =>
    change Commute (∑ i, s i * bergTowerTail (finiteCuntzDiagonalHom s hs) k * star (s i))
        (t j) ∧ Commute (∑ i, s i * bergTowerTail (finiteCuntzDiagonalHom s hs) k * star (s i))
        (star (t j))
    constructor
    · apply Commute.sum_left
      intro i hi
      have hstar : Commute (star (s i)) (t j) := by
        simpa only [star_star] using (hc i j).2.star_star
      exact ((hc i j).1.mul_left ih.1).mul_left hstar
    · apply Commute.sum_left
      intro i hi
      exact ((hc i j).2.mul_left ih.2).mul_left (hc i j).1.star_star

lemma bergLayer_commutes_generators (s : I → E) (t : J → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hc : bergRowsCommute s t) (k : ℕ) (j : J) :
    Commute (bergTowerLayer (finiteCuntzDiagonalHom s hs) k) (t j) ∧
      Commute (bergTowerLayer (finiteCuntzDiagonalHom s hs) k) (star (t j)) := by
  exact ⟨(bergTail_commutes_generators s t hs hc k j).1.sub_left
      (bergTail_commutes_generators s t hs hc (k + 1) j).1,
    (bergTail_commutes_generators s t hs hc k j).2.sub_left
      (bergTail_commutes_generators s t hs hc (k + 1) j).2⟩

variable [Fintype J] [DecidableEq J]

lemma bergTails_commute (s : I → E) (t : J → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hc : bergRowsCommute s t) (k l : ℕ) :
    Commute (bergTowerTail (finiteCuntzDiagonalHom s hs) k)
      (bergTowerTail (finiteCuntzDiagonalHom t ht) l) := by
  induction l with
  | zero => exact Commute.one_right _
  | succ l ih =>
    change Commute (bergTowerTail (finiteCuntzDiagonalHom s hs) k)
      (∑ j, t j * bergTowerTail (finiteCuntzDiagonalHom t ht) l * star (t j))
    apply Commute.sum_right
    intro j hj
    have h := bergTail_commutes_generators s t hs hc k j
    exact (h.1.mul_right ih).mul_right h.2

lemma bergLayers_commute (s : I → E) (t : J → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hc : bergRowsCommute s t) (k l : ℕ) :
    Commute (bergTowerLayer (finiteCuntzDiagonalHom s hs) k)
      (bergTowerLayer (finiteCuntzDiagonalHom t ht) l) :=
  ((bergTails_commute s t hs ht hc k l).sub_right
    (bergTails_commute s t hs ht hc k (l + 1))).sub_left
    ((bergTails_commute s t hs ht hc (k + 1) l).sub_right
      (bergTails_commute s t hs ht hc (k + 1) (l + 1)))

/-- One rectangle in the product of the two orthogonal layer towers. -/
def bergRectangle (s : I → E) (t : J → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0) (k l : ℕ) : E :=
  bergTowerLayer (finiteCuntzDiagonalHom s hs) k *
    bergTowerLayer (finiteCuntzDiagonalHom t ht) l

lemma bergRectangle_star (s : I → E) (t : J → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hc : bergRowsCommute s t) (k l : ℕ) :
    star (bergRectangle s t hs ht k l) = bergRectangle s t hs ht k l := by
  rw [bergRectangle, star_mul, bergTowerLayer_star, bergTowerLayer_star,
    (bergLayers_commute s t hs ht hc k l).eq]

lemma bergRectangle_sq (s : I → E) (t : J → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hc : bergRowsCommute s t) (k l : ℕ) :
    bergRectangle s t hs ht k l * bergRectangle s t hs ht k l = bergRectangle s t hs ht k l := by
  let p := bergTowerLayer (finiteCuntzDiagonalHom s hs) k
  let q := bergTowerLayer (finiteCuntzDiagonalHom t ht) l
  have hp : p * p = p := bergTowerLayer_sq _ _
  have hq : q * q = q := bergTowerLayer_sq _ _
  have hcomm : p * q = q * p := (bergLayers_commute s t hs ht hc k l).eq
  change (p * q) * (p * q) = p * q
  calc
    _ = p * (q * p) * q := by noncomm_ring
    _ = p * (p * q) * q := by rw [← hcomm]
    _ = (p * p) * (q * q) := by noncomm_ring
    _ = _ := by rw [hp, hq]

lemma bergRectangle_orthogonal (s : I → E) (t : J → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hc : bergRowsCommute s t) (k l k' l' : ℕ) (hne : (k, l) ≠ (k', l')) :
    bergRectangle s t hs ht k l * bergRectangle s t hs ht k' l' = 0 := by
  have he : bergRectangle s t hs ht k l * bergRectangle s t hs ht k' l' =
      (bergTowerLayer (finiteCuntzDiagonalHom s hs) k *
        bergTowerLayer (finiteCuntzDiagonalHom s hs) k') *
      (bergTowerLayer (finiteCuntzDiagonalHom t ht) l *
        bergTowerLayer (finiteCuntzDiagonalHom t ht) l') := by
    unfold bergRectangle
    calc
      _ = bergTowerLayer (finiteCuntzDiagonalHom s hs) k *
          (bergTowerLayer (finiteCuntzDiagonalHom t ht) l *
            bergTowerLayer (finiteCuntzDiagonalHom s hs) k') *
              bergTowerLayer (finiteCuntzDiagonalHom t ht) l' := by noncomm_ring
      _ = _ := by rw [← (bergLayers_commute s t hs ht hc k' l).eq]; noncomm_ring
  rw [he]
  by_cases hkk : k = k'
  · have hll : l ≠ l' := by intro h; exact hne (Prod.ext hkk h)
    rw [bergTowerLayer_mul_of_ne _ hll, mul_zero]
  · rw [bergTowerLayer_mul_of_ne _ hkk, zero_mul]

omit [Fintype J] [DecidableEq J] in
lemma bergLayer_under_first_tail (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (k : ℕ) :
    bergTowerTail (finiteCuntzDiagonalHom s hs) 1 *
        bergTowerLayer (finiteCuntzDiagonalHom s hs) (k + 1) =
      bergTowerLayer (finiteCuntzDiagonalHom s hs) (k + 1) := by
  rw [bergTowerLayer, mul_sub, bergTowerTail_mul_of_le _ (by omega),
    bergTowerTail_mul_of_le _ (by omega)]

section Transfer

variable (s t : I → E)
variable (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
variable (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
variable (hc : bergRowsCommute s t)

include hc

omit [Fintype J] [DecidableEq J] in
lemma bergTail_source_transfer (k : ℕ) :
    bergTowerTail (finiteCuntzDiagonalHom s hs) k * finiteCuntzTransfer s t 1 =
      finiteCuntzTransfer s t 1 * bergTowerTail (finiteCuntzDiagonalHom s hs) (k + 1) := by
  simp only [finiteCuntzTransfer, mul_one, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hcom := (bergTail_commutes_generators s t hs hc k i).1
  have hshift : bergTowerTail (finiteCuntzDiagonalHom s hs) k * star (s i) =
      star (s i) * bergTowerTail (finiteCuntzDiagonalHom s hs) (k + 1) := by
    simpa only [star_mul, bergTowerTail_star] using
      (congrArg star (bergTowerTail_succ_mul_generator s hs k i)).symm
  calc
    _ = t i * (bergTowerTail (finiteCuntzDiagonalHom s hs) k * star (s i)) := by
      rw [← mul_assoc, hcom.eq, mul_assoc]
    _ = _ := by rw [hshift, ← mul_assoc]

omit [Fintype J] [DecidableEq J] in
lemma bergTail_target_transfer (l : ℕ) :
    bergTowerTail (finiteCuntzDiagonalHom t ht) (l + 1) * finiteCuntzTransfer s t 1 =
      finiteCuntzTransfer s t 1 * bergTowerTail (finiteCuntzDiagonalHom t ht) l := by
  simp only [finiteCuntzTransfer, mul_one, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hcom := (bergTail_commutes_generators t s ht (bergRowsCommute_symm s t hc) l i).2
  calc
    _ = t i * (bergTowerTail (finiteCuntzDiagonalHom t ht) l * star (s i)) := by
      rw [← mul_assoc, bergTowerTail_succ_mul_generator t ht l i, mul_assoc]
    _ = _ := by rw [hcom.eq, ← mul_assoc]

include ht in
omit [Fintype J] [DecidableEq J] in
/-- Transfer powers have the exact global source tails. -/
lemma bergTransfer_pow_source (m : ℕ) :
    star ((finiteCuntzTransfer s t 1) ^ m) * (finiteCuntzTransfer s t 1) ^ m =
      bergTowerTail (finiteCuntzDiagonalHom s hs) m := by
  let V := finiteCuntzTransfer s t 1
  have hv : star V * V = bergTowerTail (finiteCuntzDiagonalHom s hs) 1 := by
    dsimp only [V]
    rw [bergTransfer_star_mul s t hs ht, star_one, one_mul]
    rfl
  change star (V ^ m) * V ^ m = _
  induction m with
  | zero => simp only [pow_zero, star_one, one_mul, bergTowerTail_zero]
  | succ m ih =>
    rw [pow_succ, star_mul]
    calc
      _ = star V * (star (V ^ m) * V ^ m) * V := by noncomm_ring
      _ = star V * (bergTowerTail (finiteCuntzDiagonalHom s hs) m * V) := by
        rw [ih, mul_assoc]
      _ = star V * (V * bergTowerTail (finiteCuntzDiagonalHom s hs) (m + 1)) := by
        rw [bergTail_source_transfer s t hs hc]
      _ = bergTowerTail (finiteCuntzDiagonalHom s hs) 1 *
          bergTowerTail (finiteCuntzDiagonalHom s hs) (m + 1) := by rw [← mul_assoc, hv]
      _ = _ := bergTowerTail_mul_of_le _ (by omega)

include hs in
omit [Fintype J] [DecidableEq J] in
/-- Transfer powers have the exact global target tails. -/
lemma bergTransfer_pow_target (m : ℕ) :
    (finiteCuntzTransfer s t 1) ^ m * star ((finiteCuntzTransfer s t 1) ^ m) =
      bergTowerTail (finiteCuntzDiagonalHom t ht) m := by
  let V := finiteCuntzTransfer s t 1
  have hv : V * star V = bergTowerTail (finiteCuntzDiagonalHom t ht) 1 := by
    dsimp only [V]
    rw [bergTransfer_mul_star s t hs ht, star_one, mul_one]
    rfl
  change V ^ m * star (V ^ m) = _
  induction m with
  | zero => simp only [pow_zero, star_one, one_mul, bergTowerTail_zero]
  | succ m ih =>
    rw [pow_succ', star_mul]
    calc
      _ = V * (V ^ m * star (V ^ m)) * star V := by noncomm_ring
      _ = (V * bergTowerTail (finiteCuntzDiagonalHom t ht) m) * star V := by rw [ih]
      _ = (bergTowerTail (finiteCuntzDiagonalHom t ht) (m + 1) * V) * star V := by
        rw [← bergTail_target_transfer s t ht hc]
      _ = bergTowerTail (finiteCuntzDiagonalHom t ht) (m + 1) *
          bergTowerTail (finiteCuntzDiagonalHom t ht) 1 := by rw [mul_assoc, hv]
      _ = _ := bergTowerTail_mul_of_ge _ (by omega)

omit [Fintype J] [DecidableEq J] in
lemma bergLayer_source_transfer (k : ℕ) :
    bergTowerLayer (finiteCuntzDiagonalHom s hs) k * finiteCuntzTransfer s t 1 =
      finiteCuntzTransfer s t 1 * bergTowerLayer (finiteCuntzDiagonalHom s hs) (k + 1) := by
  simp only [finiteCuntzTransfer, mul_one, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hcom := (bergLayer_commutes_generators s t hs hc k i).1
  have hshift : bergTowerLayer (finiteCuntzDiagonalHom s hs) k * star (s i) =
      star (s i) * bergTowerLayer (finiteCuntzDiagonalHom s hs) (k + 1) := by
    simpa only [star_mul, bergTowerLayer_star] using
      (congrArg star (bergTowerLayer_succ_mul_generator s hs k i)).symm
  calc
    _ = t i * (bergTowerLayer (finiteCuntzDiagonalHom s hs) k * star (s i)) := by
      rw [← mul_assoc, hcom.eq, mul_assoc]
    _ = _ := by rw [hshift, ← mul_assoc]

omit [Fintype J] [DecidableEq J] in
lemma bergLayer_target_transfer (l : ℕ) :
    bergTowerLayer (finiteCuntzDiagonalHom t ht) (l + 1) * finiteCuntzTransfer s t 1 =
      finiteCuntzTransfer s t 1 * bergTowerLayer (finiteCuntzDiagonalHom t ht) l := by
  simp only [finiteCuntzTransfer, mul_one, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hcom := (bergLayer_commutes_generators t s ht (bergRowsCommute_symm s t hc) l i).2
  calc
    _ = t i * (bergTowerLayer (finiteCuntzDiagonalHom t ht) l * star (s i)) := by
      rw [← mul_assoc, bergTowerLayer_succ_mul_generator t ht l i, mul_assoc]
    _ = _ := by rw [hcom.eq, ← mul_assoc]

omit [Fintype J] [DecidableEq J] in
/-- One step preserves total layer degree and moves its separator. -/
lemma bergRectangle_transfer (k l : ℕ) :
    bergRectangle s t hs ht k (l + 1) * finiteCuntzTransfer s t 1 =
      finiteCuntzTransfer s t 1 * bergRectangle s t hs ht (k + 1) l := by
  unfold bergRectangle
  rw [mul_assoc, bergLayer_target_transfer s t ht hc l, ← mul_assoc,
    bergLayer_source_transfer s t hs hc k, mul_assoc]

omit [Fintype J] [DecidableEq J] in
lemma bergRectangle_transfer_source (k l : ℕ) :
    star (finiteCuntzTransfer s t 1 * bergRectangle s t hs ht (k + 1) l) *
      (finiteCuntzTransfer s t 1 * bergRectangle s t hs ht (k + 1) l) =
      bergRectangle s t hs ht (k + 1) l := by
  let P := bergRectangle s t hs ht (k + 1) l
  let V := finiteCuntzTransfer s t 1
  have hv : star V * V = bergTowerTail (finiteCuntzDiagonalHom s hs) 1 := by
    dsimp only [V]
    rw [bergTransfer_star_mul s t hs ht, star_one, one_mul]
    rfl
  have hp : bergTowerTail (finiteCuntzDiagonalHom s hs) 1 * P = P := by
    dsimp only [P, bergRectangle]
    rw [← mul_assoc, bergLayer_under_first_tail s hs k]
  have hpr : P * bergTowerTail (finiteCuntzDiagonalHom s hs) 1 = P := by
    have hpstar : star P = P := bergRectangle_star s t hs ht hc _ _
    simpa only [star_mul, hpstar, bergTowerTail_star] using
      congrArg star hp
  change star (V * P) * (V * P) = P
  rw [star_mul, show star P = P from bergRectangle_star s t hs ht hc _ _]
  calc
    _ = P * (star V * V) * P := by noncomm_ring
    _ = P * P := by rw [hv, hpr]
    _ = P := bergRectangle_sq s t hs ht hc _ _

omit [Fintype J] [DecidableEq J] in
lemma bergRectangle_transfer_target (k l : ℕ) :
    (finiteCuntzTransfer s t 1 * bergRectangle s t hs ht (k + 1) l) *
      star (finiteCuntzTransfer s t 1 * bergRectangle s t hs ht (k + 1) l) =
      bergRectangle s t hs ht k (l + 1) := by
  let P := bergRectangle s t hs ht (k + 1) l
  let Q := bergRectangle s t hs ht k (l + 1)
  let V := finiteCuntzTransfer s t 1
  have hv : V * star V = bergTowerTail (finiteCuntzDiagonalHom t ht) 1 := by
    dsimp only [V]
    rw [bergTransfer_mul_star s t hs ht, star_one, mul_one]
    rfl
  have hcom : Commute (bergTowerLayer (finiteCuntzDiagonalHom s hs) k)
      (bergTowerTail (finiteCuntzDiagonalHom t ht) 1) :=
    (bergTails_commute s t hs ht hc k 1).sub_left
      (bergTails_commute s t hs ht hc (k + 1) 1)
  have hq : bergTowerTail (finiteCuntzDiagonalHom t ht) 1 * Q = Q := by
    dsimp only [Q, bergRectangle]
    rw [← mul_assoc, ← hcom.eq, mul_assoc, bergLayer_under_first_tail t ht l]
  have hqr : Q * bergTowerTail (finiteCuntzDiagonalHom t ht) 1 = Q := by
    have hqstar : star Q = Q := bergRectangle_star s t hs ht hc _ _
    simpa only [star_mul, hqstar, bergTowerTail_star] using
      congrArg star hq
  have hVP : V * P = Q * V := (bergRectangle_transfer s t hs ht hc k l).symm
  change (V * P) * star (V * P) = Q
  rw [star_mul, show star P = P from bergRectangle_star s t hs ht hc _ _]
  calc
    _ = V * (P * P) * star V := by noncomm_ring
    _ = V * P * star V := by rw [bergRectangle_sq s t hs ht hc _ _]
    _ = Q * (V * star V) := by rw [hVP, mul_assoc]
    _ = Q := by rw [hv, hqr]

omit [Fintype J] [DecidableEq J] in
lemma bergRectangle_transfer_square_zero (k l : ℕ) :
    (finiteCuntzTransfer s t 1 * bergRectangle s t hs ht (k + 1) l) *
      (finiteCuntzTransfer s t 1 * bergRectangle s t hs ht (k + 1) l) = 0 := by
  let P := bergRectangle s t hs ht (k + 1) l
  let Q := bergRectangle s t hs ht k (l + 1)
  let V := finiteCuntzTransfer s t 1
  let r := V * P
  have hrP : r * P = r := by
    dsimp only [r]
    rw [mul_assoc, bergRectangle_sq s t hs ht hc]
  have hQr : Q * r = r := by
    dsimp only [r]
    rw [← mul_assoc, bergRectangle_transfer s t hs ht hc, mul_assoc,
      bergRectangle_sq s t hs ht hc]
  have hPQ : P * Q = 0 := bergRectangle_orthogonal s t hs ht hc _ _ _ _ (by
    intro h
    have hfirst := congrArg Prod.fst h
    change k + 1 = k at hfirst
    omega)
  change r * r = 0
  calc
    _ = (r * P) * (Q * r) := by rw [hrP, hQr]
    _ = r * (P * Q) * r := by noncomm_ring
    _ = 0 := by rw [hPQ, mul_zero, zero_mul]

omit [Fintype J] [DecidableEq J] in
lemma bergRectangle_transfer_partial (k l : ℕ) :
    (finiteCuntzTransfer s t 1 * bergRectangle s t hs ht (k + 1) l) *
      star (finiteCuntzTransfer s t 1 * bergRectangle s t hs ht (k + 1) l) *
      (finiteCuntzTransfer s t 1 * bergRectangle s t hs ht (k + 1) l) =
        finiteCuntzTransfer s t 1 * bergRectangle s t hs ht (k + 1) l := by
  rw [bergRectangle_transfer_target s t hs ht hc, ← mul_assoc,
    bergRectangle_transfer s t hs ht hc, mul_assoc, bergRectangle_sq s t hs ht hc]

omit [Fintype J] [DecidableEq J] in
/-- Adjacent rectangles on a shell are related by an explicit connected
quarter-turn. This is a local terminal-corner move, not yet a global flip. -/
lemma exists_connected_rectangle_step (k l : ℕ) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (u : E) * bergRectangle s t hs ht (k + 1) l =
        finiteCuntzTransfer s t 1 * bergRectangle s t hs ht (k + 1) l := by
  let r := finiteCuntzTransfer s t 1 * bergRectangle s t hs ht (k + 1) l
  have hr := bergRectangle_transfer_partial s t hs ht hc k l
  have hrr := bergRectangle_transfer_square_zero s t hs ht hc k l
  let u := partialIsometryBergRotationUnitary r hr hrr (Real.pi / 2)
  refine ⟨u, partialIsometryBergRotationUnitary_joined r hr hrr _, ?_⟩
  have h := partialIsometryBergRotation_quarter_mul_initial r hr hrr
  rwa [bergRectangle_transfer_source s t hs ht hc] at h

omit [Fintype J] [DecidableEq J] in
lemma exists_connected_rectangle_conjugacy (k l : ℕ) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (u : E) * bergRectangle s t hs ht (k + 1) l * star (u : E) =
        bergRectangle s t hs ht k (l + 1) := by
  obtain ⟨u, hu, hUp⟩ := exists_connected_rectangle_step s t hs ht hc k l
  refine ⟨u, hu, ?_⟩
  let P := bergRectangle s t hs ht (k + 1) l
  have hp : star P = P := bergRectangle_star s t hs ht hc _ _
  have hpp : P * P = P := bergRectangle_sq s t hs ht hc _ _
  calc
    (u : E) * P * star (u : E) = ((u : E) * P) * star ((u : E) * P) := by
      rw [star_mul, hp]
      calc
        _ = (u : E) * (P * P) * star (u : E) := by rw [hpp]
        _ = _ := by noncomm_ring
    _ = (finiteCuntzTransfer s t 1 * P) * star (finiteCuntzTransfer s t 1 * P) := by rw [hUp]
    _ = _ := bergRectangle_transfer_target s t hs ht hc k l

omit [Fintype J] [DecidableEq J] in
/-- A finite sequence of connected rectangle rotations transports either
endpoint of a total-degree shell to the other endpoint. -/
lemma exists_connected_rectangle_path (m k l : ℕ) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (u : E) * bergRectangle s t hs ht (k + m) l * star (u : E) =
        bergRectangle s t hs ht k (l + m) := by
  induction m generalizing k l with
  | zero =>
    refine ⟨1, Joined.refl 1, ?_⟩
    simp only [Submonoid.coe_one, one_mul, star_one, mul_one, Nat.add_zero]
  | succ m ih =>
    obtain ⟨u, hu, hup⟩ := ih (k + 1) l
    obtain ⟨v, hv, hvp⟩ := exists_connected_rectangle_conjugacy s t hs ht hc k (l + m)
    refine ⟨v * u, ?_, ?_⟩
    · simpa only [one_mul] using hv.mul hu
    · have hidx : k + (m + 1) = (k + 1) + m := by omega
      have hldy : l + (m + 1) = (l + m) + 1 := by omega
      rw [hidx, hldy, Submonoid.coe_mul, star_mul]
      calc
        _ = (v : E) * ((u : E) * bergRectangle s t hs ht ((k + 1) + m) l *
              star (u : E)) * star (v : E) := by noncomm_ring
        _ = _ := by rw [hup, hvp]

end Transfer

end WeakPureInfiniteness

end

end OAI
