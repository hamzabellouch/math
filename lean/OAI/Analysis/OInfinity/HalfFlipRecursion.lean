import Mathlib

namespace OAI

/-! # Finite recursive intertwiners for the O∞ half-flip

For two finite Cuntz families, the transfer operator sends `x` to
`∑ i, t i * x * star (s i)`. Its Cesàro means are contractions and satisfy a
uniform recursive intertwining estimate. These means are not asserted to be
unitary; constructing nearby connected unitaries remains a separate step.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

/-- The finite transfer operator from the family `s` to the family `t`. -/
def finiteCuntzTransfer (s t : I → E) (x : E) : E :=
  ∑ i, t i * x * star (s i)

omit [Fintype I] in
private lemma finiteCuntzDiagonal_mul_term (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (x y : E) (i j : I) :
    (s i * x * star (s i)) * (s j * y * star (s j)) =
      if i = j then s i * (x * y) * star (s i) else 0 := by
  calc
    _ = s i * x * (star (s i) * s j) * y * star (s j) := by noncomm_ring
    _ = _ := by
      rw [hs]
      split_ifs with h
      · subst j
        simp only [mul_one, mul_assoc]
      · simp

/-- The diagonal corner sum is a genuine star homomorphism. -/
def finiteCuntzDiagonalHom (s : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) : E →⋆ₙₐ[ℂ] E where
  toFun x := ∑ i, s i * x * star (s i)
  map_zero' := by simp
  map_add' x y := by simp only [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [mul_smul_comm, smul_mul_assoc, Finset.smul_sum, MonoidHom.id_apply]
  map_mul' x y := by
    simp only [Finset.sum_mul, Finset.mul_sum, finiteCuntzDiagonal_mul_term s hs]
    simp
  map_star' x := by simp only [star_sum, star_mul, star_star, mul_assoc]

lemma finiteCuntzTransfer_mul (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (x : E) (i : I) : finiteCuntzTransfer s t x * s i = t i * x := by
  simp only [finiteCuntzTransfer, Finset.sum_mul]
  have hterm (j : I) : (t j * x * star (s j)) * s i =
      if j = i then t j * x else 0 := by
    rw [mul_assoc, hs]
    split_ifs <;> simp
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma finiteCuntzTransfer_star_mul (s t : I → E)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0) (x : E) :
    star (finiteCuntzTransfer s t x) * finiteCuntzTransfer s t x =
      ∑ i, s i * (star x * x) * star (s i) := by
  simp only [finiteCuntzTransfer, star_sum, star_mul, star_star,
    Finset.sum_mul, Finset.mul_sum]
  have hterm (i j : I) :
      (s i * (star x * star (t i))) * (t j * x * star (s j)) =
        if i = j then s i * (star x * x) * star (s i) else 0 := by
    calc
      _ = s i * star x * (star (t i) * t j) * x * star (s j) := by noncomm_ring
      _ = _ := by
        rw [ht]
        split_ifs with h
        · subst j
          simp only [mul_one, mul_assoc]
        · simp
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [DecidableEq I] in
lemma finiteCuntzTransfer_continuous (s t : I → E) :
    Continuous (finiteCuntzTransfer s t) := by
  unfold finiteCuntzTransfer
  fun_prop

omit [DecidableEq I] in
lemma finiteCuntzTransfer_sub (s t : I → E) (x y : E) :
    finiteCuntzTransfer s t x - finiteCuntzTransfer s t y =
      finiteCuntzTransfer s t (x - y) := by
  simp only [finiteCuntzTransfer, mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma finiteCuntzTransfer_norm_le (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0) (x : E) :
    ‖finiteCuntzTransfer s t x‖ ≤ ‖x‖ := by
  have h := NonUnitalStarAlgHom.norm_apply_le (finiteCuntzDiagonalHom s hs) (star x * x)
  change ‖∑ i, s i * (star x * x) * star (s i)‖ ≤ ‖star x * x‖ at h
  rw [← finiteCuntzTransfer_star_mul s t ht, CStarRing.norm_star_mul_self,
    CStarRing.norm_star_mul_self] at h
  nlinarith only [h, norm_nonneg (finiteCuntzTransfer s t x), norm_nonneg x]

lemma finiteCuntzTransfer_sub_norm_le (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0) (x y : E) :
    ‖finiteCuntzTransfer s t x - finiteCuntzTransfer s t y‖ ≤ ‖x - y‖ := by
  rw [finiteCuntzTransfer_sub]
  exact finiteCuntzTransfer_norm_le s t hs ht (x - y)

/-- Iteration is kept explicit to expose the last boundary term. -/
def finiteCuntzTransferIter (s t : I → E) : ℕ → E → E
  | 0, x => x
  | n + 1, x => finiteCuntzTransfer s t (finiteCuntzTransferIter s t n x)

omit [DecidableEq I] in
@[simp] lemma finiteCuntzTransferIter_zero (s t : I → E) (x : E) :
    finiteCuntzTransferIter s t 0 x = x := rfl

omit [DecidableEq I] in
@[simp] lemma finiteCuntzTransferIter_succ (s t : I → E) (n : ℕ) (x : E) :
    finiteCuntzTransferIter s t (n + 1) x =
      finiteCuntzTransfer s t (finiteCuntzTransferIter s t n x) := rfl

lemma finiteCuntzTransferIter_norm_le (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0) (n : ℕ) (x : E) :
    ‖finiteCuntzTransferIter s t n x‖ ≤ ‖x‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (finiteCuntzTransfer_norm_le s t hs ht _).trans ih

def finiteCuntzTransferSum (s t : I → E) (n : ℕ) (x : E) : E :=
  ∑ k ∈ Finset.range (n + 1), finiteCuntzTransferIter s t k x

omit [DecidableEq I] in
lemma finiteCuntzTransferSum_succ (s t : I → E) (n : ℕ) (x : E) :
    finiteCuntzTransferSum s t (n + 1) x =
      finiteCuntzTransferSum s t n x + finiteCuntzTransferIter s t (n + 1) x := by
  exact Finset.sum_range_succ _ _

/-- The entire intertwining error is the difference of two boundary terms. -/
lemma finiteCuntzTransferSum_intertwining (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (n : ℕ) (x : E) (i : I) :
    finiteCuntzTransferSum s t n x * s i - t i * finiteCuntzTransferSum s t n x =
      x * s i - t i * finiteCuntzTransferIter s t n x := by
  induction n with
  | zero => simp [finiteCuntzTransferSum]
  | succ n ih =>
    rw [finiteCuntzTransferSum_succ, add_mul, mul_add,
      finiteCuntzTransferIter_succ, finiteCuntzTransfer_mul s t hs]
    calc
      _ = (finiteCuntzTransferSum s t n x * s i -
          t i * finiteCuntzTransferSum s t n x) +
          t i * finiteCuntzTransferIter s t n x -
          t i * finiteCuntzTransfer s t (finiteCuntzTransferIter s t n x) := by abel
      _ = _ := by rw [ih]; abel

/-- Cesàro smoothing of the recursive intertwiner. -/
def finiteCuntzCesaro (s t : I → E) (n : ℕ) (x : E) : E :=
  ((n : ℝ) + 1)⁻¹ • finiteCuntzTransferSum s t n x

lemma finiteCuntzCesaro_intertwining (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (n : ℕ) (x : E) (i : I) :
    finiteCuntzCesaro s t n x * s i - t i * finiteCuntzCesaro s t n x =
      ((n : ℝ) + 1)⁻¹ • (x * s i - t i * finiteCuntzTransferIter s t n x) := by
  simp only [finiteCuntzCesaro, smul_mul_assoc, mul_smul_comm, ← smul_sub]
  rw [finiteCuntzTransferSum_intertwining s t hs]

lemma finiteCuntzCesaro_norm_le (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0) (n : ℕ) (x : E) :
    ‖finiteCuntzCesaro s t n x‖ ≤ ‖x‖ := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hsum : ‖finiteCuntzTransferSum s t n x‖ ≤ ((n : ℝ) + 1) * ‖x‖ := by
    calc
      _ ≤ ∑ k ∈ Finset.range (n + 1), ‖finiteCuntzTransferIter s t k x‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range (n + 1), ‖x‖ :=
        Finset.sum_le_sum fun k _ => finiteCuntzTransferIter_norm_le s t hs ht k x
      _ = _ := by simp [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [finiteCuntzCesaro, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le)]
  exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)).trans_eq (by rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul])

lemma finiteCuntzCesaro_intertwining_norm_le (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hsn : ∀ i, ‖s i‖ ≤ 1) (htn : ∀ i, ‖t i‖ ≤ 1) (n : ℕ) (x : E) (i : I) :
    ‖finiteCuntzCesaro s t n x * s i - t i * finiteCuntzCesaro s t n x‖ ≤
      (2 * ‖x‖) / ((n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hfirst : ‖x * s i‖ ≤ ‖x‖ :=
    (norm_mul_le _ _).trans (by simpa using mul_le_mul_of_nonneg_left (hsn i) (norm_nonneg x))
  have hlast : ‖t i * finiteCuntzTransferIter s t n x‖ ≤ ‖x‖ :=
    (norm_mul_le _ _).trans ((mul_le_mul (htn i)
      (finiteCuntzTransferIter_norm_le s t hs ht n x) (norm_nonneg _) zero_le_one).trans_eq
        (one_mul _))
  rw [finiteCuntzCesaro_intertwining s t hs, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hn.le)]
  calc
    _ ≤ ((n : ℝ) + 1)⁻¹ * (‖x‖ + ‖x‖) :=
      mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hfirst hlast))
        (inv_nonneg.mpr hn.le)
    _ = _ := by rw [div_eq_mul_inv]; ring

omit [DecidableEq I] in
/-- The transfer operator annihilates the unused source corner. -/
lemma finiteCuntzTransfer_mul_annihilator (s t : I → E) (x q : E)
    (hq : ∀ i, star (s i) * q = 0) : finiteCuntzTransfer s t x * q = 0 := by
  simp only [finiteCuntzTransfer, Finset.sum_mul, mul_assoc, hq, mul_zero, Finset.sum_const_zero]

omit [DecidableEq I] in
lemma finiteCuntzTransferSum_mul_annihilator (s t : I → E) (n : ℕ) (x q : E)
    (hq : ∀ i, star (s i) * q = 0) : finiteCuntzTransferSum s t n x * q = x * q := by
  induction n with
  | zero => simp [finiteCuntzTransferSum]
  | succ n ih =>
    rw [finiteCuntzTransferSum_succ, add_mul, ih, finiteCuntzTransferIter_succ,
      finiteCuntzTransfer_mul_annihilator s t _ q hq, add_zero]

omit [DecidableEq I] in
/-- In the unused source corner, smoothing retains only the scaled seed.
This exposes the boundary obstruction to a unitary normalization. -/
lemma finiteCuntzCesaro_mul_annihilator (s t : I → E) (n : ℕ) (x q : E)
    (hq : ∀ i, star (s i) * q = 0) :
    finiteCuntzCesaro s t n x * q = ((n : ℝ) + 1)⁻¹ • (x * q) := by
  rw [finiteCuntzCesaro, smul_mul_assoc, finiteCuntzTransferSum_mul_annihilator s t n x q hq]

omit [DecidableEq I] in
/-- A seed-one Cesàro mean stays far from every unitary when a nonzero
unused source corner survives. It is not a unitary half-flip witness. -/
lemma finiteCuntzCesaro_dist_unitary_lower (s t : I → E) (n : ℕ) (q : E)
    (hq : ∀ i, star (s i) * q = 0) (hq0 : q ≠ 0) (u : unitary E) :
    1 - ((n : ℝ) + 1)⁻¹ ≤ ‖(u : E) - finiteCuntzCesaro s t n 1‖ := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hqnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hmean : ‖finiteCuntzCesaro s t n 1 * q‖ = ((n : ℝ) + 1)⁻¹ * ‖q‖ := by
    rw [finiteCuntzCesaro_mul_annihilator s t n 1 q hq, one_mul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le)]
  have htriangle : ‖q‖ ≤
      ‖(u : E) - finiteCuntzCesaro s t n 1‖ * ‖q‖ + ((n : ℝ) + 1)⁻¹ * ‖q‖ := by
    calc
      _ = ‖(u : E) * q‖ := (CStarRing.norm_coe_unitary_mul u q).symm
      _ ≤ ‖((u : E) - finiteCuntzCesaro s t n 1) * q‖ +
          ‖finiteCuntzCesaro s t n 1 * q‖ := by
        simpa only [sub_mul, sub_add_cancel] using
          norm_add_le (((u : E) - finiteCuntzCesaro s t n 1) * q)
            (finiteCuntzCesaro s t n 1 * q)
      _ ≤ _ := add_le_add (norm_mul_le _ _) (le_of_eq hmean)
  by_contra! hbad
  have hpos := mul_pos (sub_pos.mpr hbad) hqnorm
  nlinarith only [htriangle, hpos]

/-- Unitary conjugation has exactly the same error as recursive intertwining. -/
lemma unitary_conjugation_error_eq (u : unitary E) (a b : E) :
    ‖(u : E) * a * star (u : E) - b‖ = ‖(u : E) * a - b * (u : E)‖ := by
  calc
    _ = ‖((u : E) * a - b * (u : E)) * star (u : E)‖ := by
      have hu : (u : E) * star (u : E) = 1 := u.property.2
      congr 1
      simp only [sub_mul, mul_assoc, hu, mul_one]
    _ = _ := by
      simpa only [Unitary.coe_star] using
        CStarRing.norm_mul_coe_unitary ((u : E) * a - b * (u : E)) (star u)

/-- A later unitary completion must control its distance from the recursive
intertwiner; the error cost of that replacement is at most twice the distance. -/
lemma unitary_conjugation_error_le (u : unitary E) (x a b : E)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖(u : E) * a * star (u : E) - b‖ ≤ 2 * ‖(u : E) - x‖ + ‖x * a - b * x‖ := by
  rw [unitary_conjugation_error_eq]
  have he : (u : E) * a - b * (u : E) =
      ((u : E) - x) * a + (x * a - b * x) + b * (x - (u : E)) := by noncomm_ring
  have hfirst : ‖((u : E) - x) * a‖ ≤ ‖(u : E) - x‖ :=
    (norm_mul_le _ _).trans (by simpa using mul_le_mul_of_nonneg_left ha (norm_nonneg _))
  have hlast : ‖b * (x - (u : E))‖ ≤ ‖(u : E) - x‖ := by
    calc
      _ ≤ ‖b‖ * ‖x - (u : E)‖ := norm_mul_le _ _
      _ ≤ 1 * ‖x - (u : E)‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = _ := by rw [one_mul, norm_sub_rev]
  rw [he]
  exact norm_add₃_le.trans ((add_le_add (add_le_add hfirst le_rfl) hlast).trans_eq (by ring))

/-- Swap the orthogonal initial and final spaces of a square-zero partial
isometry, and act identically on their common complement. -/
def partialIsometrySwap (a : E) : E :=
  a + star a + (1 - star a * a - a * star a)

/-- The chosen two-swap completion, with fixed initial support `p` and
spare isometry `r`. This is a polynomial in the partial intertwiner `v`. -/
def partialIsometryCompletion (r p v : E) : E :=
  partialIsometrySwap (v * star r) * partialIsometrySwap (r * p)

lemma partialIsometryCompletion_continuous (r p : E) :
    Continuous (partialIsometryCompletion r p) := by
  unfold partialIsometryCompletion partialIsometrySwap
  fun_prop

lemma partialIsometrySwap_sub (a b : E)
    (hi : star a * a = star b * b) (hf : a * star a = b * star b) :
    partialIsometrySwap a - partialIsometrySwap b = (a - b) + star (a - b) := by
  simp only [partialIsometrySwap, hi, hf, star_sub]
  abel

lemma partialIsometrySwap_sub_norm_le (a b : E)
    (hi : star a * a = star b * b) (hf : a * star a = b * star b) :
    ‖partialIsometrySwap a - partialIsometrySwap b‖ ≤ 2 * ‖a - b‖ := by
  rw [partialIsometrySwap_sub a b hi hf]
  calc
    _ ≤ ‖a - b‖ + ‖star (a - b)‖ := norm_add_le _ _
    _ = _ := by rw [norm_star]; ring

/-- On a fixed pair of support projections, the completion is 2-Lipschitz.
The fixed right swap is unitary, so it contributes no norm loss. -/
lemma partialIsometryCompletion_sub_norm_le [Nontrivial E] (r p v w : E)
    (hr : star r * r = 1) (hu : partialIsometrySwap (r * p) ∈ unitary E)
    (hi : star v * v = star w * w) (hf : v * star v = w * star w) :
    ‖partialIsometryCompletion r p v - partialIsometryCompletion r p w‖ ≤
      2 * ‖v - w‖ := by
  have hri : ‖r‖ = 1 := by
    have he := congrArg norm hr
    rw [CStarRing.norm_star_mul_self, norm_one] at he
    nlinarith [norm_nonneg r]
  have hi' : star (v * star r) * (v * star r) =
      star (w * star r) * (w * star r) := by
    simp only [star_mul, star_star]
    calc
      _ = r * (star v * v) * star r := by noncomm_ring
      _ = r * (star w * w) * star r := by rw [hi]
      _ = _ := by noncomm_ring
  have hf' : (v * star r) * star (v * star r) =
      (w * star r) * star (w * star r) := by
    simp only [star_mul, star_star]
    calc
      _ = v * (star r * r) * star v := by noncomm_ring
      _ = w * (star r * r) * star w := by simpa only [hr, mul_one] using hf
      _ = _ := by noncomm_ring
  rw [partialIsometryCompletion, partialIsometryCompletion, ← sub_mul,
    CStarRing.norm_mul_mem_unitary _ hu]
  calc
    _ ≤ 2 * ‖v * star r - w * star r‖ :=
      partialIsometrySwap_sub_norm_le _ _ hi' hf'
    _ = 2 * ‖(v - w) * star r‖ := by rw [sub_mul]
    _ ≤ 2 * (‖v - w‖ * ‖star r‖) := mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by norm_num)
    _ = _ := by rw [norm_star, hri, mul_one]

private lemma norm_add_star_of_square_zero (a : E) (ha : a * a = 0) :
    ‖a + star a‖ = ‖a‖ := by
  have hss : star a * star a = 0 := by
    simpa only [star_mul, star_zero] using congrArg star ha
  have hs : star (a + star a) = a + star a := by
    simp only [star_add, star_star, add_comm]
  have ho : (star a * a) * (a * star a) = 0 := by
    calc
      _ = star a * (a * a) * star a := by noncomm_ring
      _ = 0 := by rw [ha, mul_zero, zero_mul]
  have he : (a + star a) * (a + star a) = star a * a + a * star a := by
    noncomm_ring [ha, hss]
  have hn := CStarRing.norm_star_mul_self (x := a + star a)
  rw [hs, he, (IsSelfAdjoint.star_mul_self a).norm_add_eq_max
    (IsSelfAdjoint.mul_star_self a) ho, CStarRing.norm_star_mul_self,
    CStarRing.norm_self_mul_star, max_self] at hn
  nlinarith [norm_nonneg (a + star a), norm_nonneg a]

/-- With the common spare range orthogonal to both final supports, the
completion is actually nonexpansive: its varying part is an off-diagonal
selfadjoint corner, whose norm equals the norm of that corner. -/
lemma partialIsometryCompletion_sub_norm_le_one [Nontrivial E] (r p v w : E)
    (hr : star r * r = 1) (hu : partialIsometrySwap (r * p) ∈ unitary E)
    (hi : star v * v = star w * w) (hf : v * star v = w * star w)
    (hvr : star r * v = 0) (hwr : star r * w = 0) :
    ‖partialIsometryCompletion r p v - partialIsometryCompletion r p w‖ ≤
      ‖v - w‖ := by
  have hri : ‖r‖ = 1 := by
    have he := congrArg norm hr
    rw [CStarRing.norm_star_mul_self, norm_one] at he
    nlinarith [norm_nonneg r]
  have hi' : star (v * star r) * (v * star r) =
      star (w * star r) * (w * star r) := by
    simp only [star_mul, star_star]
    calc
      _ = r * (star v * v) * star r := by noncomm_ring
      _ = r * (star w * w) * star r := by rw [hi]
      _ = _ := by noncomm_ring
  have hf' : (v * star r) * star (v * star r) =
      (w * star r) * star (w * star r) := by
    simp only [star_mul, star_star]
    calc
      _ = v * (star r * r) * star v := by noncomm_ring
      _ = w * (star r * r) * star w := by simpa only [hr, mul_one] using hf
      _ = _ := by noncomm_ring
  have hd : (v * star r - w * star r) * (v * star r - w * star r) = 0 := by
    calc
      _ = (v - w) * (star r * v - star r * w) * star r := by noncomm_ring
      _ = 0 := by rw [hvr, hwr, sub_self, mul_zero, zero_mul]
  rw [partialIsometryCompletion, partialIsometryCompletion, ← sub_mul,
    CStarRing.norm_mul_mem_unitary _ hu, partialIsometrySwap_sub _ _ hi' hf',
    norm_add_star_of_square_zero _ hd, ← sub_mul]
  calc
    _ ≤ ‖v - w‖ * ‖star r‖ := norm_mul_le _ _
    _ = _ := by rw [norm_star, hri, mul_one]

lemma partialIsometrySwap_star (a : E) :
    star (partialIsometrySwap a) = partialIsometrySwap a := by
  simp only [partialIsometrySwap, star_add, star_sub, star_one, star_mul, star_star]
  abel

lemma partialIsometrySwap_sq (a : E) (ha : a * star a * a = a) (haa : a * a = 0) :
    partialIsometrySwap a * partialIsometrySwap a = 1 := by
  have ha' : a * (star a * a) = a := by simpa only [mul_assoc] using ha
  have hs : star a * a * star a = star a := by
    simpa only [star_mul, star_star, mul_assoc] using congrArg star ha
  have hs' : star a * (a * star a) = star a := by simpa only [mul_assoc] using hs
  have hss : star a * star a = 0 := by
    simpa only [star_mul, star_zero] using congrArg star haa
  have haa_right (x : E) : a * (a * x) = 0 := by
    rw [← mul_assoc, haa, zero_mul]
  have hss_right (x : E) : star a * (star a * x) = 0 := by
    rw [← mul_assoc, hss, zero_mul]
  unfold partialIsometrySwap
  noncomm_ring [ha, ha', hs, hs', haa, hss, haa_right, hss_right]

def partialIsometrySwapUnitary (a : E) (ha : a * star a * a = a) (haa : a * a = 0) :
    unitary E :=
  ⟨partialIsometrySwap a, by
    constructor <;> rw [partialIsometrySwap_star, partialIsometrySwap_sq a ha haa]⟩

lemma partialIsometrySwap_mul_initial (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) :
    partialIsometrySwap a * (star a * a) = a := by
  have ha' : a * (star a * a) = a := by simpa only [mul_assoc] using ha
  have hs : star a * a * star a = star a := by
    simpa only [star_mul, star_star, mul_assoc] using congrArg star ha
  have hs' : star a * (a * star a) = star a := by simpa only [mul_assoc] using hs
  have hss : star a * star a = 0 := by
    simpa only [star_mul, star_zero] using congrArg star haa
  have haa_right (x : E) : a * (a * x) = 0 := by
    rw [← mul_assoc, haa, zero_mul]
  have hss_right (x : E) : star a * (star a * x) = 0 := by
    rw [← mul_assoc, hss, zero_mul]
  unfold partialIsometrySwap
  noncomm_ring [ha, ha', hs, hs', haa, hss, haa_right, hss_right]

lemma partialIsometrySwap_isometry_projection_mem (r p : E)
    (hr : star r * r = 1) (hp : star p = p) (hpp : p * p = p)
    (hpr : p * r = 0) : partialIsometrySwap (r * p) ∈ unitary E := by
  have ha : (r * p) * star (r * p) * (r * p) = r * p := by
    rw [star_mul, hp]
    calc
      _ = r * (p * p) * (star r * r) * p := by noncomm_ring
      _ = _ := by rw [hpp, hr, mul_one, mul_assoc, hpp]
  have haa : (r * p) * (r * p) = 0 := by
    calc
      _ = r * (p * r) * p := by noncomm_ring
      _ = 0 := by rw [hpr]; simp
  exact (partialIsometrySwapUnitary (r * p) ha haa).property

/-- A selfadjoint unitary belongs to the identity path component. The two
short paths run through its scalar rotation by `I`. -/
lemma selfadjoint_unitary_joined_one [Nontrivial E] (u : unitary E)
    (hu : star (u : E) = (u : E)) : Joined (1 : unitary E) u := by
  have hI : Complex.I ∈ unitary ℂ := by constructor <;> simp
  let v : unitary E := ⟨Complex.I • (u : E), Unitary.smul_mem_of_mem hI u.property⟩
  have huu : (u : E) * (u : E) = 1 := by
    simpa only [hu] using Unitary.coe_star_mul_self u
  have hsq1 : star ((v : E) - 1) * ((v : E) - 1) = (2 : ℂ) • (1 : E) := by
    change star (Complex.I • (u : E) - 1) * (Complex.I • (u : E) - 1) = _
    simp only [star_sub, star_smul, star_one, Complex.star_def, Complex.conj_I, hu, sub_mul, mul_sub,
      smul_mul_assoc, mul_smul_comm, mul_one, one_mul, huu]
    module_nf; norm_num [Complex.I_sq]
  have hnorm1 : ‖(v : E) - 1‖ < 2 := by
    have h := congrArg norm hsq1
    rw [CStarRing.norm_star_mul_self, norm_smul, norm_one] at h
    norm_num at h
    nlinarith [norm_nonneg ((v : E) - 1)]
  have hsq2 : star ((u : E) - v) * ((u : E) - v) = (2 : ℂ) • (1 : E) := by
    change star ((u : E) - Complex.I • (u : E)) * ((u : E) - Complex.I • (u : E)) = _
    simp only [star_sub, star_smul, Complex.star_def, Complex.conj_I, hu, sub_mul, mul_sub,
      smul_mul_assoc, mul_smul_comm, huu]
    module_nf; norm_num [Complex.I_sq]
  have hnorm2 : ‖(u : E) - v‖ < 2 := by
    have h := congrArg norm hsq2
    rw [CStarRing.norm_star_mul_self, norm_smul, norm_one] at h
    norm_num at h
    nlinarith [norm_nonneg ((u : E) - v)]
  exact (Unitary.joined 1 v hnorm1).trans (Unitary.joined v u hnorm2)

lemma partialIsometrySwapUnitary_joined [Nontrivial E] (a : E)
    (ha : a * star a * a = a) (haa : a * a = 0) :
    Joined (1 : unitary E) (partialIsometrySwapUnitary a ha haa) :=
  selfadjoint_unitary_joined_one _ (partialIsometrySwap_star a)

/-- One isometry in the common complement completes a partial isometry to a
unitary in the identity component. This does not assert recursive invariance. -/
lemma exists_explicit_connected_unitary_extension [Nontrivial E] (v r : E)
    (hv : v * star v * v = v) (hr : star r * r = 1)
    (hpr : (star v * v) * r = 0) (hqr : (v * star v) * r = 0) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (u : E) = partialIsometryCompletion r (star v * v) v ∧
      (u : E) * (star v * v) = v := by
  let p := star v * v
  let a := r * p
  let b := v * star r
  have hv' : v * (star v * v) = v := by simpa only [mul_assoc] using hv
  have hpp : p * p = p := by
    dsimp only [p]
    calc
      _ = star v * (v * star v * v) := by noncomm_ring
      _ = _ := by rw [hv]
  have hpstar : star p = p := by simp only [p, star_mul, star_star]
  have ha : a * star a * a = a := by
    dsimp only [a]
    rw [star_mul, hpstar]
    calc
      _ = r * (p * p) * (star r * r) * p := by noncomm_ring
      _ = _ := by rw [hpp, hr, mul_one, mul_assoc, hpp]
  have haa : a * a = 0 := by
    dsimp only [a]
    calc
      _ = r * (p * r) * p := by noncomm_ring
      _ = 0 := by rw [hpr]; simp
  have hb : b * star b * b = b := by
    dsimp only [b]
    rw [star_mul, star_star]
    calc
      _ = v * (star r * r) * star v * v * star r := by noncomm_ring
      _ = _ := by rw [hr, mul_one, hv]
  have hrv : star r * v = 0 := by
    have hz : star r * (v * star v) = 0 := by
      simpa only [star_mul, star_star, star_zero] using congrArg star hqr
    calc
      _ = star r * (v * star v * v) := by rw [hv]
      _ = 0 := by rw [← mul_assoc, hz, zero_mul]
  have hbb : b * b = 0 := by
    dsimp only [b]
    calc
      _ = v * (star r * v) * star r := by noncomm_ring
      _ = 0 := by rw [hrv]; simp
  have hba : (star b * b) * a = a := by
    dsimp only [b, a]
    rw [star_mul, star_star]
    calc
      _ = r * p * (star r * r) * p := by dsimp only [p]; noncomm_ring
      _ = _ := by rw [hr, mul_one, mul_assoc, hpp]
  let ua := partialIsometrySwapUnitary a ha haa
  let ub := partialIsometrySwapUnitary b hb hbb
  have hj : Joined (1 : unitary E) (ub * ua) := by
    simpa only [one_mul] using (partialIsometrySwapUnitary_joined b hb hbb).mul
      (partialIsometrySwapUnitary_joined a ha haa)
  refine ⟨ub * ua, hj, rfl, ?_⟩
  change (partialIsometrySwap b * partialIsometrySwap a) * p = v
  have hsa : partialIsometrySwap a * p = a := by
    have he : star a * a = p := by
      dsimp only [a]
      rw [star_mul, hpstar]
      calc
        _ = p * (star r * r) * p := by noncomm_ring
        _ = p := by rw [hr, mul_one, hpp]
    rw [← he, partialIsometrySwap_mul_initial a ha haa]
  rw [mul_assoc, hsa]
  calc
    _ = partialIsometrySwap b * ((star b * b) * a) := by rw [hba]
    _ = (partialIsometrySwap b * (star b * b)) * a := by noncomm_ring
    _ = b * a := by rw [partialIsometrySwap_mul_initial b hb hbb]
    _ = v := by
      dsimp only [b, a]
      calc
        _ = v * (star r * r) * p := by noncomm_ring
        _ = v := by rw [hr, mul_one]; exact hv'

/-- Forgetting the explicit formula recovers the usual extension statement. -/
lemma exists_connected_unitary_extension [Nontrivial E] (v r : E)
    (hv : v * star v * v = v) (hr : star r * r = 1)
    (hpr : (star v * v) * r = 0) (hqr : (v * star v) * r = 0) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧ (u : E) * (star v * v) = v := by
  obtain ⟨u, hu, _, he⟩ := exists_explicit_connected_unitary_extension v r hv hr hpr hqr
  exact ⟨u, hu, he⟩

/-- A continuous family of partial intertwiners with fixed initial support
has a continuous family of connected unitary extensions given by the same
polynomial formula. No local choice of unitaries is needed. -/
lemma exists_continuous_connected_unitary_extensions {X : Type*} [TopologicalSpace X]
    [Nontrivial E] (v : X → E) (r p : E) (hvcont : Continuous v)
    (hv : ∀ x, v x * star (v x) * v x = v x)
    (hp : ∀ x, star (v x) * v x = p) (hr : star r * r = 1)
    (hpr : p * r = 0) (hqr : ∀ x, (v x * star (v x)) * r = 0) :
    ∃ u : X → unitary E, Continuous u ∧ ∀ x,
      Joined (1 : unitary E) (u x) ∧
      (u x : E) = partialIsometryCompletion r p (v x) ∧ (u x : E) * p = v x := by
  have hx (x : X) : ∃ z : unitary E, Joined (1 : unitary E) z ∧
      (z : E) = partialIsometryCompletion r p (v x) ∧ (z : E) * p = v x := by
    simpa only [hp x] using exists_explicit_connected_unitary_extension
      (v x) r (hv x) hr (by rw [hp x]; exact hpr) (hqr x)
  have hmem (x : X) : partialIsometryCompletion r p (v x) ∈ unitary E := by
    obtain ⟨z, _, hz, _⟩ := hx x
    rw [← hz]
    exact z.property
  let u (x : X) : unitary E := ⟨partialIsometryCompletion r p (v x), hmem x⟩
  refine ⟨u, ((partialIsometryCompletion_continuous r p).comp hvcont).subtype_mk hmem, ?_⟩
  intro x
  obtain ⟨z, hz, hze, hzp⟩ := hx x
  have he : u x = z := Subtype.ext hze.symm
  exact ⟨he.symm ▸ hz, rfl, he.symm ▸ hzp⟩

omit [DecidableEq I] in
lemma finiteCuntzTransfer_star (s t : I → E) (x : E) :
    star (finiteCuntzTransfer s t x) = finiteCuntzTransfer t s (star x) := by
  simp only [finiteCuntzTransfer, star_sum, star_mul, star_star, mul_assoc]

/-- Complete one recursive step to an actual connected unitary. The right
hand side retains the previous unitary `w`; it is not a conjugacy assertion. -/
lemma exists_connected_transfer_step [Nontrivial E] (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (r : E) (hr : star r * r = 1)
    (hsr : ∀ i, star (s i) * r = 0) (htr : ∀ i, star (t i) * r = 0)
    (w : unitary E) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      ∀ i, (u : E) * s i = t i * (w : E) := by
  let v := finiteCuntzTransfer s t (w : E)
  let p := ∑ i, s i * star (s i)
  let q := ∑ i, t i * star (t i)
  have hp : star v * v = p := by
    dsimp only [v]
    rw [finiteCuntzTransfer_star_mul s t ht]
    simp only [Unitary.coe_star_mul_self, mul_one]
    rfl
  have hq : v * star v = q := by
    dsimp only [v]
    rw [finiteCuntzTransfer_star]
    have he := finiteCuntzTransfer_star_mul t s hs (star (w : E))
    rw [finiteCuntzTransfer_star, star_star] at he
    simpa only [Unitary.mul_star_self_of_mem w.property, mul_one] using he
  have hvp : v * p = v := by
    dsimp only [p, v]
    simp only [Finset.mul_sum, ← mul_assoc, finiteCuntzTransfer_mul s t hs]
    rfl
  have hv : v * star v * v = v := by rw [mul_assoc, hp, hvp]
  have hpr : (star v * v) * r = 0 := by
    rw [hp]
    simp only [p, Finset.sum_mul, mul_assoc, hsr, mul_zero, Finset.sum_const_zero]
  have hqr : (v * star v) * r = 0 := by
    rw [hq]
    simp only [q, Finset.sum_mul, mul_assoc, htr, mul_zero, Finset.sum_const_zero]
  obtain ⟨u, hu, huv⟩ := exists_connected_unitary_extension v r hv hr hpr hqr
  refine ⟨u, hu, ?_⟩
  intro i
  have hpi : p * s i = s i := by
    simp only [p, Finset.sum_mul, mul_assoc, hs, mul_ite, mul_one, mul_zero]
    simp
  calc
    (u : E) * s i = (u : E) * (p * s i) := by rw [hpi]
    _ = ((u : E) * (star v * v)) * s i := by rw [hp, mul_assoc]
    _ = v * s i := by rw [huv]
    _ = t i * (w : E) := finiteCuntzTransfer_mul s t hs _ i

/-- Completing each transfer in a continuous family yields a continuous
family of connected unitaries. The completion does not increase the
norm variation of the preceding unitaries. This applies in particular
to any path of preceding unitaries, without claiming a fixed point. -/
lemma exists_continuous_connected_transfer_steps {X : Type*} [TopologicalSpace X]
    [Nontrivial E] (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (r : E) (hr : star r * r = 1)
    (hsr : ∀ i, star (s i) * r = 0) (htr : ∀ i, star (t i) * r = 0)
    (w : X → unitary E) (hw : Continuous w) :
    ∃ u : X → unitary E, Continuous u ∧
      (∀ x, Joined (1 : unitary E) (u x) ∧
        ∀ i, (u x : E) * s i = t i * (w x : E)) ∧
      ∀ x y, ‖(u x : E) - u y‖ ≤ ‖(w x : E) - w y‖ := by
  let v (x : X) := finiteCuntzTransfer s t (w x : E)
  let p := ∑ i, s i * star (s i)
  let q := ∑ i, t i * star (t i)
  have hp (x : X) : star (v x) * v x = p := by
    dsimp only [v]
    rw [finiteCuntzTransfer_star_mul s t ht]
    simp only [Unitary.coe_star_mul_self, mul_one]
    rfl
  have hq (x : X) : v x * star (v x) = q := by
    dsimp only [v]
    rw [finiteCuntzTransfer_star]
    have he := finiteCuntzTransfer_star_mul t s hs (star (w x : E))
    rw [finiteCuntzTransfer_star, star_star] at he
    simpa only [Unitary.mul_star_self_of_mem (w x).property, mul_one] using he
  have hvp (x : X) : v x * p = v x := by
    dsimp only [p, v]
    simp only [Finset.mul_sum, ← mul_assoc, finiteCuntzTransfer_mul s t hs]
    rfl
  have hv (x : X) : v x * star (v x) * v x = v x := by
    rw [mul_assoc, hp x, hvp x]
  have hpr : p * r = 0 := by
    simp only [p, Finset.sum_mul, mul_assoc, hsr, mul_zero, Finset.sum_const_zero]
  have hqr (x : X) : (v x * star (v x)) * r = 0 := by
    rw [hq x]
    simp only [q, Finset.sum_mul, mul_assoc, htr, mul_zero, Finset.sum_const_zero]
  have hrv (x : X) : star r * v x = 0 := by
    have hz : star r * (v x * star (v x)) = 0 := by
      simpa only [star_mul, star_star, star_zero] using congrArg star (hqr x)
    calc
      _ = star r * (v x * star (v x) * v x) := by rw [hv x]
      _ = 0 := by rw [← mul_assoc, hz, zero_mul]
  have hvcont : Continuous v :=
    (finiteCuntzTransfer_continuous s t).comp (continuous_subtype_val.comp hw)
  obtain ⟨u, hu, he⟩ := exists_continuous_connected_unitary_extensions v r p
    hvcont hv hp hr hpr hqr
  refine ⟨u, hu, ?_, ?_⟩
  · intro x
    refine ⟨(he x).1, ?_⟩
    intro i
    have hpi : p * s i = s i := by
      simp only [p, Finset.sum_mul, mul_assoc, hs, mul_ite, mul_one, mul_zero]
      simp
    calc
      (u x : E) * s i = (u x : E) * (p * s i) := by rw [hpi]
      _ = ((u x : E) * p) * s i := by rw [mul_assoc]
      _ = v x * s i := by rw [(he x).2.2]
      _ = t i * (w x : E) := finiteCuntzTransfer_mul s t hs _ i
  · intro x y
    have hpstar : star p = p := by
      simp only [p, star_sum, star_mul, star_star]
    have hpp : p * p = p := by
      rw [← hp x]
      calc
        _ = star (v x) * (v x * star (v x) * v x) := by noncomm_ring
        _ = _ := by rw [hv x]
    have hswap := partialIsometrySwap_isometry_projection_mem r p hr hpstar hpp hpr
    rw [(he x).2.1, (he y).2.1]
    exact (partialIsometryCompletion_sub_norm_le_one r p (v x) (v y) hr hswap
      ((hp x).trans (hp y).symm) ((hq x).trans (hq y).symm) (hrv x) (hrv y)).trans
        (finiteCuntzTransfer_sub_norm_le s t hs ht _ _)

/-- Iterating the continuous completion produces a tower of unitary paths.
Adjacent paths match at their endpoints, and adjacent levels satisfy exact
recursive intertwining. The estimate controls each finite part of the tower;
it does not assert that consecutive levels become close. -/
lemma exists_continuous_transfer_path_tower [Nontrivial E] (s t : I → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (r : E) (hr : star r * r = 1)
    (hsr : ∀ i, star (s i) * r = 0) (htr : ∀ i, star (t i) * r = 0) :
    ∃ u : ℕ → unitInterval → unitary E,
      (∀ n, Continuous (u n)) ∧ u 0 0 = 1 ∧
      (∀ n, u n 1 = u (n + 1) 0) ∧
      (∀ n x i, (u (n + 1) x : E) * s i = t i * (u n x : E)) ∧
      ∀ n x y, ‖(u n x : E) - u n y‖ ≤ ‖(u 0 x : E) - u 0 y‖ := by
  obtain ⟨f, hfcont, hf, hfnorm⟩ := exists_continuous_connected_transfer_steps
    s t hs ht r hr hsr htr (id : unitary E → unitary E) continuous_id
  let γ : Path (1 : unitary E) (f 1) := (hf 1).1.somePath
  let u (n : ℕ) (x : unitInterval) := f^[n] (γ x)
  have hnorm (n : ℕ) (a b : unitary E) :
      ‖(f^[n] a : E) - f^[n] b‖ ≤ ‖(a : E) - b‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (hfnorm _ _).trans ih
  refine ⟨u, fun n => (hfcont.iterate n).comp γ.continuous, ?_, ?_, ?_, ?_⟩
  · exact γ.source
  · intro n
    change f^[n] (γ 1) = f^[n + 1] (γ 0)
    rw [γ.target, γ.source, Function.iterate_succ_apply]
  · intro n x i
    change (f^[n + 1] (γ x) : E) * s i = t i * (f^[n] (γ x) : E)
    rw [Function.iterate_succ_apply']
    exact (hf _).2 i
  · intro n x y
    exact hnorm n (γ x) (γ y)

/-- For the two tensor-factor Cuntz families, one unused product isometry
lies in the common complement of the first `N` ranges. -/
lemma exists_connected_infinite_transfer_step [Nontrivial E] (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (hc : ∀ i j, Commute (star (t i)) (s j)) (N : ℕ) (w : unitary E) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧
      ∀ i < N, (u : E) * s i = t i * (w : E) := by
  let r := s N * t N
  have hr : star r * r = 1 := by
    dsimp only [r]
    rw [star_mul]
    calc
      _ = star (t N) * (star (s N) * s N) * t N := by noncomm_ring
      _ = 1 := by rw [hs, ite_eq_left rfl, mul_one, ht, ite_eq_left rfl]
  have hsr (i : Fin N) : star (s i) * r = 0 := by
    dsimp only [r]
    rw [← mul_assoc, hs, ite_eq_right (Nat.ne_of_lt i.isLt), zero_mul]
  have htr (i : Fin N) : star (t i) * r = 0 := by
    dsimp only [r]
    rw [← mul_assoc, (hc i N).eq, mul_assoc, ht,
      ite_eq_right (Nat.ne_of_lt i.isLt), mul_zero]
  have hsFin (i j : Fin N) : star (s i) * s j = if i = j then 1 else 0 := by
    simpa only [Fin.ext_iff] using hs i j
  have htFin (i j : Fin N) : star (t i) * t j = if i = j then 1 else 0 := by
    simpa only [Fin.ext_iff] using ht i j
  obtain ⟨u, hu, h⟩ := exists_connected_transfer_step
    (fun i : Fin N => s i) (fun i : Fin N => t i) hsFin htFin r hr hsr htr w
  exact ⟨u, hu, fun i hi => h ⟨i, hi⟩⟩

end WeakPureInfiniteness

end

end OAI
