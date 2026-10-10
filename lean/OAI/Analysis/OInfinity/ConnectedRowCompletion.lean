import OAI.Analysis.OInfinity.FixedComplementPaths

namespace OAI

/-! # Connected choices of finite binary completions

Three orthogonal buffer isometries let two finite rows with actual unused
isometries be matched on the left by a connected unitary. Applying this to
the finite shift equations gives a full binary completion with a connected
left cocycle relative to a prescribed reference row. Left matching alone
is not an assertion of conjugacy.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

private lemma connectedRow_product_gram (a b : E)
    (ha : star a * a = 1) (hb : star b * b = 1) :
    star (a * b) * (a * b) = 1 := by
  rw [star_mul]
  calc
    _ = star b * (star a * a) * b := by noncomm_ring
    _ = 1 := by rw [ha, mul_one, hb]

/-- Only the two displayed commutations with the unused isometries are
needed. The buffer need not commute with the tested finite rows. -/
lemma exists_connected_finite_row_leftMatch [Nontrivial E]
    {n : ℕ} (x y : Fin n → E)
    (hx : ∀ i j, star (x i) * x j = if i = j then 1 else 0)
    (hy : ∀ i j, star (y i) * y j = if i = j then 1 else 0)
    (e f : E) (he : star e * e = 1) (hf : star f * f = 1)
    (hxe : ∀ i, star (x i) * e = 0) (hyf : ∀ i, star (y i) * f = 0)
    (r : Fin 3 → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (her : Commute (star (r 0)) e) (hfr : Commute (star (r 1)) f) :
    ∃ u : unitary E, Joined (1 : unitary E) u ∧ ∀ i, (u : E) * x i = y i := by
  have hr0 : star (r 0) * r 0 = 1 := by simpa only [ite_true] using hr 0 0
  have hr1 : star (r 1) * r 1 = 1 := by simpa only [ite_true] using hr 1 1
  have hr2 : star (r 2) * r 2 = 1 := by simpa only [ite_true] using hr 2 2
  let X : Fin n → E := fun i => r 0 * x i
  let Y : Fin n → E := fun i => r 1 * y i
  have hX (i j : Fin n) : star (X i) * X j = if i = j then 1 else 0 := by
    change star (r 0 * x i) * (r 0 * x j) = _
    rw [star_mul]
    calc
      _ = star (x i) * (star (r 0) * r 0) * x j := by noncomm_ring
      _ = _ := by rw [hr0, mul_one, hx]
  have hY (i j : Fin n) : star (Y i) * Y j = if i = j then 1 else 0 := by
    change star (r 1 * y i) * (r 1 * y j) = _
    rw [star_mul]
    calc
      _ = star (y i) * (star (r 1) * r 1) * y j := by noncomm_ring
      _ = _ := by rw [hr1, mul_one, hy]
  have hxes (i : Fin n) : star (x i) * (e * r 1) = 0 := by
    rw [← mul_assoc, hxe, zero_mul]
  have hXes (i : Fin n) : star (X i) * (e * r 1) = 0 := by
    change star (r 0 * x i) * (e * r 1) = 0
    rw [star_mul]
    calc
      _ = star (x i) * (star (r 0) * e) * r 1 := by noncomm_ring
      _ = 0 := by rw [her.eq, ← mul_assoc, hxe, zero_mul, zero_mul]
  obtain ⟨u, hu, hux⟩ := exists_connected_transfer_step x X hx hX (e * r 1)
    (connectedRow_product_gram e (r 1) he hr1) hxes hXes 1
  have hux' (i : Fin n) : (u : E) * x i = X i := by
    simpa only [OneMemClass.coe_one, mul_one] using hux i
  have hyfs (i : Fin n) : star (y i) * (f * r 0) = 0 := by
    rw [← mul_assoc, hyf, zero_mul]
  have hYfs (i : Fin n) : star (Y i) * (f * r 0) = 0 := by
    change star (r 1 * y i) * (f * r 0) = 0
    rw [star_mul]
    calc
      _ = star (y i) * (star (r 1) * f) * r 0 := by noncomm_ring
      _ = 0 := by rw [hfr.eq, ← mul_assoc, hyf, zero_mul, zero_mul]
  obtain ⟨v, hv, hvy⟩ := exists_connected_transfer_step y Y hy hY (f * r 0)
    (connectedRow_product_gram f (r 0) hf hr0) hyfs hYfs 1
  have hvy' (i : Fin n) : (v : E) * y i = Y i := by
    simpa only [OneMemClass.coe_one, mul_one] using hvy i
  have hXr (i : Fin n) : star (X i) * r 2 = 0 := by
    change star (r 0 * x i) * r 2 = 0
    rw [star_mul, mul_assoc, hr]
    simp only [show (0 : Fin 3) ≠ 2 by decide, ite_false, mul_zero]
  have hYr (i : Fin n) : star (Y i) * r 2 = 0 := by
    change star (r 1 * y i) * r 2 = 0
    rw [star_mul, mul_assoc, hr]
    simp only [show (1 : Fin 3) ≠ 2 by decide, ite_false, mul_zero]
  obtain ⟨z, hz, hzX⟩ := exists_connected_transfer_step X Y hX hY (r 2) hr2 hXr hYr 1
  have hzX' (i : Fin n) : (z : E) * X i = Y i := by
    simpa only [OneMemClass.coe_one, mul_one] using hzX i
  have hvstar : Joined (1 : unitary E) (star v) := by
    simpa only [star_one] using hv.map (continuous_star : Continuous (star : unitary E → unitary E))
  refine ⟨star v * z * u, ?_, fun i => ?_⟩
  · simpa only [one_mul] using (hvstar.mul hz).mul hu
  · change (star (v : E) * (z : E) * (u : E)) * x i = y i
    rw [mul_assoc, mul_assoc, hux', hzX', ← hvy', ← mul_assoc, v.property.1, one_mul]

/-- The tested finite row is the initial binary prefix, and the full
binary row has a connected left cocycle to the specified reference. -/
lemma exists_connected_binary_row_completion [Nontrivial E]
    {n : ℕ} (x : Fin (n + 1) → E)
    (hx : ∀ i j, star (x i) * x j = if i = j then 1 else 0)
    (e : E) (he : star e * e = 1) (hxe : ∀ i, star (x i) * e = 0)
    (b : Fin 2 → E)
    (hb : ∀ i j, star (b i) * b j = if i = j then 1 else 0)
    (hbs : (∑ i, b i * star (b i)) = 1)
    (r : Fin 3 → E)
    (hr : ∀ i j, star (r i) * r j = if i = j then 1 else 0)
    (her : Commute (star (r 0)) e)
    (hfr : Commute (star (r 1)) (b 0 * e)) :
    ∃ a : Fin 2 → E, ∃ u : unitary E, Joined (1 : unitary E) u ∧
      (∀ i j, star (a i) * a j = if i = j then 1 else 0) ∧
      (∑ i, a i * star (a i)) = 1 ∧
      (∀ i : Fin (n + 1), a 0 ^ (i : ℕ) * a 1 = x i) ∧
      ∀ j, (u : E) * a j = b j := by
  let y : Fin (n + 1) → E := Fin.cases (b 1) (fun i : Fin n => b 0 * x i.castSucc)
  have hb0 : star (b 0) * b 0 = 1 := by simpa only [ite_true] using hb 0 0
  have hb1 : star (b 1) * b 1 = 1 := by simpa only [ite_true] using hb 1 1
  have hb01 : star (b 0) * b 1 = 0 := by simpa only [ite_false, Fin.zero_ne_one] using hb 0 1
  have hb10 : star (b 1) * b 0 = 0 := by
    simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false] using hb 1 0
  have hy (i j : Fin (n + 1)) : star (y i) * y j = if i = j then 1 else 0 := by
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [y, Fin.cases_zero, ite_true] using hb1
    · simp only [y, Fin.cases_zero, Fin.cases_succ, (Fin.succ_ne_zero j).symm, ite_false]
      rw [← mul_assoc, hb10, zero_mul]
    · simp only [y, Fin.cases_zero, Fin.cases_succ, Fin.succ_ne_zero, ite_false, star_mul]
      rw [mul_assoc, hb01, mul_zero]
    · simp only [y, Fin.cases_succ, star_mul]
      calc
        _ = star (x i.castSucc) * (star (b 0) * b 0) * x j.castSucc := by noncomm_ring
        _ = _ := by rw [hb0, mul_one, hx]; simp
  have hyf (i : Fin (n + 1)) : star (y i) * (b 0 * e) = 0 := by
    refine Fin.cases ?_ (fun i => ?_) i
    · change star (b 1) * (b 0 * e) = 0
      rw [← mul_assoc, hb10, zero_mul]
    · change star (b 0 * x i.castSucc) * (b 0 * e) = 0
      rw [star_mul]
      calc
        _ = star (x i.castSucc) * (star (b 0) * b 0) * e := by noncomm_ring
        _ = 0 := by rw [hb0, mul_one, hxe]
  obtain ⟨u, hu, hux⟩ := exists_connected_finite_row_leftMatch x y hx hy e (b 0 * e)
    he (connectedRow_product_gram (b 0) e hb0 he) hxe hyf r hr her hfr
  let a : Fin 2 → E := fun j => star (u : E) * b j
  have huc : ∀ j, (u : E) * a j = b j := by
    intro j
    change (u : E) * (star (u : E) * b j) = b j
    rw [← mul_assoc, u.property.2, one_mul]
  have hag (i j : Fin 2) : star (a i) * a j = if i = j then 1 else 0 := by
    change star (star (u : E) * b i) * (star (u : E) * b j) = _
    rw [star_mul, star_star]
    calc
      _ = star (b i) * ((u : E) * star (u : E)) * b j := by noncomm_ring
      _ = _ := by rw [u.property.2, mul_one, hb]
  have has : (∑ i, a i * star (a i)) = 1 := by
    simp only [a, star_mul, star_star]
    calc
      _ = star (u : E) * (∑ i, b i * star (b i)) * (u : E) := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = 1 := by rw [hbs, mul_one, u.property.1]
  have ha1 : a 1 = x 0 := by
    have h := hux 0
    change (u : E) * x 0 = b 1 at h
    calc
      _ = star (u : E) * ((u : E) * x 0) := by rw [h]
      _ = x 0 := by rw [← mul_assoc, u.property.1, one_mul]
  have hast (i : Fin n) : a 0 * x i.castSucc = x i.succ := by
    have h := hux i.succ
    change (u : E) * x i.succ = b 0 * x i.castSucc at h
    change (star (u : E) * b 0) * x i.castSucc = _
    rw [mul_assoc, ← h, ← mul_assoc, u.property.1, one_mul]
  refine ⟨a, u, hu, hag, has, ?_, huc⟩
  intro i
  induction i using Fin.induction with
  | zero => simpa only [Fin.val_zero, pow_zero, one_mul] using ha1
  | succ i ih =>
    change a 0 ^ (i : ℕ) * a 1 = x i.castSucc at ih
    change a 0 ^ ((i : ℕ) + 1) * a 1 = x i.succ
    rw [pow_succ', mul_assoc, ih, hast]

end WeakPureInfiniteness

end

end OAI
