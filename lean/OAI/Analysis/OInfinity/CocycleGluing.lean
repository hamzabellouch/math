import OAI.Analysis.OInfinity.RelativeCocycle

namespace OAI

/-! # Finite cocycle coefficients with an exact terminal seam

A path from `V_N` to `1` gives coefficients `V_k α^[k](p(k/N))`.
The zeroth and terminal coefficients agree exactly, while consecutive
coefficients satisfy the cocycle equation up to `L/N`. These are the
coefficients for finite Rohlin gluing; commutation with the gluing
projections is a separate requirement.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma binarySplitHom_sub_norm_le (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) (u v : unitary E) :
    ‖(binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
        (by simpa using hs 1 1) (by simpa using hs 0 1) u : E) -
      (binarySplitHom (s 0) (s 1) (by simpa using hs 0 0)
        (by simpa using hs 1 1) (by simpa using hs 0 1) v : E)‖ ≤ ‖(u : E) - v‖ := by
  rw [binarySplitHom_coe s hs hsum, binarySplitHom_coe s hs hsum]
  exact finiteCuntzTransfer_sub_norm_le s s hs hs u v

lemma unitaryHom_iterate_sub_norm_le (α : unitary E →* unitary E)
    (hα : ∀ u v : unitary E, ‖(α u : E) - α v‖ ≤ ‖(u : E) - v‖)
    (n : ℕ) (u v : unitary E) :
    ‖((α^[n]) u : E) - (α^[n]) v‖ ≤ ‖(u : E) - v‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (hα _ _).trans ih

lemma unitaryHom_iterate_one (α : unitary E →* unitary E) (n : ℕ) :
    (α^[n]) 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_one]

def finiteCocycleCoefficient (α : unitary E →* unitary E) (w : unitary E)
    {N : ℕ} (p : Path (finiteGroupCocycle α w N) 1) (k : ℕ) (t : unitInterval) :
    unitary E := finiteGroupCocycle α w k * (α^[k]) (p t)

lemma finiteCocycleCoefficient_zero (α : unitary E →* unitary E) (w : unitary E)
    {N : ℕ} (p : Path (finiteGroupCocycle α w N) 1) :
    finiteCocycleCoefficient α w p 0 0 = finiteGroupCocycle α w N := by
  simp only [finiteCocycleCoefficient, finiteGroupCocycle, Function.iterate_zero,
    id_eq, one_mul, p.source]

lemma finiteCocycleCoefficient_terminal (α : unitary E →* unitary E) (w : unitary E)
    {N : ℕ} (p : Path (finiteGroupCocycle α w N) 1) :
    finiteCocycleCoefficient α w p N 1 = finiteGroupCocycle α w N := by
  rw [finiteCocycleCoefficient, p.target, unitaryHom_iterate_one, mul_one]

lemma finiteCocycleCoefficient_step (α : unitary E →* unitary E) (w : unitary E)
    {N : ℕ} (p : Path (finiteGroupCocycle α w N) 1) (k : ℕ) (t : unitInterval) :
    w * α (finiteCocycleCoefficient α w p k t) =
      finiteCocycleCoefficient α w p (k + 1) t := by
  simp only [finiteCocycleCoefficient, map_mul, finiteGroupCocycle,
    Function.iterate_succ_apply', mul_assoc]

lemma finiteCocycleCoefficient_step_norm (α : unitary E →* unitary E) (w : unitary E)
    (hα : ∀ u v : unitary E, ‖(α u : E) - α v‖ ≤ ‖(u : E) - v‖)
    {N : ℕ} (p : Path (finiteGroupCocycle α w N) 1)
    (L : ℝ) (hp : ∀ a b, ‖(p a : E) - p b‖ ≤ L * |(a : ℝ) - b|)
    (k : ℕ) (a b : unitInterval) :
    ‖(w : E) * α (finiteCocycleCoefficient α w p k a) -
      finiteCocycleCoefficient α w p (k + 1) b‖ ≤ L * |(a : ℝ) - b| := by
  change ‖(↑(w * α (finiteCocycleCoefficient α w p k a)) : E) -
    (finiteCocycleCoefficient α w p (k + 1) b : E)‖ ≤ _
  rw [finiteCocycleCoefficient_step]
  change ‖(↑(finiteGroupCocycle α w (k + 1)) : E) * ((α^[k + 1]) (p a) : E) -
    (↑(finiteGroupCocycle α w (k + 1)) : E) * ((α^[k + 1]) (p b) : E)‖ ≤ _
  rw [← mul_sub, CStarRing.norm_coe_unitary_mul]
  exact (unitaryHom_iterate_sub_norm_le α hα (k + 1) (p a) (p b)).trans (hp a b)

/-- The actual finite mesh. Its endpoint belongs to the same unit interval. -/
def cocycleGridTime (N : ℕ) (hN : 0 < N) (k : Fin (N + 1)) : unitInterval :=
  ⟨(k : ℝ) / N, by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast hN : (0 : ℝ) < N)).mpr
      exact_mod_cast Nat.le_of_lt_succ k.isLt⟩

lemma cocycleGridTime_zero (N : ℕ) (hN : 0 < N) :
    cocycleGridTime N hN 0 = 0 := by
  apply Subtype.ext
  simp only [cocycleGridTime, Fin.val_zero, Nat.cast_zero, zero_div]
  rfl

lemma cocycleGridTime_last (N : ℕ) (hN : 0 < N) :
    cocycleGridTime N hN (Fin.last N) = 1 := by
  apply Subtype.ext
  change (N : ℝ) / N = 1
  exact div_self (by exact_mod_cast hN.ne')

lemma cocycleGridTime_step (N : ℕ) (hN : 0 < N) (k : Fin N) :
    |(cocycleGridTime N hN k.castSucc : ℝ) - cocycleGridTime N hN k.succ| = 1 / N := by
  change |(k : ℝ) / N - ((k : ℕ) + 1 : ℕ) / (N : ℝ)| = 1 / N
  rw [Nat.cast_add, Nat.cast_one, ← sub_div]
  have he : (k : ℝ) - ((k : ℝ) + 1) = -1 := by ring
  rw [he, neg_div, abs_neg, abs_of_pos (one_div_pos.mpr (by exact_mod_cast hN))]

lemma finiteCocycleCoefficient_grid_seam (α : unitary E →* unitary E) (w : unitary E)
    (N : ℕ) (hN : 0 < N) (p : Path (finiteGroupCocycle α w N) 1) :
    finiteCocycleCoefficient α w p 0 (cocycleGridTime N hN 0) =
      finiteCocycleCoefficient α w p N (cocycleGridTime N hN (Fin.last N)) := by
  rw [cocycleGridTime_zero, cocycleGridTime_last,
    finiteCocycleCoefficient_zero, finiteCocycleCoefficient_terminal]

lemma finiteCocycleCoefficient_grid_step (α : unitary E →* unitary E) (w : unitary E)
    (hα : ∀ u v : unitary E, ‖(α u : E) - α v‖ ≤ ‖(u : E) - v‖)
    (N : ℕ) (hN : 0 < N) (p : Path (finiteGroupCocycle α w N) 1)
    (L : ℝ) (hp : ∀ a b, ‖(p a : E) - p b‖ ≤ L * |(a : ℝ) - b|) (k : Fin N) :
    ‖(w : E) * α (finiteCocycleCoefficient α w p k (cocycleGridTime N hN k.castSucc)) -
      finiteCocycleCoefficient α w p (k + 1) (cocycleGridTime N hN k.succ)‖ ≤ L / N := by
  have h := finiteCocycleCoefficient_step_norm α w hα p L hp k
    (cocycleGridTime N hN k.castSucc) (cocycleGridTime N hN k.succ)
  rw [cocycleGridTime_step] at h
  simpa only [mul_one_div] using h

end WeakPureInfiniteness

end

end OAI
