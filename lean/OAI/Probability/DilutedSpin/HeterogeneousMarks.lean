import OAI.Probability.DilutedSpin.ReservoirVariance

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set
namespace DilutedSpinGlass.HeterogeneousMarks
open scoped BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]

/-- The independent auxiliary mark row for the actually realized type list. -/
abbrev Row {k : ℕ} (roots : Fin k → I) := (j : Fin k) → A (roots j)

/-- A product-prior tower on the physical state and all realized marks. -/
noncomputable def tower {k : ℕ} (roots : Fin k → I) : (L : ℕ) →
    KernelTower Ω L → ((i : I) → Fin L → FiniteLaw (A i)) →
    KernelTower (Ω × Row (A := A) roots) L
  | 0, _, _ => ()
  | L+1, T, Q => (T.1.bind (fun _ => FiniteLaw.pi (fun j => Q (roots j) 0)),
      fun y => tower roots L (T.2 y.1) (fun i j => Q i j.succ))

/-- Forget all auxiliary marks. -/
def physical {k : ℕ} (roots : Fin k → I) : (L : ℕ) →
    FinitePath (Ω × Row (A := A) roots) L → FinitePath Ω L
  | 0, _ => ()
  | L+1, y => (y.1.1, physical roots L y.2)

/-- The path of the q-th realized mark, in that mark's own finite space. -/
def mark {k : ℕ} {roots : Fin k → I} (q : Fin k) : (L : ℕ) →
    FinitePath (Ω × Row (A := A) roots) L → FinitePath (A (roots q)) L
  | 0, _ => ()
  | L+1, y => (y.1.2 q, mark q L y.2)

/-- Move one distinguished mark out of the dependent row. -/
def split {k : ℕ} (roots : Fin k → I) (i : I) :
    (Ω × Row (A := A) (Fin.cons i roots)) ≃ ((Ω × Row (A := A) roots) × A i) where
  toFun y := ((y.1, Fin.tail y.2), y.2 0)
  invFun z := (z.1.1, Fin.cons z.2 z.1.2)
  left_inv y := by simp only [Fin.cons_self_tail]
  right_inv z := by
    rcases z with ⟨⟨x, row⟩, a⟩
    rfl

/-- Adding a type uses its own prior, independently of all old marks. -/
theorem tower_split {k : ℕ} (roots : Fin k → I) (i : I) (L : ℕ)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    KernelTower.transport (split roots i) L (tower (Fin.cons i roots) L T Q) =
      KernelTower.prod L (tower roots L T Q) (markPrior L (Q i)) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · apply FiniteLaw.eq_of_weights
      intro z
      change T.1.weight z.1.1 *
          (∏ j : Fin (k+1), (Q ((Fin.cons i roots : Fin (k+1) → I) j) 0).weight
            ((Fin.cons z.2 z.1.2 : Row (A := A) (Fin.cons i roots)) j)) =
        (T.1.weight z.1.1 * ∏ j, (Q (roots j) 0).weight (z.1.2 j)) * (Q i 0).weight z.2
      rw [Fin.prod_univ_succ]
      change T.1.weight z.1.1 *
        ((Q i 0).weight z.2 * ∏ j, (Q (roots j) 0).weight (z.1.2 j)) =
        (T.1.weight z.1.1 * ∏ j, (Q (roots j) 0).weight (z.1.2 j)) * (Q i 0).weight z.2
      ring
    · funext z
      exact ih (T.2 z.1.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem physical_split {k : ℕ} (roots : Fin k → I) (i : I) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    physical roots L (KernelTower.pathFst L (KernelTower.pathEquiv (split roots i) L y)) =
      physical (Fin.cons i roots) L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physical roots L (KernelTower.pathFst L
      (KernelTower.pathEquiv (split roots i) L y.2))) =
      (y.1.1, physical (Fin.cons i roots) L y.2)
    rw [ih]

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem mark_split_succ {k : ℕ} (roots : Fin k → I) (i : I) (q : Fin k) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    mark q L (KernelTower.pathFst L (KernelTower.pathEquiv (split roots i) L y)) =
      mark q.succ L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 q.succ, mark q L (KernelTower.pathFst L
      (KernelTower.pathEquiv (split roots i) L y.2))) = (y.1.2 q.succ, mark q.succ L y.2)
    rw [ih]
    rfl

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem mark_split_zero {k : ℕ} (roots : Fin k → I) (i : I) (L : ℕ)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    KernelTower.pathSnd L (KernelTower.pathEquiv (split roots i) L y) = mark 0 L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.2 0, KernelTower.pathSnd L (KernelTower.pathEquiv (split roots i) L y.2)) =
      (y.1.2 0, mark 0 L y.2)
    rw [ih]
    rfl

variable {k L : ℕ}

/-- A finite realized row in the full countable-type model. -/
noncomputable def logWeight (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (y : FinitePath (Ω × Row (A := A) roots) L) : ℝ :=
  base (physical roots L y) + ∑ q, Real.log (factor (roots q) (physical roots L y) (mark q L y))

/-- The insertion keeps the complete original mark row in the base law. -/
noncomputable def insertedLog (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (i : I)
    (y : FinitePath ((Ω × Row (A := A) roots) × A i) L) : ℝ :=
  logWeight base roots factor (KernelTower.pathFst L y) +
    Real.log (factor i (physical roots L (KernelTower.pathFst L y)) (KernelTower.pathSnd L y))

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem insertedLog_split (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (i : I)
    (y : FinitePath (Ω × Row (A := A) (Fin.cons i roots)) L) :
    insertedLog base roots factor i (KernelTower.pathEquiv (split roots i) L y) =
      logWeight base (Fin.cons i roots) factor y := by
  simp only [insertedLog, logWeight, physical_split, mark_split_succ,
    mark_split_zero, Fin.sum_univ_succ]
  change base (physical (Fin.cons i roots) L y) +
      (∑ q, Real.log (factor (roots q) (physical (Fin.cons i roots) L y) (mark q.succ L y))) +
      Real.log (factor i (physical (Fin.cons i roots) L y) (mark 0 L y)) =
    base (physical (Fin.cons i roots) L y) +
      (Real.log (factor i (physical (Fin.cons i roots) L y) (mark 0 L y)) +
      ∑ q, Real.log (factor (roots q) (physical (Fin.cons i roots) L y) (mark q.succ L y)))
  ring

/-- The quenched logarithmic root energy in the actual dependent mark row. -/
noncomputable def root (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) : ℝ :=
  KernelTower.backwardLog L (tower roots L T Q) m (logWeight base roots factor)

/-- Uniform add/delete control does not depend on the mark dimension or type. -/
theorem root_cons_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I) (i : I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hfactor : ∀ x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base (Fin.cons i roots) factor - root T Q m base roots factor| ≤ C := by
  have h := KernelTower.backwardLog_transport (split roots i) L
    (tower (Fin.cons i roots) L T Q) m (insertedLog base roots factor i)
  have heq : insertedLog base roots factor i ∘ KernelTower.pathEquiv (split roots i) L =
      logWeight base (Fin.cons i roots) factor :=
    funext (fun y => insertedLog_split base roots factor i y)
  rw [heq, tower_split] at h
  unfold root
  rw [← h, ← KernelTower.backwardLog_prod_fst L (tower roots L T Q) (markPrior L (Q i)) m
    (logWeight base roots factor)]
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simpa only [insertedLog, add_sub_cancel_left] using hfactor
    (physical roots L (KernelTower.pathFst L y)) (KernelTower.pathSnd L y)

/-- Typewise log-factor errors sum on the actual root list. -/
theorem root_factor_stability (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor factor' : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (C : I → ℝ) (hC : ∀ i x y, |Real.log (factor i x y) - Real.log (factor' i x y)| ≤ C i) :
    |root T Q m base roots factor - root T Q m base roots factor'| ≤ ∑ q, C (roots q) := by
  apply KernelTower.backwardLog_stability L _ m hm
  intro y
  simp only [logWeight, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun q _ => hC _ _ _))

/-- Deleting tail types is comparison on a common law, not a change of law. -/
theorem root_mask_bound (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (keep : I → Prop) [DecidablePred keep] (C : I → ℝ)
    (hC : ∀ i x y, |Real.log (factor i x y)| ≤ C i) :
    |root T Q m base roots factor -
      root T Q m base roots (fun i x y => if keep i then factor i x y else 1)| ≤
        ∑ q, if keep (roots q) then 0 else C (roots q) := by
  apply root_factor_stability T Q m hm base roots _ _ (fun i => if keep i then 0 else C i)
  intro i x y
  by_cases hi : keep i
  · simp [hi]
  · simpa only [hi, ↓reduceIte, Real.log_one, sub_zero] using hC i x y

end DilutedSpinGlass.HeterogeneousMarks

namespace DilutedSpinGlass.HeterogeneousMarks
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
variable {k L : ℕ}

/-- The complete independent row can be integrated as a single finite mark.
Its dimension depends on the realized labels, never on a deterministic cutoff. -/
theorem tower_eq_prod (roots : Fin k → I) (L : ℕ) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) :
    tower roots L T Q = KernelTower.prod L T
      (markPrior L (fun d => FiniteLaw.pi (fun j => Q (roots j) d))) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    apply Prod.ext
    · rfl
    · funext y
      exact ih (T.2 y.1) (fun i j => Q i j.succ)

omit [Fintype Ω] [∀ i, Fintype (A i)] in
theorem physical_eq_fst (roots : Fin k → I)
    (y : FinitePath (Ω × Row (A := A) roots) L) :
    physical roots L y = KernelTower.pathFst L y := by
  induction L with
  | zero => rfl
  | succ L ih =>
    change (y.1.1, physical roots L y.2) = (y.1.1, KernelTower.pathFst L y.2)
    rw [ih]

/-- All unused finite priors integrate out, exactly, even if their dimension
varies over the full countable type list. -/
theorem root_one (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin k → I) :
    root T Q m base roots (fun _ _ _ => 1) = KernelTower.backwardLog L T m base := by
  unfold root
  have heq : logWeight (A := A) base roots (fun _ _ _ => 1) =
      base ∘ KernelTower.pathFst L := by
    funext y
    simp only [logWeight, Real.log_one, Finset.sum_const_zero, add_zero,
      physical_eq_fst, Function.comp_apply]
  rw [heq, tower_eq_prod]
  exact KernelTower.backwardLog_prod_fst L T _ m base

/-- The pathwise perturbation cost is additive over all realized labels. -/
theorem root_base_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (C : I → ℝ) (hC : ∀ i x y, |Real.log (factor i x y)| ≤ C i) :
    |root T Q m base roots factor - KernelTower.backwardLog L T m base| ≤
      ∑ q, C (roots q) := by
  rw [← root_one T Q m base roots]
  exact root_factor_stability T Q m hm base roots factor (fun _ _ _ => 1) C
    (fun i x y => by simpa only [Real.log_one, sub_zero] using hC i x y)

/-- No lower bound on a type's intensity occurs in this global domination. -/
theorem abs_root_le (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ) (roots : Fin k → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {C : ℝ}
    (hC : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base roots factor| ≤ |KernelTower.backwardLog L T m base| + C*k := by
  have h := root_base_bound T Q m hm base roots factor (fun _ => C) hC
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have ht := abs_add_le (root T Q m base roots factor - KernelTower.backwardLog L T m base)
    (KernelTower.backwardLog L T m base)
  rw [sub_add_cancel] at ht
  linarith

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
