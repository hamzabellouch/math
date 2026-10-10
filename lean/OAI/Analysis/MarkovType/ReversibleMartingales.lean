import OAI.Analysis.MarkovType.FinitePaths
import OAI.Analysis.MarkovType.FiniteSmoothMoments
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {S X : Type*} [Fintype S]
variable [NormedAddCommGroup X] [sectionNormedSpaceℝX : NormedSpace ℝ X]

local instance : DecidableEq S := Classical.decEq S

def chainAverage (C : FiniteReversibleChain S) (f : S → X) (i : S) : X :=
  ∑ j, C.P i j • f j

def chainDrift (C : FiniteReversibleChain S) (f : S → X) (i : S) : X :=
  chainAverage C f i - f i

theorem chainDrift_eq_sum (C : FiniteReversibleChain S) (f : S → X) (i : S) :
    chainDrift C f i = ∑ j, C.P i j • (f j - f i) := by
  simp only [chainDrift, chainAverage, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, C.sum_P, one_smul]

theorem chainAverage_centered_sum (C : FiniteReversibleChain S)
    (f : S → X) (i : S) :
    (∑ j, C.P i j • (f j - chainAverage C f i)) = 0 := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
    C.sum_P, one_smul]
  exact sub_self _

def sampledEvenIndex {m : ℕ} (j : Fin (m + 1)) : Fin (2 * m + 1) :=
  ⟨2 * j.val, by omega⟩

def sampledOddIndex {m : ℕ} (j : Fin m) : Fin (2 * m + 1) :=
  ⟨2 * j.val + 1, by omega⟩

def sampledDifference (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (j : Fin m) (ω : StatePath S (2 * m)) : X :=
  f (ω (sampledEvenIndex j.succ)) - chainAverage C f (ω (sampledOddIndex j))

def sampledForward (C : FiniteReversibleChain S) (f : S → X)
    (m k : ℕ) (ω : StatePath S (2 * m)) : X :=
  ∑ j : Fin m, if j.val < k then sampledDifference C f j ω else 0

def sampledBackward (C : FiniteReversibleChain S) (f : S → X)
    (m k : ℕ) (ω : StatePath S (2 * m)) : X :=
  sampledForward C f m k (pathReverse ω)

def sampledKey (m : ℕ) (k : Fin m) (ω : StatePath S (2 * m)) :
    StatePath S (2 * k.val) :=
  pathTake (2 * k.val) (by omega) ω

@[simp] theorem sampledForward_zero (C : FiniteReversibleChain S)
    (f : S → X) (m : ℕ) (ω : StatePath S (2 * m)) :
    sampledForward C f m 0 ω = 0 := by
  simp [sampledForward]

theorem sampledForward_step (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (k : Fin m) (ω : StatePath S (2 * m)) :
    sampledForward C f m (k.val + 1) ω - sampledForward C f m k.val ω =
      sampledDifference C f k ω := by
  classical
  unfold sampledForward
  rw [← Finset.sum_sub_distrib]
  have he (j : Fin m) :
      (if j.val < k.val + 1 then sampledDifference C f j ω else 0) -
        (if j.val < k.val then sampledDifference C f j ω else 0) =
      if j = k then sampledDifference C f k ω else 0 := by
    by_cases hjk : j = k
    · subst j
      simp
    · have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
      by_cases hj : j.val < k.val
      · have hj' : j.val < k.val + 1 := by omega
        simp [hj, hj', hjk]
      · have hj' : ¬ j.val < k.val + 1 := by omega
        simp [hj, hj', hjk]
  simp_rw [he]
  simp

theorem sampledForward_end (C : FiniteReversibleChain S) (f : S → X)
    (m : ℕ) (ω : StatePath S (2 * m)) :
    sampledForward C f m m ω = ∑ j : Fin m, sampledDifference C f j ω := by
  apply Finset.sum_congr rfl
  intro j hj
  exact ite_eq_left j.isLt

theorem sampledForward_fiber_constant (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (k : Fin m) (ω ω' : StatePath S (2 * m))
    (hkey : sampledKey m k ω = sampledKey m k ω') :
    sampledForward C f m k.val ω = sampledForward C f m k.val ω' := by
  classical
  unfold sampledForward
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjk : j.val < k.val
  · simp only [ite_eq_left hjk]
    have he := congrFun hkey (⟨2 * j.val + 2, by omega⟩ : Fin (2 * k.val + 1))
    have ho := congrFun hkey (⟨2 * j.val + 1, by omega⟩ : Fin (2 * k.val + 1))
    change ω ⟨2 * j.val + 2, _⟩ = ω' ⟨2 * j.val + 2, _⟩ at he
    change ω ⟨2 * j.val + 1, _⟩ = ω' ⟨2 * j.val + 1, _⟩ at ho
    unfold sampledDifference sampledEvenIndex sampledOddIndex
    dsimp only [Fin.val_succ]
    simpa only [Nat.mul_add, Nat.mul_one] using
      congrArg₂ (fun a b : S => f a - chainAverage C f b) he ho
  · simp only [ite_eq_right hjk]

omit sectionNormedSpaceℝX in
private theorem sum_fin_successive_sub [NormedSpace ℝ X] {m : ℕ} (g : Fin (m + 1) → X) :
    (∑ j : Fin m, (g j.succ - g j.castSucc)) = g (Fin.last m) - g 0 := by
  have he : g 0 + (∑ j : Fin m, g j.succ) =
      (∑ j : Fin m, g j.castSucc) + g (Fin.last m) :=
    (Fin.sum_univ_succ g).symm.trans (Fin.sum_univ_castSucc g)
  rw [Finset.sum_sub_distrib]
  calc
    _ = (g 0 + ∑ j : Fin m, g j.succ) -
        ((∑ j : Fin m, g j.castSucc) + g 0) := by abel
    _ = ((∑ j : Fin m, g j.castSucc) + g (Fin.last m)) -
        ((∑ j : Fin m, g j.castSucc) + g 0) := by rw [he]
    _ = g (Fin.last m) - g 0 := by abel

theorem sampledDifference_reverse (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (j : Fin m) (ω : StatePath S (2 * m)) :
    sampledDifference C f j ω - sampledDifference C f j.rev (pathReverse ω) =
      f (ω (sampledEvenIndex j.succ)) - f (ω (sampledEvenIndex j.castSucc)) := by
  have ho : (sampledOddIndex j.rev).rev = sampledOddIndex j := by
    apply Fin.ext
    simp only [sampledOddIndex, Fin.val_rev]
    omega
  have he : (sampledEvenIndex j.rev.succ).rev = sampledEvenIndex j.castSucc := by
    apply Fin.ext
    simp only [sampledEvenIndex, Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
    omega
  simp only [sampledDifference, pathReverse, ho, he]
  abel

theorem even_displacement_decomposition (C : FiniteReversibleChain S) (f : S → X)
    (m : ℕ) (ω : StatePath S (2 * m)) :
    f (ω (Fin.last (2 * m))) - f (ω 0) =
      sampledForward C f m m ω - sampledBackward C f m m ω := by
  classical
  rw [sampledBackward, sampledForward_end, sampledForward_end]
  let e : Fin m ≃ Fin m := Fin.revPerm
  have hs := e.sum_comp (fun j => sampledDifference C f j (pathReverse ω))
  rw [← hs, ← Finset.sum_sub_distrib]
  change _ = ∑ j : Fin m,
    (sampledDifference C f j ω - sampledDifference C f j.rev (pathReverse ω))
  simp_rw [sampledDifference_reverse]
  have h := sum_fin_successive_sub (fun j : Fin (m + 1) => f (ω (sampledEvenIndex j)))
  have hlast : sampledEvenIndex (Fin.last m) = Fin.last (2 * m) := by
    apply Fin.ext
    simp only [sampledEvenIndex, Fin.val_last]
  have hzero : sampledEvenIndex (0 : Fin (m + 1)) = 0 := by
    apply Fin.ext
    simp only [sampledEvenIndex, Fin.val_zero, Nat.mul_zero]
  simpa only [hlast, hzero] using h.symm

private theorem sum_fiber_comp_zero {Ω ι κ V : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι] [DecidableEq κ] [AddCommMonoid V]
    (key : Ω → ι) (coarse : ι → κ) (F : Ω → V)
    (hz : ∀ a, ∑ ω ∈ Finset.univ.filter (fun ω => key ω = a), F ω = 0)
    (b : κ) :
    (∑ ω ∈ Finset.univ.filter (fun ω => coarse (key ω) = b), F ω) = 0 := by
  classical
  rw [← Finset.sum_fiberwise _ key F]
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hb : coarse a = b
  · have he : (Finset.univ.filter (fun ω => coarse (key ω) = b)).filter
        (fun ω => key ω = a) = Finset.univ.filter (fun ω => key ω = a) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by simpa only [h] using hb, h⟩
    rw [he]
    exact hz a
  · have he : (Finset.univ.filter (fun ω => coarse (key ω) = b)).filter
        (fun ω => key ω = a) = ∅ := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_and]
      intro h h'
      exact hb (h' ▸ h)
    rw [he, Finset.sum_empty]

theorem sampledDifference_fine_cancel (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (k : Fin m) (η : StatePath S (2 * k.val + 1)) :
    (∑ ω ∈ Finset.univ.filter
        (fun ω : StatePath S (2 * m) => pathTake (2 * k.val + 1) (by omega) ω = η),
      pathWeight C (2 * m) ω • sampledDifference C f k ω) = 0 := by
  classical
  have h := sum_pathWeight_take_next C (2 * k.val + 1) (by omega : 2 * k.val + 1 < 2 * m)
    η (fun j => f j - chainAverage C f (η (Fin.last (2 * k.val + 1))))
  rw [chainAverage_centered_sum, smul_zero] at h
  rw [Finset.sum_filter]
  calc
    _ = ∑ ω : StatePath S (2 * m),
        if pathTake (2 * k.val + 1) (by omega) ω = η then
          pathWeight C (2 * m) ω •
            (f (ω ⟨2 * k.val + 1 + 1, by omega⟩) -
              chainAverage C f (η (Fin.last (2 * k.val + 1))))
        else 0 := by
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases he : pathTake (2 * k.val + 1) (by omega) ω = η
      · have hc := congrFun he (Fin.last (2 * k.val + 1))
        change ω (sampledOddIndex k) = η (Fin.last (2 * k.val + 1)) at hc
        simp only [ite_eq_left he, sampledDifference, hc, sampledEvenIndex,
          Fin.val_succ, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      · simp only [ite_eq_right he]
    _ = 0 := h

theorem sampledForward_fiber_cancel (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (k : Fin m) (η : StatePath S (2 * k.val)) :
    (∑ ω ∈ Finset.univ.filter (fun ω => sampledKey m k ω = η),
      pathWeight C (2 * m) ω •
        (sampledForward C f m (k.val + 1) ω - sampledForward C f m k.val ω)) = 0 := by
  classical
  simp_rw [sampledForward_step]
  exact sum_fiber_comp_zero
    (fun ω : StatePath S (2 * m) => pathTake (2 * k.val + 1) (by omega) ω)
    (pathTake (2 * k.val) (Nat.le_succ _))
    (fun ω => pathWeight C (2 * m) ω • sampledDifference C f k ω)
    (sampledDifference_fine_cancel C f k) η

theorem sampledBackward_fiber_constant (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (k : Fin m) (ω ω' : StatePath S (2 * m))
    (hkey : sampledKey m k (pathReverse ω) = sampledKey m k (pathReverse ω')) :
    sampledBackward C f m k.val ω = sampledBackward C f m k.val ω' :=
  sampledForward_fiber_constant C f k _ _ hkey

theorem sampledBackward_fiber_cancel (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (k : Fin m) (η : StatePath S (2 * k.val)) :
    (∑ ω ∈ Finset.univ.filter (fun ω => sampledKey m k (pathReverse ω) = η),
      pathWeight C (2 * m) ω •
        (sampledBackward C f m (k.val + 1) ω - sampledBackward C f m k.val ω)) = 0 := by
  classical
  have hr := sum_pathWeight_reverse_v C (2 * m)
    (fun ω => if sampledKey m k ω = η then
      sampledForward C f m (k.val + 1) ω - sampledForward C f m k.val ω else 0)
  have hz := sampledForward_fiber_cancel C f k η
  simpa only [sampledBackward, Finset.sum_filter, smul_ite, smul_zero] using hr.trans
    (by simpa only [Finset.sum_filter, smul_ite, smul_zero] using hz)

private theorem sum_weighted_two {Ω : Type*} [Fintype Ω]
    (w a b : Ω → ℝ) :
    (∑ ω, w ω * (2 * (a ω + b ω))) =
      2 * ((∑ ω, w ω * a ω) + ∑ ω, w ω * b ω) := by
  calc
    _ = ∑ ω, (2 * (w ω * a ω) + 2 * (w ω * b ω)) := by
      apply Finset.sum_congr rfl
      intro ω hω
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring

theorem chainDrift_q_moment_le {q : ℝ} (hq : 1 ≤ q)
    (C : FiniteReversibleChain S) (f : S → X) :
    (∑ i, C.π i * ‖chainDrift C f i‖ ^ q) ≤ stateCost C f q 1 := by
  rw [stateCost_one]
  calc
    _ ≤ ∑ i, C.π i * ∑ j, C.P i j * ‖f j - f i‖ ^ q := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (C.π_nonneg i)
      rw [chainDrift_eq_sum]
      exact finite_norm_rpow_jensen (C.P i) (fun j => f j - f i)
        (C.P_nonneg i) (C.sum_P i) hq
    _ = _ := by simp only [Finset.mul_sum, mul_assoc, Real.rpow_eq_pow]

theorem centered_edge_q_moment_le_four {q : ℝ} (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (C : FiniteReversibleChain S) (f : S → X) :
    (∑ i, ∑ j, (C.π i * C.P i j) * ‖f j - chainAverage C f i‖ ^ q) ≤
      4 * stateCost C f q 1 := by
  have htriangle (i j : S) : ‖f j - chainAverage C f i‖ ^ q ≤
      2 * (‖f j - f i‖ ^ q + ‖chainDrift C f i‖ ^ q) := by
    have he : (f j - f i) - chainDrift C f i = f j - chainAverage C f i := by
      unfold chainDrift
      abel
    simpa only [he] using norm_sub_rpow_le_two hq hq2 (f j - f i) (chainDrift C f i)
  have hrow : (∑ i, ∑ j, (C.π i * C.P i j) * ‖chainDrift C f i‖ ^ q) =
      ∑ i, C.π i * ‖chainDrift C f i‖ ^ q := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      _ = (C.π i * ∑ j, C.P i j) * ‖chainDrift C f i‖ ^ q := by
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = _ := by rw [C.sum_P, mul_one]
  have he (i j : S) :
      (C.π i * C.P i j) *
          (2 * (‖f j - f i‖ ^ q + ‖chainDrift C f i‖ ^ q)) =
        2 * ((C.π i * C.P i j) * ‖f j - f i‖ ^ q) +
          2 * ((C.π i * C.P i j) * ‖chainDrift C f i‖ ^ q) := by ring
  calc
    _ ≤ ∑ i, ∑ j, (C.π i * C.P i j) *
        (2 * (‖f j - f i‖ ^ q + ‖chainDrift C f i‖ ^ q)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (htriangle i j)
        (mul_nonneg (C.π_nonneg i) (C.P_nonneg i j))
    _ = 2 * stateCost C f q 1 + 2 * ∑ i, C.π i * ‖chainDrift C f i‖ ^ q := by
      simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hrow, stateCost_one]
      simp only [Real.rpow_eq_pow]
    _ ≤ 4 * stateCost C f q 1 := by
      linarith only [chainDrift_q_moment_le hq C f]

theorem sampledDifference_q_moment_le_four {q : ℝ}
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (C : FiniteReversibleChain S) (f : S → X)
    {m : ℕ} (k : Fin m) :
    (∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
      ‖sampledDifference C f k ω‖ ^ q) ≤ 4 * stateCost C f q 1 := by
  have hodd : (⟨2 * k.val + 1, by omega⟩ : Fin (2 * m)).castSucc =
      sampledOddIndex k := by
    apply Fin.ext
    rfl
  have heven : (⟨2 * k.val + 1, by omega⟩ : Fin (2 * m)).succ =
      sampledEvenIndex k.succ := by
    apply Fin.ext
    change 2 * k.val + 1 + 1 = 2 * (k.val + 1)
    omega
  have hp := sum_pathWeight_pair C (2 * k.val + 1)
    (by omega : 2 * k.val + 1 < 2 * m)
    (fun i j => ‖f j - chainAverage C f i‖ ^ q)
  have he : (∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
      ‖sampledDifference C f k ω‖ ^ q) =
      ∑ i, ∑ j, (C.π i * C.P i j) * ‖f j - chainAverage C f i‖ ^ q := by
    simpa only [sampledDifference, hodd, heven] using hp
  rw [he]
  exact centered_edge_q_moment_le_four hq hq2 C f

theorem sampledForward_q_moment_le {q D : ℝ}
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hD : 0 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X)
    (C : FiniteReversibleChain S) (f : S → X) (m : ℕ) :
    (∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
      ‖sampledForward C f m m ω‖ ^ q) ≤
      16 * D * (m : ℝ) * stateCost C f q 1 := by
  classical
  have h := finite_martingale_q_moment_four hq hq2 hD hsmooth m
    (fun k : Fin m => StatePath S (2 * k.val))
    (pathWeight C (2 * m)) (sampledKey m) (sampledForward C f m)
    (pathWeight_nonneg C (2 * m)) (sampledForward_zero C f m)
    (sampledForward_fiber_constant C f) (sampledForward_fiber_cancel C f)
  calc
    _ ≤ (4 * D) * ∑ k : Fin m, ∑ ω : StatePath S (2 * m),
        pathWeight C (2 * m) ω *
          ‖sampledForward C f m (k.val + 1) ω - sampledForward C f m k.val ω‖ ^ q := h
    _ = (4 * D) * ∑ k : Fin m, ∑ ω : StatePath S (2 * m),
        pathWeight C (2 * m) ω * ‖sampledDifference C f k ω‖ ^ q := by
      simp_rw [sampledForward_step]
    _ ≤ (4 * D) * ∑ _k : Fin m, 4 * stateCost C f q 1 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hD)
      exact Finset.sum_le_sum fun k hk => sampledDifference_q_moment_le_four hq hq2 C f k
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem sampledBackward_q_moment_le {q D : ℝ}
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hD : 0 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X)
    (C : FiniteReversibleChain S) (f : S → X) (m : ℕ) :
    (∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
      ‖sampledBackward C f m m ω‖ ^ q) ≤
      16 * D * (m : ℝ) * stateCost C f q 1 := by
  have h := sum_pathWeight_reverse_v C (2 * m)
    (fun ω => ‖sampledForward C f m m ω‖ ^ q)
  have he : (∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
      ‖sampledBackward C f m m ω‖ ^ q) =
      ∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
        ‖sampledForward C f m m ω‖ ^ q := by
    simpa only [sampledBackward, smul_eq_mul] using h
  rw [he]
  exact sampledForward_q_moment_le hq hq2 hD hsmooth C f m

theorem even_stateCost_le {q D : ℝ}
    (hq : 1 ≤ q) (hq2 : q ≤ 2) (hD : 0 ≤ D)
    (hsmooth : SymmetricPowerSmoothWith q D X)
    (C : FiniteReversibleChain S) (f : S → X) (m : ℕ) :
    stateCost C f q (2 * m) ≤
      32 * D * ((2 * m : ℕ) : ℝ) * stateCost C f q 1 := by
  have ha := sampledForward_q_moment_le hq hq2 hD hsmooth C f m
  have hb := sampledBackward_q_moment_le hq hq2 hD hsmooth C f m
  calc
    _ = ∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
        ‖sampledForward C f m m ω - sampledBackward C f m m ω‖ ^ q := by
      unfold stateCost
      simp_rw [even_displacement_decomposition C f m, Real.rpow_eq_pow]
    _ ≤ ∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
        (2 * (‖sampledForward C f m m ω‖ ^ q +
          ‖sampledBackward C f m m ω‖ ^ q)) := by
      exact Finset.sum_le_sum fun ω hω => mul_le_mul_of_nonneg_left
        (norm_sub_rpow_le_two hq hq2 _ _) (pathWeight_nonneg C (2 * m) ω)
    _ = 2 * ((∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
        ‖sampledForward C f m m ω‖ ^ q) +
        (∑ ω : StatePath S (2 * m), pathWeight C (2 * m) ω *
          ‖sampledBackward C f m m ω‖ ^ q)) := by
      exact sum_weighted_two _ _ _
    _ ≤ 32 * D * ((2 * m : ℕ) : ℝ) * stateCost C f q 1 := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      linarith only [ha, hb]

theorem stateCost_succ_le_two {q : ℝ} (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (C : FiniteReversibleChain S) (f : S → X) (n : ℕ) :
    stateCost C f q (n + 1) ≤ 2 * (stateCost C f q n + stateCost C f q 1) := by
  let first : StatePath S (n + 1) → X := fun ω =>
    f (ω (Fin.last n).castSucc) - f (ω 0)
  let last : StatePath S (n + 1) → X := fun ω =>
    f (ω (Fin.last (n + 1))) - f (ω (Fin.last n).castSucc)
  have hsplit (ω : StatePath S (n + 1)) :
      f (ω (Fin.last (n + 1))) - f (ω 0) = first ω + last ω := by
    dsimp [first, last]
    abel
  have hfirst : (∑ ω : StatePath S (n + 1), pathWeight C (n + 1) ω * ‖first ω‖ ^ q) =
      stateCost C f q n := by
    have hcast (i : Fin (n + 1)) :
        Fin.castLE (Nat.add_le_add_right (Nat.le_succ n) 1) i = i.castSucc := by
      apply Fin.ext
      rfl
    have hzero : (0 : Fin (n + 1)).castSucc = 0 := by
      apply Fin.ext
      rfl
    simpa only [first, pathTake, stateCost, hcast, hzero, Real.rpow_eq_pow] using
      sum_pathWeight_take C n (Nat.le_succ n)
        (fun η => ‖f (η (Fin.last n)) - f (η 0)‖ ^ q)
  have hlast : (∑ ω : StatePath S (n + 1), pathWeight C (n + 1) ω * ‖last ω‖ ^ q) =
      stateCost C f q 1 := by
    rw [stateCost_one]
    exact sum_pathWeight_last_pair C n (fun i j => ‖f j - f i‖ ^ q)
  calc
    _ = ∑ ω : StatePath S (n + 1), pathWeight C (n + 1) ω * ‖first ω + last ω‖ ^ q := by
      unfold stateCost
      simp_rw [hsplit, Real.rpow_eq_pow]
    _ ≤ ∑ ω : StatePath S (n + 1), pathWeight C (n + 1) ω *
        (2 * (‖first ω‖ ^ q + ‖last ω‖ ^ q)) := by
      exact Finset.sum_le_sum fun ω hω => mul_le_mul_of_nonneg_left
        (norm_add_rpow_le_two hq hq2 _ _) (pathWeight_nonneg C (n + 1) ω)
    _ = 2 * ((∑ ω : StatePath S (n + 1), pathWeight C (n + 1) ω * ‖first ω‖ ^ q) +
        (∑ ω : StatePath S (n + 1), pathWeight C (n + 1) ω * ‖last ω‖ ^ q)) := by
      exact sum_weighted_two _ _ _
    _ = _ := by rw [hfirst, hlast]

end MarkovSuperreflexivity

end

end OAI
