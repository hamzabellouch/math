import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.TableValue

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

def initialState (E : Type*) (a T : ℕ) : GreedyState E a T :=
  (0, fun _ _ => none)

lemma initialState_invariant {E : Type*} {a T : ℕ} (part : E → Fin a) :
    GreedyInvariant part (initialState E a T) := by
  constructor
  · intro j ω e he
    change (none : Option E) = some e at he
    cases he
  · intro j ω h
    rfl

lemma draw_none {E Ω : Type*} [DecidableEq E] (a : ℕ) (seed : Fin a → Ω)
    (S : Finset E) : draw a (fun _ _ => (none : Option E)) seed S = S := by
  induction a with
  | zero => rfl
  | succ a ih => exact ih (Fin.tail seed)

lemma tableValue_none {E Ω : Type*} [DecidableEq E] [Fintype Ω] [Nonempty Ω]
    (a : ℕ) (g : SetFunction E) :
    tableValue g (fun _ : Fin a => fun _ : Ω => none) = g ∅ := by
  unfold tableValue
  simp_rw [draw_none]
  exact average_const _

section Run
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}

noncomputable def greedyRun (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (seed : Fin T → OracleSeed E a T L) : GreedyState E a T :=
  adaptiveRun (greedyStep part hp g) T (initialState E a T) seed

noncomputable def greedyOutput (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T)) : Finset E :=
  draw a (greedyRun part hp g seed.1).2 seed.2 ∅

lemma greedyRun_invariant (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (seed : Fin T → OracleSeed E a T L) :
    GreedyInvariant part (greedyRun part hp g seed) :=
  adaptiveRun_invariant _ (GreedyInvariant part) (greedyStep_invariant part hp g)
    T _ (initialState_invariant part) seed

lemma greedyOutput_feasible (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T)) :
    ∀ j, ((greedyOutput part hp g seed).filter (fun e => part e = j)).card ≤ 1 := by
  intro j
  exact draw_feasible part _ (greedyRun_invariant part hp g seed.1) seed.2 j

lemma greedyRun_expectation (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) :
    average (fun seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T) =>
      g (greedyOutput part hp g seed)) =
        average (fun seed : Fin T → OracleSeed E a T L =>
          tableValue g (greedyRun part hp g seed).2) := by
  exact average_prod _

omit [Fintype E] in
lemma tableValue_nonneg [NeZero T] (g : SetFunction E) (hmono : Monotone g)
    (hg0 : g ∅ = 0) (r : Fin a → Table (Fin T) E) : 0 ≤ tableValue g r := by
  apply average_nonneg
  intro seed
  rw [← hg0]
  exact hmono (Finset.empty_subset _)

lemma greedyRun_good [NeZero T] (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (o : Fin a → E) (ho : ∀ j, part (o j) = j)
    (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    {M tau : ℝ} (hM : 0 ≤ M) (hMo : M ≤ g (Finset.univ.image o))
    (hg : BoundedMarginals g M) (ha : 0 < a) (htau : 0 ≤ tau) (htau1 : tau ≤ 1/8)
    (hscale : (a:ℝ)^2 ≤ tau*T) (seed : Fin T → OracleSeed E a T L)
    (hgood : ¬adaptiveBad (greedyStep part hp g) (estimationBad part g M tau)
      T (initialState E a T) seed) :
    (1 - 1/Real.exp 1 - 3*tau) * g (Finset.univ.image o) ≤
      tableValue g (greedyRun part hp g seed).2 := by
  have hTR : (0:ℝ) < T := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne T))
  have hT1 : (1:ℝ) ≤ T := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne T))
  have hr : 0 ≤ 1 - 1/(T:ℝ) := sub_nonneg.mpr ((div_le_one hTR).mpr hT1)
  have hQ : 0 ≤ g (Finset.univ.image o) - 3*tau*M := by nlinarith
  have hh := adaptiveRun_growth (greedyStep part hp g) (estimationBad part g M tau)
    (GreedyInvariant part) Prod.fst (fun s => tableValue g s.2) T
    (Q := g (Finset.univ.image o) - 3*tau*M) hr
    (greedyStep_invariant part hp g) (greedyStep_clock part hp g)
    (fun s hs hlt ω hw => by
      have h := greedyStep_recurrence part hp g o ho hmono hsub hM hg ha hscale s hs hlt ω hw
      convert h using 1 ; ring)
    T (initialState E a T) (initialState_invariant part) (by simp [initialState]) seed hgood
  simp only [initialState, tableValue_none, hg0, mul_zero, zero_add] at hh
  have he := Real.one_sub_div_pow_le_exp_neg (n := T) (t := (1:ℝ)) hT1
  rw [Real.exp_neg] at he
  have he' := mul_le_mul_of_nonneg_right (sub_le_sub_left he 1) hQ
  have hexp : 0 ≤ 1 / Real.exp 1 := by positivity
  have hexp1 : 1 / Real.exp 1 ≤ 1 := by
    apply (div_le_one (Real.exp_pos _)).mpr
    exact Real.one_le_exp_iff.mpr (by norm_num)
  have hprod : (1 - 1 / Real.exp 1) * M ≤ g (Finset.univ.image o) := by nlinarith
  have hprod' := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 3*tau by positivity)
  calc
    _ ≤ (1 - 1/Real.exp 1) * (g (Finset.univ.image o) - 3*tau*M) := by nlinarith
    _ ≤ (1 - (1-1/(T:ℝ))^T) * (g (Finset.univ.image o) - 3*tau*M) :=
      by simpa only [one_div] using he'
    _ ≤ _ := hh

end Run
end MetricKMedianRecovery.Categorical

end OAI
