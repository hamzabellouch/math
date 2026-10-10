import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.UniformBits

namespace OAI

namespace MetricKMedianRecovery.Categorical.Selected
open FiniteSampling
structure Rule {E : Type*} {a : ℕ} (part : E→Fin a) where
  choose : (E→ℝ)→Fin a→E
  spec : ∀ score j,part (choose score j)=j ∧ ∀ e,part e=j→score e ≤ score (choose score j)
lemma Rule.surjective {E : Type*} {a : ℕ} {part : E→Fin a} (rule : Rule part) : Function.Surjective part :=
  fun j=>⟨rule.choose (fun _=>0) j,(rule.spec _ j).1⟩
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}
noncomputable def greedyStep (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (s : GreedyState E a T) (seed : OracleSeed E a T L) :
    GreedyState E a T :=
  if h : s.1 < T then
    (s.1+1, advance s.2 ⟨s.1,h⟩ (rule.choose (scores part g s.2 seed)))
  else s

omit [Fintype E] in
lemma greedyStep_clock (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (s : GreedyState E a T) (ht : s.1 < T)
    (seed : OracleSeed E a T L) : (greedyStep part rule g s seed).1 = s.1+1 := by
  simp [greedyStep, ht]

omit [Fintype E] in
lemma greedyStep_invariant (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (s : GreedyState E a T) (hs : GreedyInvariant part s)
    (seed : OracleSeed E a T L) : GreedyInvariant part (greedyStep part rule g s seed) := by
  by_cases ht : s.1 < T
  · simp only [greedyStep, dite_eq_left ht, GreedyInvariant, advance]
    constructor
    · intro j ω e he
      by_cases hω : ω = (⟨s.1,ht⟩ : Fin T)
      · subst ω
        simp only [Function.update_self, Option.some.injEq] at he
        rw [← he]
        exact (rule.spec _ j).1
      · rw [Function.update_of_ne hω] at he
        exact hs.1 j ω e he
    · intro j ω hω
      have hne : ω ≠ (⟨s.1,ht⟩ : Fin T) := by
        intro he
        have := congrArg Fin.val he
        simp only at this
        omega
      rw [Function.update_of_ne hne]
      exact hs.2 j ω (by omega)
  · simpa only [greedyStep, dite_eq_right ht] using hs

lemma sampled_select_choice [NeZero T] (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (r : Fin a → Table (Fin T) E) (o : Fin a → E)
    (ho : ∀ j, part (o j) = j) (seed : OracleSeed E a T L) {tol : ℝ}
    (hgood : ∀ e, |scores part g r seed e - average (marginalSample part g r e)| ≤ tol) :
    let c := rule.choose (scores part g r seed)
    ∀ j, derivative r c j (o j) g ∅ ≤ derivative r c j (c j) g ∅ + 2 * tol := by
  intro c j
  have hc := (rule.spec (scores part g r seed) j)
  have hg1 := hgood (c j)
  have hg2 := hgood (o j)
  rw [marginalSample_average part g r c, hc.1] at hg1
  rw [marginalSample_average part g r c, ho] at hg2
  exact two_estimates_choice hg1 hg2 (hc.2 (o j) (ho j))

lemma greedyStep_recurrence [NeZero T] (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (o : Fin a → E) (ho : ∀ j, part (o j) = j)
    (hmono : Monotone g) (hsub : Diminishing g) {M tau : ℝ} (hM : 0 ≤ M)
    (hg : BoundedMarginals g M) (ha : 0 < a) (hscale : (a:ℝ)^2 ≤ tau*T)
    (s : GreedyState E a T) (hs : GreedyInvariant part s) (ht : s.1 < T)
    (seed : OracleSeed E a T L) (hgood : ¬estimationBad part g M tau s seed) :
    tableValue g s.2 + (g (Finset.univ.image o) - tableValue g s.2 - 3*tau*M)/T ≤
      tableValue g (greedyStep part rule g s seed).2 := by
  have hgood' : ∀ e, |scores part g s.2 seed e - average (marginalSample part g s.2 e)|
      ≤ tau*M/a := by
    intro e
    exact not_lt.mp (fun he => hgood ⟨e,he⟩)
  have hc := sampled_select_choice part rule g s.2 o ho seed hgood'
  simpa only [greedyStep, dite_eq_left ht] using
    advance_recurrence g s.2 ⟨s.1,ht⟩ (rule.choose (scores part g s.2 seed)) o
      (fun j => hs.2 j ⟨s.1,ht⟩ (le_refl _)) hmono hsub hM hg ha hscale hc

lemma greedy_failure_bound [NeZero T] (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) {M tau : ℝ} (hM : 0 < M) (htau : 0 < tau)
    (hg : BoundedMarginals g M) (ha : 0 < a) (hL : 0 < L)
    (hcount : (T:ℝ) * Fintype.card E * a^2 / (4*tau^3) ≤ L)
    (s : GreedyState E a T) :
    probability (adaptiveBad (greedyStep (L := L) part rule g)
      (estimationBad part g M tau) T s) ≤ tau := by
  let X : GreedyState E a T → E → (Fin a → Fin T) → ℝ :=
    fun u e => marginalSample part g u.2 e
  have hX : ∀ u : GreedyState E a T, True → ∀ e seed,
      0 ≤ X u e seed ∧ X u e seed ≤ M := by
    intro u _ e seed
    exact hg e (draw a (Function.update u.2 (part e) (fun _ => none)) seed ∅)
  have hb := adaptive_categorical_error X L T a hL
    (Nat.pos_of_ne_zero (NeZero.ne T)) ha hM htau (greedyStep part rule g)
    (fun _ => True) (fun _ _ _ => trivial) hX hcount s trivial
  exact hb

noncomputable def greedyRun (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (seed : Fin T → OracleSeed E a T L) : GreedyState E a T :=
  adaptiveRun (greedyStep part rule g) T (initialState E a T) seed

noncomputable def greedyOutput (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T)) : Finset E :=
  draw a (greedyRun part rule g seed.1).2 seed.2 ∅

omit [Fintype E] in
lemma greedyRun_invariant (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (seed : Fin T → OracleSeed E a T L) :
    GreedyInvariant part (greedyRun part rule g seed) :=
  adaptiveRun_invariant _ (GreedyInvariant part) (greedyStep_invariant part rule g)
    T _ (initialState_invariant part) seed

omit [Fintype E] in
lemma greedyOutput_feasible (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T)) :
    ∀ j, ((greedyOutput part rule g seed).filter (fun e => part e = j)).card ≤ 1 := by
  intro j
  exact draw_feasible part _ (greedyRun_invariant part rule g seed.1) seed.2 j

lemma greedyRun_expectation (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) :
    average (fun seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T) =>
      g (greedyOutput part rule g seed)) =
        average (fun seed : Fin T → OracleSeed E a T L =>
          tableValue g (greedyRun part rule g seed).2) := by
  exact average_prod _

lemma greedyRun_good [NeZero T] (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (o : Fin a → E) (ho : ∀ j, part (o j) = j)
    (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    {M tau : ℝ} (hM : 0 ≤ M) (hMo : M ≤ g (Finset.univ.image o))
    (hg : BoundedMarginals g M) (ha : 0 < a) (htau : 0 ≤ tau) (htau1 : tau ≤ 1/8)
    (hscale : (a:ℝ)^2 ≤ tau*T) (seed : Fin T → OracleSeed E a T L)
    (hgood : ¬adaptiveBad (greedyStep part rule g) (estimationBad part g M tau)
      T (initialState E a T) seed) :
    (1 - 1/Real.exp 1 - 3*tau) * g (Finset.univ.image o) ≤
      tableValue g (greedyRun part rule g seed).2 := by
  have hTR : (0:ℝ) < T := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne T))
  have hT1 : (1:ℝ) ≤ T := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne T))
  have hr : 0 ≤ 1 - 1/(T:ℝ) := sub_nonneg.mpr ((div_le_one hTR).mpr hT1)
  have hQ : 0 ≤ g (Finset.univ.image o) - 3*tau*M := by nlinarith
  have hh := adaptiveRun_growth (greedyStep part rule g) (estimationBad part g M tau)
    (GreedyInvariant part) Prod.fst (fun s => tableValue g s.2) T
    (Q := g (Finset.univ.image o) - 3*tau*M) hr
    (greedyStep_invariant part rule g) (greedyStep_clock part rule g)
    (fun s hs hlt ω hw => by
      have h := greedyStep_recurrence part rule g o ho hmono hsub hM hg ha hscale s hs hlt ω hw
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

lemma greedyOutput_expected {E : Type*} [Fintype E] [DecidableEq E]
    {a T L : ℕ} [NeZero T] (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (o : Fin a → E) (ho : ∀ j, part (o j) = j)
    (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    {M tau : ℝ} (hM : 0 < M) (hMo : M ≤ g (Finset.univ.image o))
    (hg : BoundedMarginals g M) (ha : 0 < a) (htau : 0 < tau) (htau1 : tau ≤ 1/8)
    (hscale : (a:ℝ)^2 ≤ tau*T) (hL : 0 < L)
    (hcount : (T:ℝ) * Fintype.card E * a^2 / (4*tau^3) ≤ L) :
    (1 - 1/Real.exp 1 - 4*tau) * g (Finset.univ.image o) ≤
      average (fun seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T) =>
        g (greedyOutput part rule g seed)) := by
  have hO : 0 ≤ g (Finset.univ.image o) := le_trans hM.le hMo
  have he2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have he0 : 0 ≤ 1/Real.exp 1 := by positivity
  have hehalf : 1/Real.exp 1 ≤ (1:ℝ)/2 := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  have hc : 0 ≤ (1 - 1/Real.exp 1 - 3*tau) * g (Finset.univ.image o) :=
    mul_nonneg (by linarith) hO
  have hb := greedy_failure_bound part rule g hM htau hg ha hL hcount
    (initialState E a T)
  have havg := average_on_good (fun seed : Fin T → OracleSeed E a T L =>
      tableValue g (greedyRun part rule g seed).2)
    (adaptiveBad (greedyStep part rule g) (estimationBad part g M tau)
      T (initialState E a T))
    (fun _ => tableValue_nonneg g hmono hg0 _)
    (fun seed hgood => greedyRun_good part rule g o ho hmono hsub hg0 hM.le hMo
        hg ha htau.le htau1 hscale seed hgood)
  rw [greedyRun_expectation]
  calc
    _ ≤ (1-tau) * ((1 - 1/Real.exp 1 - 3*tau) * g (Finset.univ.image o)) := by
      have hs : 1 - 1/Real.exp 1 - 4*tau ≤
          (1-tau)*(1 - 1/Real.exp 1 - 3*tau) := by
        nlinarith [mul_nonneg htau.le he0, sq_nonneg tau]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hs hO
    _ ≤ (1 - probability (adaptiveBad (greedyStep part rule g)
        (estimationBad part g M tau) T (initialState E a T))) *
          ((1 - 1/Real.exp 1 - 3*tau) * g (Finset.univ.image o)) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_left hb 1) hc
    _ ≤ _ := havg

lemma categorical_expected {E : Type*} [Fintype E] [DecidableEq E]
    {a T L : ℕ} [NeZero T] (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    {tau : ℝ} (ha : 0 < a) (htau : 0 < tau) (htau1 : tau ≤ 1/8)
    (hscale : (a:ℝ)^2 ≤ tau*T) (hL : 0 < L)
    (hcount : (T:ℝ) * Fintype.card E * a^2 / (4*tau^3) ≤ L)
    (S : Finset E) (hS : PartitionFeasible part S) :
    (1 - 1/Real.exp 1 - 4*tau) * g S ≤
      average (fun seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T) =>
        g (greedyOutput part rule g seed)) := by
  have hnonneg : ∀ U, 0 ≤ g U := fun U => by
    rw [← hg0]
    exact hmono (Finset.empty_subset U)
  obtain ⟨e, _⟩ := rule.surjective ⟨0,ha⟩
  have hE : (Finset.univ : Finset E).Nonempty := ⟨e, Finset.mem_univ e⟩
  obtain ⟨emax, _, hmax⟩ := Finset.univ.exists_max_image (fun e : E => g {e}) hE
  have hbound := boundedMarginals_of_submodular g hmono hsub hg0
    (fun e => hmax e (Finset.mem_univ _))
  by_cases hM : 0 < g {emax}
  · obtain ⟨o, ho, hopt⟩ := exists_optimal_assignment part rule.surjective g hmono
    have havg := greedyOutput_expected part rule g o ho hmono hsub hg0 hM
      (hopt {emax} (partitionFeasible_singleton part emax)) hbound ha htau htau1
      hscale hL hcount
    have he2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hehalf : 1/Real.exp 1 ≤ (1:ℝ)/2 := by
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      linarith
    exact (mul_le_mul_of_nonneg_left (hopt S hS) (by linarith)).trans havg
  · have hM0 : g {emax} = 0 := le_antisymm (not_lt.mp hM) (hnonneg _)
    rw [hM0] at hbound
    rw [zero_of_boundedMarginals_zero g hg0 hbound S, mul_zero]
    exact average_nonneg (fun _ => hnonneg _)

noncomputable def binaryGreedyOutput {E : Type*} [Fintype E] [DecidableEq E]
    {a b L : ℕ} (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (bits : BinaryOracleIndex E a b L → Bool) : Finset E :=
  greedyOutput part rule g (binarySeedEquiv E a b L bits)

lemma binaryGreedyOutput_feasible {E : Type*} [Fintype E] [DecidableEq E]
    {a b L : ℕ} (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (bits : BinaryOracleIndex E a b L → Bool) :
    PartitionFeasible part (binaryGreedyOutput part rule g bits) :=
  greedyOutput_feasible part rule g _

lemma binaryGreedyOutput_expected {E : Type*} [Fintype E] [DecidableEq E]
    {a b L : ℕ} (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    {tau : ℝ} (ha : 0 < a) (htau : 0 < tau) (htau1 : tau ≤ 1/8)
    (hscale : (a:ℝ)^2 ≤ tau*(2^b:ℕ)) (hL : 0 < L)
    (hcount : ((2^b:ℕ):ℝ)*Fintype.card E*a^2/(4*tau^3) ≤ L)
    (S : Finset E) (hS : PartitionFeasible part S) :
    (1 - 1/Real.exp 1 - 4*tau) * g S ≤
      average (fun bits : BinaryOracleIndex E a b L → Bool =>
        g (binaryGreedyOutput part rule g bits)) := by
  simp only [binaryGreedyOutput]
  rw [average_equiv (binarySeedEquiv E a b L) _
    (fun seed => g (greedyOutput part rule g seed)) (fun _ => rfl)]
  exact categorical_expected part rule g hmono hsub hg0 ha htau htau1 hscale hL hcount S hS

end MetricKMedianRecovery.Categorical.Selected

end OAI
