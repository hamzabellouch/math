import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.InitialState2

namespace OAI

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

lemma greedyOutput_expected {E : Type*} [Fintype E] [DecidableEq E]
    {a T L : ℕ} [NeZero T] (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (o : Fin a → E) (ho : ∀ j, part (o j) = j)
    (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    {M tau : ℝ} (hM : 0 < M) (hMo : M ≤ g (Finset.univ.image o))
    (hg : BoundedMarginals g M) (ha : 0 < a) (htau : 0 < tau) (htau1 : tau ≤ 1/8)
    (hscale : (a:ℝ)^2 ≤ tau*T) (hL : 0 < L)
    (hcount : (T:ℝ) * Fintype.card E * a^2 / (4*tau^3) ≤ L) :
    (1 - 1/Real.exp 1 - 4*tau) * g (Finset.univ.image o) ≤
      average (fun seed : (Fin T → OracleSeed E a T L) × (Fin a → Fin T) =>
        g (greedyOutput part hp g seed)) := by
  have hO : 0 ≤ g (Finset.univ.image o) := le_trans hM.le hMo
  have he2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have he0 : 0 ≤ 1/Real.exp 1 := by positivity
  have hehalf : 1/Real.exp 1 ≤ (1:ℝ)/2 := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  have hc : 0 ≤ (1 - 1/Real.exp 1 - 3*tau) * g (Finset.univ.image o) :=
    mul_nonneg (by linarith) hO
  have hb := greedy_failure_bound part hp g hM htau hg ha hL hcount
    (initialState E a T)
  have havg := average_on_good (fun seed : Fin T → OracleSeed E a T L =>
      tableValue g (greedyRun part hp g seed).2)
    (adaptiveBad (greedyStep part hp g) (estimationBad part g M tau)
      T (initialState E a T))
    (fun _ => tableValue_nonneg g hmono hg0 _)
    (fun seed hgood => greedyRun_good part hp g o ho hmono hsub hg0 hM.le hMo
        hg ha htau.le htau1 hscale seed hgood)
  rw [greedyRun_expectation]
  calc
    _ ≤ (1-tau) * ((1 - 1/Real.exp 1 - 3*tau) * g (Finset.univ.image o)) := by
      have hs : 1 - 1/Real.exp 1 - 4*tau ≤
          (1-tau)*(1 - 1/Real.exp 1 - 3*tau) := by
        nlinarith [mul_nonneg htau.le he0, sq_nonneg tau]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hs hO
    _ ≤ (1 - probability (adaptiveBad (greedyStep part hp g)
        (estimationBad part g M tau) T (initialState E a T))) *
          ((1 - 1/Real.exp 1 - 3*tau) * g (Finset.univ.image o)) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_left hb 1) hc
    _ ≤ _ := havg

end MetricKMedianRecovery.Categorical

namespace MetricKMedianRecovery.Categorical
open FiniteSampling

section Feasible
variable {E : Type*} [Fintype E] [DecidableEq E] {a : ℕ}

def PartitionFeasible (part : E → Fin a) (S : Finset E) : Prop :=
  ∀ j, (S.filter (fun e => part e = j)).card ≤ 1

omit [Fintype E] in
lemma diminishing_of_submodular (g : SetFunction E) (hmono : Monotone g)
    (hsub : ∀ U V : Finset E, U ⊆ V → ∀ e, e ∉ V →
      g (insert e V) - g V ≤ g (insert e U) - g U) : Diminishing g := by
  intro U V hUV e
  by_cases he : e ∈ V
  · simp only [marginal, Finset.insert_eq_of_mem he, sub_self]
    exact sub_nonneg.mpr (hmono (Finset.subset_insert _ _))
  · exact hsub U V hUV e he

omit [Fintype E] [DecidableEq E] in
lemma partitionFeasible_singleton (part : E → Fin a) (e : E) :
    PartitionFeasible part {e} := by
  intro j
  exact (Finset.card_filter_le _ _).trans (by simp)

omit [Fintype E] in
lemma partitionFeasible_image (part : E → Fin a) (o : Fin a → E)
    (ho : ∀ j, part (o j) = j) : PartitionFeasible part (Finset.univ.image o) := by
  intro j
  apply (Finset.card_le_card ?_).trans (show ({o j} : Finset E).card ≤ 1 by simp)
  intro e he
  obtain ⟨he, hp⟩ := Finset.mem_filter.mp he
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
  rw [ho] at hp
  simp [hp]

omit [Fintype E] in

lemma exists_filling (part : E → Fin a) (hp : Function.Surjective part)
    (S : Finset E) (hS : PartitionFeasible part S) :
    ∃ o : Fin a → E, (∀ j, part (o j) = j) ∧ S ⊆ Finset.univ.image o := by
  classical
  have hc : ∀ j : Fin a, ∃ e, part e = j ∧ ∀ f ∈ S, part f = j → f = e := by
    intro j
    by_cases hn : (S.filter (fun e => part e = j)).Nonempty
    · obtain ⟨e, he⟩ := hn
      refine ⟨e, (Finset.mem_filter.mp he).2, ?_⟩
      intro f hf hp
      exact (Finset.card_le_one.mp (hS j)) _ (Finset.mem_filter.mpr ⟨hf,hp⟩) _ he
    · obtain ⟨e, he⟩ := hp j
      refine ⟨e, he, ?_⟩
      intro f hf hp
      exact False.elim (hn ⟨f, Finset.mem_filter.mpr ⟨hf,hp⟩⟩)
  choose o ho hfill using hc
  refine ⟨o, ho, ?_⟩
  intro e he
  exact Finset.mem_image.mpr ⟨part e, Finset.mem_univ _, (hfill _ e he rfl).symm⟩

lemma exists_optimal_assignment (part : E → Fin a) (hp : Function.Surjective part)
    (g : SetFunction E) (hmono : Monotone g) :
    ∃ o : Fin a → E, (∀ j, part (o j) = j) ∧
      ∀ S, PartitionFeasible part S → g S ≤ g (Finset.univ.image o) := by
  classical
  let A : Finset (Fin a → E) := Finset.univ.filter (fun o => ∀ j, part (o j) = j)
  have hA : A.Nonempty := by
    choose o ho using hp
    exact ⟨o, Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho⟩⟩
  obtain ⟨o, ho, hmax⟩ := A.exists_max_image (fun o => g (Finset.univ.image o)) hA
  refine ⟨o, (Finset.mem_filter.mp ho).2, ?_⟩
  intro S hS
  obtain ⟨c, hc, hfill⟩ := exists_filling part hp S hS
  exact (hmono hfill).trans (hmax c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩))

omit [Fintype E] in
lemma zero_of_boundedMarginals_zero (g : SetFunction E) (hg0 : g ∅ = 0)
    (hg : BoundedMarginals g 0) (S : Finset E) : g S = 0 := by
  induction S using Finset.induction_on with
  | empty => exact hg0
  | @insert e S he ih =>
    have h := hg e S
    unfold marginal at h
    linarith

end Feasible
end MetricKMedianRecovery.Categorical

end OAI
