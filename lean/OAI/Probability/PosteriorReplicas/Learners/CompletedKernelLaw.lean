import OAI.Probability.PosteriorReplicas.Learners.CompletedKernelLearner

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal RealInnerProductSpace unitInterval
noncomputable section
namespace PosteriorRegression

lemma map_prod_eq_bind {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [Countable A] [MeasurableSingletonClass A]
    (μ : Measure A) (ν : Measure B) [SFinite ν] {f : A × B → C} (hf : Measurable f) :
    (μ.prod ν).map f = μ.bind (fun a => ν.map (fun b => f (a,b))) := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.prod_apply (hf hs),
    Measure.bind_apply hs (measurable_of_countable _).aemeasurable]
  apply lintegral_congr
  intro a
  exact (Measure.map_apply (hf.comp measurable_prodMk_left) hs).symm

namespace CompletedKernelLearner
open Learner

def Realization.stepMap {d M T : ℕ} {K : CompletedKernelLearner d M} (R : Realization K)
    (s : UnitSphere d) (x : Samples d T) (i : Fin T) : RunStatus M × unitInterval → RunStatus M
  | (.inr done,_) => .inr done
  | (.inl a,u) => destStatus (i.val+1) (R.transition (i.val+1) a (x i,⟪x i,s.val⟫) u)

lemma Realization.measurable_stepMap {d M T : ℕ} {K : CompletedKernelLearner d M} (R : Realization K)
    (s : UnitSphere d) (x : Samples d T) (i : Fin T) : Measurable (R.stepMap s x i) := by
  apply measurable_from_prod_countable_right
  intro r
  rcases r with a | done
  · exact (measurable_of_finite (destStatus (i.val+1))).comp
      ((R.measurable_transition (i.val+1) a).comp (measurable_const.prodMk measurable_id))
  · exact measurable_const

lemma Realization.run_succ {d M T : ℕ} {K : CompletedKernelLearner d M} (R : Realization K)
    (s : UnitSphere d) (x : Samples d T) (n : ℕ) (hn : n<T) (ω : Coins T) :
    (R.toLearner T).run s ω x (n+1) =
      R.stepMap s x ⟨n,hn⟩ ((R.toLearner T).run s ω x n,ω ⟨n+1,by omega⟩) := by
  rw [Learner.run]
  cases (R.toLearner T).run s ω x n <;>
    simp only [dite_eq_left hn, Realization.toLearner, dite_eq_left (show n+1≤T by omega), stepMap, destStatus]

lemma Realization.measurable_run {d M T : ℕ} {K : CompletedKernelLearner d M} (R : Realization K)
    (s : UnitSphere d) (x : Samples d T) (n : ℕ) :
    Measurable (fun ω => (R.toLearner T).run s ω x n) := by
  induction n with
  | zero => exact (measurable_of_finite (destStatus 0)).comp (R.measurable_initial.comp (measurable_pi_apply 0))
  | succ n ih =>
    by_cases hn : n<T
    · simpa only [R.run_succ s x n hn, Function.comp_def] using
        (R.measurable_stepMap s x ⟨n,hn⟩).comp (ih.prodMk (measurable_pi_apply (⟨n+1,by omega⟩ : Fin (T+2))))
    · have he : (fun ω => (R.toLearner T).run s ω x (n+1)) = (fun ω => (R.toLearner T).run s ω x n) := by
        funext ω
        rw [Learner.run]
        cases (R.toLearner T).run s ω x n <;> simp [hn]
      rw [he]
      exact ih

lemma Realization.run_depends_prefix {d M T : ℕ} {K : CompletedKernelLearner d M} (R : Realization K)
    (s : UnitSphere d) (x : Samples d T) (n : ℕ) {ω ω' : Coins T}
    (hω : ∀ j : Fin (T+2), j.val≤n → ω j = ω' j) :
    (R.toLearner T).run s ω x n = (R.toLearner T).run s ω' x n := by
  induction n with
  | zero => exact congrArg (destStatus 0 ∘ R.initial) (hω 0 (by simp))
  | succ n ih =>
    have hprev := ih (fun j hj => hω j (by omega))
    by_cases hn : n<T
    · rw [R.run_succ s x n hn, R.run_succ s x n hn, hprev, hω ⟨n+1,by omega⟩ (by simp)]
    · rw [Learner.run,Learner.run,hprev]
      cases (R.toLearner T).run s ω' x n <;> simp [hn]

def fillCoins {T : ℕ} (A : Finset (Fin (T+2))) (u : A → unitInterval) : Coins T :=
  fun j => if hj : j∈A then u ⟨j,hj⟩ else 0

lemma measurable_fillCoins {T : ℕ} (A : Finset (Fin (T+2))) : Measurable (fillCoins A) := by
  apply Measurable.of_eval
  intro j
  by_cases hj : j∈A
  · simpa [fillCoins,hj] using (measurable_pi_apply (⟨j,hj⟩ : A))
  · simp [fillCoins,hj]

lemma indep_fresh_coin {T : ℕ} {Z : Type*} [MeasurableSpace Z] (n : ℕ)
    {f : Coins T → Z} (hf : Measurable f)
    (hprefix : ∀ ω ω', (∀ j : Fin (T+2), j.val≤n → ω j = ω' j) → f ω = f ω')
    (j : Fin (T+2)) (hj : n<j.val) : IndepFun f (fun ω => ω j) (coinsLaw T) := by
  classical
  let A := Finset.univ.filter (fun i : Fin (T+2) => i.val≤n)
  have hd : Disjoint A {j} := by
    simp only [Finset.disjoint_singleton_right, A, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hi : iIndepFun (fun i (ω : Coins T) => ω i) (coinsLaw T) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have hh := (hi.indepFun_finset A {j} hd (fun i => measurable_pi_apply i)).comp
    (hf.comp (measurable_fillCoins A)) (measurable_pi_apply (⟨j,Finset.mem_singleton_self j⟩ : ({j} : Finset (Fin (T+2)))))
  have he : (fun ω : Coins T => f (fillCoins A (fun i : A => ω i))) = f := by
    funext ω
    apply hprefix
    intro i hi
    simp [fillCoins, A, hi]
  simpa only [Function.comp_def, he] using hh

lemma Realization.step_law {d M T : ℕ} {K : CompletedKernelLearner d M} (R : Realization K)
    (s : UnitSphere d) (x : Samples d T) (i : Fin T) (r : RunStatus M) :
    volume.map (fun u => R.stepMap s x i (r,u)) = K.stepMeasure s x i r := by
  rcases r with a | done
  · change volume.map (destStatus (i.val+1) ∘ R.transition (i.val+1) a (x i,⟪x i,s.val⟫)) = _
    have hm : Measurable (R.transition (i.val+1) a (x i,⟪x i,s.val⟫)) :=
      (R.measurable_transition (i.val+1) a).comp (measurable_const.prodMk measurable_id)
    rw [← Measure.map_map (measurable_of_finite (destStatus (M := M) (i.val+1))) hm]
    rw [R.law_transition]
    rfl
  · simp [stepMap,stepMeasure,Measure.map_const]

lemma Realization.run_law {d M T : ℕ} {K : CompletedKernelLearner d M} (R : Realization K)
    (s : UnitSphere d) (x : Samples d T) (n : ℕ) :
    (coinsLaw T).map (fun ω => (R.toLearner T).run s ω x n) = K.runMeasure s x n := by
  induction n with
  | zero =>
    change (coinsLaw T).map (destStatus 0 ∘ (R.toLearner T).initialChoice) = _
    have hm : Measurable (R.toLearner T).initialChoice := R.measurable_initial.comp (measurable_pi_apply 0)
    rw [← Measure.map_map (measurable_of_finite (destStatus (M := M) 0)) hm, R.initial_law]
    rfl
  | succ n ih =>
    by_cases hn : n<T
    · have hi := indep_fresh_coin n (R.measurable_run s x n)
        (fun ω ω' hω => R.run_depends_prefix s x n hω) (⟨n+1,by omega⟩ : Fin (T+2)) (by simp)
      have hj := hi.map_prod_eq_prod_map_map (R.measurable_run s x n).aemeasurable
        (measurable_pi_apply (⟨n+1,by omega⟩ : Fin (T+2))).aemeasurable
      have hc : (coinsLaw T).map (fun ω => ω (⟨n+1,by omega⟩ : Fin (T+2))) = volume :=
        (measurePreserving_eval (fun _ : Fin (T+2) => (volume : Measure unitInterval)) ⟨n+1,by omega⟩).map_eq
      simp only [R.run_succ s x n hn]
      change (coinsLaw T).map (R.stepMap s x ⟨n,hn⟩ ∘ (fun ω => ((R.toLearner T).run s ω x n,ω ⟨n+1,by omega⟩))) = _
      rw [← Measure.map_map (R.measurable_stepMap s x _) ((R.measurable_run s x n).prodMk (measurable_pi_apply _)), hj, ih, hc,
        map_prod_eq_bind _ _ (R.measurable_stepMap s x _)]
      simp only [R.step_law,runMeasure,dite_eq_left hn]
    · have he : (fun ω => (R.toLearner T).run s ω x (n+1)) = (fun ω => (R.toLearner T).run s ω x n) := by
        funext ω
        rw [Learner.run]
        cases (R.toLearner T).run s ω x n <;> simp [hn]
      simpa only [he, runMeasure, dite_eq_right hn] using ih

lemma Realization.measurable_terminal {d M T : ℕ} {K : CompletedKernelLearner d M} (R : Realization K)
    (s : UnitSphere d) (x : Samples d T) :
    Measurable (fun ω => (R.toLearner T).terminal s ω x) :=
  (measurable_of_countable (finishState T)).comp (R.measurable_run s x T)

lemma Realization.terminal_law {d M T : ℕ} {K : CompletedKernelLearner d M} (R : Realization K)
    (s : UnitSphere d) (x : Samples d T) :
    (coinsLaw T).map (fun ω => (R.toLearner T).terminal s ω x) = K.terminalLaw s x := by
  change (coinsLaw T).map (finishState T ∘ fun ω => (R.toLearner T).run s ω x T) = _
  rw [← Measure.map_map (measurable_of_countable _) (R.measurable_run s x T),R.run_law]
  rfl

lemma Realization.measurable_estimate {d M T : ℕ} {K : CompletedKernelLearner d M} (R : Realization K)
    (s : UnitSphere d) (x : Samples d T) :
    Measurable (fun ω => (R.toLearner T).estimate s ω x) := by
  have hm : Measurable (fun z : (ℕ × State M) × unitInterval => R.output z.1.1 z.1.2 z.2) :=
    measurable_from_prod_countable_right (fun a => R.measurable_output a.1 a.2)
  exact hm.comp ((R.measurable_terminal s x).prodMk (measurable_pi_apply (⟨T+1,by omega⟩ : Fin (T+2))))

lemma Realization.estimate_law {d M T : ℕ} {K : CompletedKernelLearner d M} (R : Realization K)
    (s : UnitSphere d) (x : Samples d T) :
    (coinsLaw T).map (fun ω => (R.toLearner T).estimate s ω x) = K.estimateLaw s x := by
  let g : (ℕ × State M) × unitInterval → UnitSphere d := fun z => R.output z.1.1 z.1.2 z.2
  have hg : Measurable g :=
    measurable_from_prod_countable_right (fun a => R.measurable_output a.1 a.2)
  have hi := indep_fresh_coin T (R.measurable_terminal s x) (fun ω ω' hω =>
    congrArg (finishState T) (R.run_depends_prefix s x T hω)) (⟨T+1,by omega⟩ : Fin (T+2)) (by simp)
  have hj := hi.map_prod_eq_prod_map_map (R.measurable_terminal s x).aemeasurable
    (measurable_pi_apply (⟨T+1,by omega⟩ : Fin (T+2))).aemeasurable
  have hc : (coinsLaw T).map (fun ω => ω (⟨T+1,by omega⟩ : Fin (T+2))) = volume :=
    (measurePreserving_eval (fun _ : Fin (T+2) => (volume : Measure unitInterval)) ⟨T+1,by omega⟩).map_eq
  change (coinsLaw T).map (g ∘ (fun ω => ((R.toLearner T).terminal s ω x,ω ⟨T+1,by omega⟩))) = _
  rw [← Measure.map_map hg ((R.measurable_terminal s x).prodMk (measurable_pi_apply _)), hj,
    R.terminal_law, hc, map_prod_eq_bind _ _ hg]
  simp only [g, R.law_output, estimateLaw]

instance estimateLaw_probability {d M T : ℕ} (K : CompletedKernelLearner d M)
    (s : UnitSphere d) (x : Samples d T) : IsProbabilityMeasure (K.estimateLaw s x) := by
  rw [← K.realization.estimate_law s x]
  exact (Measure.isProbabilityMeasure_map_iff
    (K.realization.measurable_estimate s x).aemeasurable).mpr inferInstance

end CompletedKernelLearner
end PosteriorRegression
end

end OAI
