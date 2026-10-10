import OAI.NumberTheory.Jacobsthal.Estimates.FinitePairOccurrence
import OAI.NumberTheory.Jacobsthal.Estimates.RepeatedStepRowBound

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.RepeatedPairEvents
open _root_.Set _root_.MeasureTheory ProbabilityTheory
open FinitePathGeometry PrimeHistories PrimeKilledChain ActualProcessCoupling ActualFlagInvariant PersistentFailureFlag
open RepeatedStepRowBound

variable {w ell S : ℝ} {start : Node}

def primeRepeatPair {n : ℕ} (lab : ℕ → Fin n) (X U : ℝ) (G : Set (ChainState w ell S start)) :
    ChainState w ell S start × ChainState w ell S start → Prop
  | (some h,some k) => h.primes ≠ [] ∧ h.node.ratio ≤ U ∧ some h ∈ G ∧
      lab (h.primes.getLastD 0)=lab (k.primes.getLastD 0) ∧ X ≤ k.node.cutoff
  | _ => False

noncomputable def goodRepeatPair {n : ℕ} (lab : ℕ → Fin n) (X U : ℝ) (G : Set (ChainState w ell S start))
    (v mesh : ℝ) (N : ℕ) : Set (FlagState (JointState w ell S start) × FlagState (JointState w ell S start)) :=
  {xy | GoodAt v mesh N xy.1.1 ∧ GoodAt v mesh N xy.2.1 ∧ primeRepeatPair lab X U G (xy.1.1.1,xy.2.1.1)}

theorem goodRepeatPair_measurable {n : ℕ} (lab : ℕ → Fin n) (X U : ℝ) (G : Set (ChainState w ell S start))
    (v mesh : ℝ) (N : ℕ) : MeasurableSet (goodRepeatPair lab X U G v mesh N) := by
  have hp : MeasurableSet {pq : ChainState w ell S start × ChainState w ell S start | primeRepeatPair lab X U G pq} :=
    (Set.to_countable _).measurableSet
  have hm : Measurable (fun xy : FlagState (JointState w ell S start) × FlagState (JointState w ell S start) =>
      (xy.1.1.1,xy.2.1.1)) := by fun_prop
  exact ((measurable_fst.comp measurable_fst) (GoodAt_measurable v mesh N)).inter
    (((measurable_fst.comp measurable_snd) (GoodAt_measurable v mesh N)).inter (hm hp))

theorem primeRepeatPair_left {n : ℕ} (lab : ℕ → Fin n) {X U : ℝ} {G : Set (ChainState w ell S start)}
    {p q : ChainState w ell S start} (hp : primeRepeatPair lab X U G (p,q)) :
    ∃ h : History w ell S start,p=some h ∧ h.primes ≠ [] ∧ h.node.ratio ≤ U ∧ p ∈ G := by
  cases p with
  | none => exact False.elim hp
  | some h =>
    cases q with
    | none => exact False.elim hp
    | some k => exact ⟨h,rfl,hp.1,hp.2.1,hp.2.2.1⟩

theorem primeRepeatPair_next {n : ℕ} (lab : ℕ → Fin n) {X U : ℝ} {G : Set (ChainState w ell S start)}
    (h : History w ell S start) (y : FlagState (JointState w ell S start))
    (hp : primeRepeatPair lab X U G (some h,y.1.1)) : nextRepeat lab X h y := by
  cases hy : y.1.1 with
  | none => rw [hy] at hp; exact False.elim hp
  | some k =>
    rw [hy] at hp
    unfold nextRepeat
    rw [hy]
    exact hp.2.2.2

theorem goodAt_enlarge {v mesh : ℝ} (hm : 0 ≤ mesh) {n N : ℕ} (hn : n ≤ N)
    (q : JointState w ell S start) (hq : GoodAt v mesh n q) : GoodAt v mesh N q := by
  rcases q with ⟨p,y⟩
  cases p with
  | none => cases y <;> exact hq
  | some p =>
    cases y with
    | inr u => exact False.elim hq
    | inl y =>
      refine ⟨hq.1,hq.2.1,hq.2.2.1,hq.2.2.2.trans ?_⟩
      have hnR : (n:ℝ) ≤ N := by exact_mod_cast hn
      nlinarith [mul_le_mul_of_nonneg_right hnR hm]
end NumberTheoryLean.RepeatedPairEvents


end Erdos970

end OAI
