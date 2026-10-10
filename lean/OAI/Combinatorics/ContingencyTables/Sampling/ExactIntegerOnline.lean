import OAI.Combinatorics.ContingencyTables.Sampling.ExactIntegerRetry
import OAI.Combinatorics.ContingencyTables.Machines.OnlineIntegerRetry
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordExecution
import OAI.Combinatorics.ContingencyTables.Machines.IntegerMatrixProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseWordProgram

namespace OAI

/-! # The concrete fair-bit integer trial used by exact correction -/

namespace ContingencyTables.ExactIntegerOnline
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open ExactIntegerChoice ExactIntegerPrograms FirstSuccess ResidualMixture
open scoped BigOperators Classical

def trialBits (w : List ℕ) : ℕ := Nat.clog 2 w.sum

def trialBitsRealizer : Realizer trialBits :=
  composition listSum DensePrograms.ceilLogTwoRealizer

lemma polynomial_trialBits : PolynomialTime trialBitsRealizer :=
  polynomial_composition polynomial_listSum DensePrograms.polynomial_ceilLogTwo

def trial (w : List ℕ) : Experiment (Option ℕ) :=
  FiniteWordExecution.experiment trialBits weightedIndex w

noncomputable def trialRealizer : OnlineTree.Realizer trial :=
  FiniteWordExecution.realizer trialBitsRealizer weightedIndexRealizer

lemma trialBits_le_weight (w : List ℕ) : trialBits w ≤ weight w := by
  rw [trialBits,DensePrograms.clog_two_eq_size_pred]
  exact (Nat.size_le_size (Nat.sub_le _ _)).trans (IntegerMatrixPrograms.sum_size_le_weight w)

theorem polynomial_trial : OnlineTree.PolynomialTime trialRealizer := by
  apply OnlineTree.work_remeasure
    (FiniteWordExecution.work_realizer polynomial_trialBits polynomial_weightedIndex)
    (2*Polynomial.X)
  intro w
  have hb:=trialBits_le_weight w
  simp only [FiniteWordExecution.wordMeasure,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_X]
  omega

private lemma map_expectation {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (p : RationalLaw X) (f : X → Y) (g : Y → ℚ) :
    (∑ y,(mapLaw p f).mass y*g y)=∑ x,p.mass x*g (f x) := by
  simp only [mapLaw,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

private lemma average_expectation {Y : Type*} [Fintype Y] [DecidableEq Y]
    (k : ℕ) (f : (Fin k → Bool) → Y) (g : Y → ℚ) :
    average (fun bits => g (f bits))=
      ∑ y,(mapLaw (uniformLaw (α := Fin k → Bool)) f).mass y*g y := by
  rw [map_expectation]
  simp only [average,uniformLaw,uniformMass,Fintype.card_fun,Fintype.card_bool,
    Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,one_div,inv_mul_eq_div,Finset.sum_div]

/-- The compiled variable-length trial has precisely the integer-grid
probabilities, with the unused suffix of the binary range returning none. -/
theorem trial_mean {r : ℕ} (w : Fin r → ℕ) (h : 0<totalWeight w) (g : Option ℕ → ℚ) :
    (trial (List.ofFn w)).mean g=
      ∑ y : Option (Fin r),
        (trialLaw w h (Nat.le_pow_clog (by decide : 1<2) (totalWeight w))).mass y*
          g (y.map Fin.val) := by
  let k:=Nat.clog 2 (totalWeight w)
  let hQ:=Nat.le_pow_clog (by decide : 1<2) (totalWeight w)
  have hL : trialBits (List.ofFn w)=k := by
    rw [trialBits,List.sum_ofFn]
    rfl
  have he : trial (List.ofFn w)=(OnlineWord.prepend k []).map
      (fun bs => weightedIndex (List.ofFn w,bs)) := by
    unfold trial FiniteWordExecution.experiment FiniteWordExecution.source
    rw [hL]
  rw [he,Experiment.mean_map,OnlineWord.mean_prepend_nil]
  simp_rw [weightedIndex_ofFn w h hQ]
  rw [average_expectation k (fun bits => weightedTrial w h hQ (FairBits.binaryWordEquiv k bits))
    (fun y => g (y.map Fin.val))]
  have hlaw : mapLaw (uniformLaw (α := Fin k → Bool))
      (fun bits => weightedTrial w h hQ (FairBits.binaryWordEquiv k bits))=trialLaw w h hQ := by
    rw [←FairBits.map_equiv (FairBits.binaryWordEquiv k),FairBits.uniform_equiv]
  rw [hlaw]

private lemma retry_mass_succ {B : Type*} [Fintype B] [DecidableEq B]
    (p : RationalLaw (Option B)) (N : ℕ) (y : Option B) :
    (retryLaw p (fun b => b.map some) none (N+1)).mass y=
      (y.elim 0 (fun b => p.mass (some b)))+
        p.mass none*(retryLaw p (fun b => b.map some) none N).mass y := by
  rw [retryLaw,retryStep_mass]
  cases y <;> simp [successMass,failureMass]

/-- Mean preservation for every finite prefix allows the online loop to
reuse the already proved exact rational retry law. -/
lemma prefix_mean {A B C : Type} [Fintype B] [DecidableEq B]
    (f : A → Experiment (Option C)) (a : A) (p : RationalLaw (Option B)) (e : B → C)
    (hf : ∀ g : Option C → ℚ,(f a).mean g=∑ y,p.mass y*g (y.map e))
    (N : ℕ) (g : Option C → ℚ) :
    (OnlineIntegerRetry.prefixExperiment (f := f) a N).mean g=
      ∑ y,(retryLaw p (fun b => b.map some) none N).mass y*g (y.map e) := by
  induction N with
  | zero => simp [OnlineIntegerRetry.prefixExperiment,Experiment.mean,retryLaw,pointLaw]
  | succ N ih =>
    rw [OnlineIntegerRetry.prefixExperiment,Experiment.mean_bind,hf]
    simp only [Fintype.sum_option,Option.map_none,Option.map_some,Option.elim_none,
      Option.elim_some,Experiment.mean,ih]
    simp_rw [retry_mass_succ]
    simp only [Option.elim_none,Option.elim_some,zero_add]
    simp only [add_mul,Finset.sum_add_distrib,mul_assoc]
    rw [←Finset.mul_sum]
    ring

theorem integer_prefix_mean {r : ℕ} (w : Fin r → ℕ) (h : 0<totalWeight w)
    (N : ℕ) (g : Option ℕ → ℚ) :
    (OnlineIntegerRetry.prefixExperiment (f := trial) (List.ofFn w) N).mean g=
      ∑ y,(retryIntegerLaw w h
        (Nat.le_pow_clog (by decide : 1<2) (totalWeight w)) N).mass y*g (y.map Fin.val) :=
  prefix_mean trial (List.ofFn w) _ Fin.val (trial_mean w h) N g

theorem integer_prefix_failure {r : ℕ} (w : Fin r → ℕ) (h : 0<totalWeight w) (N : ℕ) :
    (OnlineIntegerRetry.prefixExperiment (f := trial) (List.ofFn w) N).mean
      (fun y => if y=none then 1 else 0)=
        (failure w (Q := 2^Nat.clog 2 (totalWeight w)))^N := by
  rw [integer_prefix_mean w h]
  simp only [Option.map_eq_none_iff,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,retryIntegerLaw_none]

end ContingencyTables.ExactIntegerOnline

end OAI
