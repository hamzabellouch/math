import OAI.Combinatorics.KMedianRecovery.Refined.ThresholdInput
import OAI.Combinatorics.KMedianRecovery.Refined.CheckedInput
import OAI.Combinatorics.KMedianRecovery.Refined.Work

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery

open MetricKMedian.Binary

def CompanionThresholdInput : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ f : MetricKMedian.Instance → List Bool,
    Nonempty (PolyProgram MetricKMedian.InstanceProgram.encode id f) ∧
    ∀ I, MetricKMedian.Correct ε I (f I)

private lemma quote_eq (xs : List Bool) :
    quote xs = xs.flatMap (fun b => [true, b]) ++ [false] := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [quote, ih]

private def first (xs : List Bool) : List Bool :=
  (WordTransducer.projecting false).run none xs

private lemma first_pair (x y : List Bool) : first (pairBits (x, y)) = x := by
  simpa only [first, pairBits, ← quote_eq, Bool.false_eq_true, ite_false] using
    WordTransducer.projecting_pair false x y

private noncomputable def totalProgram {f : MetricKMedian.Instance → List Bool}
    (P : PolyProgram MetricKMedian.InstanceProgram.encode id f) :
    PolyProgram id id (fun xs => f (CheckedInput.checked (MetricKMedian.InputParser.raw
      (first (first xs))))) :=
  (((WordTransducer.projecting false).program.comp
    (WordTransducer.projecting false).program).comp CheckedInput.parseProgram).comp P

private noncomputable def algorithm {f : MetricKMedian.Instance → List Bool}
    (P : PolyProgram MetricKMedian.InstanceProgram.encode id f) : BinaryRandomizedAlgorithm where
  randomBits := 0
  run p := f (CheckedInput.checked (MetricKMedian.InputParser.raw (first (first (pairBits p)))))
  computation := ((totalProgram P).recode pairBits (fun _ => rfl) (fun _ => rfl)).stock
  finiteWorkAlphabet := ((totalProgram P).recode pairBits (fun _ => rfl) (fun _ => rfl)).finite_work

private lemma algorithm_run {f : MetricKMedian.Instance → List Bool}
    (P : PolyProgram MetricKMedian.InstanceProgram.encode id f) (I : Input) (ζ : ℝ)
    (s : Seed (algorithm P) I ζ) :
    (algorithm P).run (queryBits I ζ, List.ofFn s) = f I.asInstance := by
  simp only [algorithm, queryBits, first_pair, ← I.asInstance_bits,
    MetricKMedian.InputParser.raw_encoded, CheckedInput.checked_view]

theorem refined_recovery_conditional (H : CompanionThresholdInput) : refinedRecoveryClaim := by
  intro bound ε L₀ μ hε _ _ _ _
  obtain ⟨f, ⟨P⟩, hf⟩ := H ε hε
  refine ⟨algorithm P, zero_random_polynomialWork _ rfl bound, ?_⟩
  intro I _ ζ hζ _
  have houtput (s : Seed (algorithm P) I ζ) :
      ∃ S : Finset I.Point, I.metric.Feasible S ∧ output (algorithm P) I ζ s = S ∧
        (I.metric.cost S : ℝ) ≤ (1+2/Real.exp 1+ε)*MetricKMedian.optimum I.asInstance := by
    obtain ⟨S, hSF, hS, hk, hout, hcost⟩ := hf I.asInstance
    refine ⟨S, ⟨hSF, hk, fun _ => hS⟩, ?_, ?_⟩
    · rw [output, algorithm_run, hout, I.decode_mask S hSF]
    · rwa [I.asInstance_cost] at hcost
  refine ⟨fun s => by obtain ⟨S, hS, he, _⟩ := houtput s; exact he.symm ▸ hS, ?_⟩
  intro C
  have hall (s : Seed (algorithm P) I ζ) :
      (I.metric.cost (output (algorithm P) I ζ s) : ℝ) ≤
        (1+2/Real.exp 1+ε)*(I.metric.cost C.centers : ℝ) := by
    obtain ⟨S, _, he, hc⟩ := houtput s
    rw [he]
    exact hc.trans (mul_le_mul_of_nonneg_left (I.optimum_le_comparison C) (by positivity))
  have hprob : successProbability (algorithm P) I ζ
      ((1+2/Real.exp 1+ε)*(I.metric.cost C.centers : ℝ)) = 1 := by
    classical
    simp only [successProbability, hall, Finset.filter_true, Finset.card_univ,
      Seed, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
      Nat.cast_ofNat]
    exact div_self (show (2 : ℝ) ^ seedLength (algorithm P) I ζ ≠ 0 by positivity)
  rw [hprob]
  linarith

end MetricKMedianRecovery.RefinedRecovery

end OAI
