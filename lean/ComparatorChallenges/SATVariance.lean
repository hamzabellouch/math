import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

abbrev Assignment (n : ℕ) := Fin n → Bool

def Clause (n k : ℕ) :=
  (s : {s : Finset (Fin n) // s.card = k}) × (s.1 → Bool)

instance clauseFintype (n k : ℕ) : Fintype (Clause n k) := by
  classical
  unfold Clause
  infer_instance

instance clauseMeasurableSpace (n k : ℕ) : MeasurableSpace (Clause n k) := ⊤

instance clauseMeasurableSingletonClass (n k : ℕ) :
    MeasurableSingletonClass (Clause n k) := ⟨fun _ => trivial⟩

def Satisfies {n k : ℕ} (c : Clause n k) (a : Assignment n) : Prop :=
  ∃ v : c.1.1, a v = c.2 v

abbrev Stream (n k : ℕ) := ℕ → Clause n k

def clauseLaw (n k : ℕ) : Measure (Clause n k) := uniformOn Set.univ

def streamLaw (n k : ℕ) : Measure (Stream n k) :=
  Measure.infinitePi (fun _ : ℕ => clauseLaw n k)

def PrefixSAT {n k : ℕ} (ω : Stream n k) (m : ℕ) : Prop :=
  ∃ a : Assignment n, ∀ i < m, Satisfies (ω i) a

def firstFailure {n k : ℕ} (ω : Stream n k) : ℕ∞ :=
  sInf ((fun m : ℕ => (m : ℕ∞)) '' {m | ¬ PrefixSAT ω m})

def H {n k : ℕ} (ω : Stream n k) : ℝ := (firstFailure ω).toNat

def cap (n : ℕ) (B : ℝ) : ℕ := ⌊B * n⌋₊

def T {n k : ℕ} (B : ℝ) (ω : Stream n k) : ℝ :=
  (min (firstFailure ω) (cap n B : ℕ∞)).toNat

def ell (k n : ℕ) : ℝ :=
  if k = 3 then Real.log (Real.exp 1 * n) else 1

def U (k : ℕ) : ℝ := Real.log 2 / (-Real.log (1 - ((2 : ℝ) ^ k)⁻¹))

theorem variance_main (k : ℕ) (hk : 3 ≤ k) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, k ≤ n →
      variance (H : Stream n k → ℝ) (streamLaw n k) ≤ C * n * ell k n) ∧
    (∀ B : ℝ, 0 < B → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, k ≤ n →
      variance (T B : Stream n k → ℝ) (streamLaw n k) ≤ C * n * ell k n) ∧
    (∃ c : ℝ, 0 < c ∧
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ≤ n →
        c * n ≤ variance (H : Stream n k → ℝ) (streamLaw n k)) ∧
      (∀ B : ℝ, U k < B → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ≤ n →
        c * n ≤ variance (T B : Stream n k → ℝ) (streamLaw n k))) := by
  sorry

end RandomKSAT

end

end OAI
