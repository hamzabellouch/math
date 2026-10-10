import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

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

def SetSAT {u s : ℕ} (S : Finset (Assignment u)) (ω : Stream u s) (g : ℕ) : Prop :=
  ∃ a ∈ S, ∀ i < g, Satisfies (ω i) a

def blockKill (u s : ℕ) (S : Finset (Assignment u)) (g : ℕ) : ℝ :=
  (streamLaw u s {ω | ¬ SetSAT S ω g}).toReal

def favg.{u_1} {α : Type u_1} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

def clauseStep (u s : ℕ) (f : Finset (Assignment u) → ℝ)
    (S : Finset (Assignment u)) : ℝ :=
  favg fun c : Clause u s => f (S.filter (Satisfies c))

def alive (u : ℕ) (S : Finset (Assignment u)) : ℝ := if S.Nonempty then 1 else 0

def survival (u s : ℕ) (S : Finset (Assignment u)) (m : ℕ) : ℝ :=
  (clauseStep u s)^[m] (alive u) S

def lifetime (u s : ℕ) (S : Finset (Assignment u)) : ℝ := ∑' m, survival u s S m

theorem sharpness (k : ℕ) (hk : 3 ≤ k) :
    (∀ γ D A : ℝ, γ < (k : ℝ) / ((k-1 : ℕ) : ℝ) → 0 < D → 0 < A →
      ∀ N : ℕ, ∃ u : ℕ, N ≤ u ∧ k ≤ u ∧ ∃ S : Finset (Assignment u),
        S.Nonempty ∧ A * (u : ℝ) ^ (-((k-1 : ℕ) : ℝ)) ≤ blockKill u (k-1) S 1 ∧
        D * (blockKill u (k-1) S 1) ^ (-γ) < lifetime u k S) ∧
    (∃ u : ℕ → ℕ, ∃ S : ∀ g, Finset (Assignment (u g)),
      (∀ g, 2 ≤ g → k ≤ u g ∧ (S g).Nonempty) ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun g => blockKill (u g) (k-1) (S g) 1 - blockKill (u g) k (S g) g)
        (fun g => ((2 : ℝ)^k)⁻¹ * (g : ℝ)^(-((k-1 : ℕ) : ℝ)))) ∧
    (¬ ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO Filter.atTop e (fun g => (g : ℝ)^(-((k-1 : ℕ) : ℝ))) ∧
      ∀ u, k ≤ u → ∀ S : Finset (Assignment u), S.Nonempty → ∀ g, 2 ≤ g →
        blockKill u (k-1) S 1 - e g ≤ blockKill u k S g) := by
  sorry

end RandomKSAT

end

end OAI
