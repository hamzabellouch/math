import Mathlib

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- A finite graph given by its edge list. Zero couplings can encode missing edges.
Edges are indexed separately so parallel edges are counted separately. -/
structure FiniteGraph (n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  coupling : Fin m → ℝ
  coupling_nonneg : ∀ e, 0 ≤ coupling e
  no_loops : ∀ e, left e ≠ right e

abbrev Spins (n : ℕ) := Fin n → Bool

def spin (b : Bool) : ℝ := if b then 1 else -1

noncomputable def energy {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (σ : Spins n) : ℝ :=
  (∑ e, G.coupling e * spin (σ (G.left e)) * spin (σ (G.right e))) +
    ∑ v, h v * spin (σ v)

noncomputable def weight {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (σ : Spins n) : ℝ := Real.exp (energy G h σ)

def AgreesOn {n : ℕ} (S : Finset (Fin n)) (σ τ : Spins n) : Prop :=
  ∀ v ∈ S, σ v = τ v

noncomputable def constrainedSum {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (P : Spins n → Prop) : ℝ := by
  classical
  exact ∑ σ, if P σ then weight G h σ else 0

/-- Conditional probability of σ_I=a, with σ_J=b and σ_F=τ prescribed.
All sums are finite and all fields are finite real numbers. -/
noncomputable def conditionalProb {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (a b τ : Spins n) : ℝ :=
  constrainedSum G h (fun σ => AgreesOn I σ a ∧ AgreesOn J σ b ∧ AgreesOn F σ τ) /
    constrainedSum G h (fun σ => AgreesOn J σ b ∧ AgreesOn F σ τ)

/-- Edges remaining after DELETION, not pinning, of F. -/
def keptEdges {n m : ℕ} (G : FiniteGraph n m) (F : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter (fun e => G.left e ∉ F ∧ G.right e ∉ F)

abbrev KeptVertex {n : ℕ} (F : Finset (Fin n)) := {v : Fin n // v ∉ F}

/-- Open-edge adjacency together with the two separate terminal identifications.
No virtual identification of common pins is present: those vertices are absent. -/
def comparisonRel {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) (u v : KeptVertex F) : Prop :=
  (u.val ∈ I ∧ v.val ∈ I) ∨ (u.val ∈ J ∧ v.val ∈ J) ∨
    ∃ e ∈ ω, (G.left e = u.val ∧ G.right e = v.val) ∨
      (G.left e = v.val ∧ G.right e = u.val)

/-- The equivalence closure implements components of the contracted open graph. -/
def comparisonSetoid {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) : Setoid (KeptVertex F) :=
  Relation.EqvGen.setoid (comparisonRel G I J F ω)

noncomputable def clusterCount {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) : ℕ :=
  Nat.card (Quotient (comparisonSetoid G I J F ω))

/-- Zero-field FK weight with q=2 and p_e=1-exp(-2 K_e).
Parallel edges may be retained: the measure after summing them is the measure
for the summed parallel coupling. Loops created by contraction do not change
components and cancel from connection probabilities. -/
noncomputable def fkWeight {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (ω : Finset (Fin m)) : ℝ := by
  classical
  exact (2 : ℝ) ^ clusterCount G I J F ω *
    ∏ e ∈ keptEdges G F,
      if e ∈ ω then 1 - Real.exp (-2 * G.coupling e) else Real.exp (-2 * G.coupling e)

/-- Choose any i in I and j in J. The terminal connection is independent of
these choices because I and J are each identified. -/
noncomputable def qZero {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (i j : KeptVertex F) : ℝ := by
  classical
  exact (∑ ω ∈ (keptEdges G F).powerset,
    if (comparisonSetoid G I J F ω).r i j then fkWeight G I J F ω else 0) /
    ∑ ω ∈ (keptEdges G F).powerset, fkWeight G I J F ω

/-- Any probability mixture of source prescriptions. Full configurations
index the mixture, but only their restrictions to J are used. Thus this is
exactly the class of all mixtures on {-1,+1}^J. -/
noncomputable def mixtureProb {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (a τ : Spins n)
    (mix : Spins n → ℝ) : ℝ :=
  ∑ b, mix b * conditionalProb G h I J F a b τ

@[simp] lemma spin_true : spin true = 1 := rfl
@[simp] lemma spin_false : spin false = -1 := rfl

/-- The unnormalized I,J marginal with the common pins F fixed. -/
noncomputable def jointWeight {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ a b : Spins n) : ℝ :=
  constrainedSum G h (fun σ => AgreesOn I σ a ∧ AgreesOn J σ b ∧ AgreesOn F σ τ)

/-- Expectation in the unpinned finite Ising law. -/
noncomputable def expectation {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (f : Spins n → ℝ) : ℝ :=
  (∑ σ, weight G h σ * f σ) / ∑ σ, weight G h σ

/-- Arbitrary real background fields do not increase the spin covariance above the zero-field correlation. -/
def ArbitraryFieldCovarianceBound : Prop :=
  ∀ (n m : ℕ) (G : FiniteGraph n m) (h : Fin n → ℝ) (u v : Fin n),
    expectation G h (fun σ => spin (σ u) * spin (σ v)) -
      expectation G h (fun σ => spin (σ u)) * expectation G h (fun σ => spin (σ v)) ≤
    expectation G (fun _ => 0) (fun σ => spin (σ u) * spin (σ v))

lemma weight_pos {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (σ : Spins n) : 0 < weight G h σ := Real.exp_pos _

lemma constrainedSum_nonneg {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (P : Spins n → Prop) : 0 ≤ constrainedSum G h P := by
  classical
  apply Finset.sum_nonneg
  intro σ _
  split_ifs
  · exact (weight_pos G h σ).le
  · exact le_rfl

lemma constrainedSum_pos {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (P : Spins n → Prop) (σ : Spins n) (hσ : P σ) :
    0 < constrainedSum G h P := by
  classical
  apply lt_of_lt_of_le (weight_pos G h σ)
  unfold constrainedSum
  exact Finset.single_le_sum (fun τ _ => by
    split_ifs
    · exact (weight_pos G h τ).le
    · exact le_rfl) (Finset.mem_univ σ) |>.trans' (by simp [hσ])

lemma jointWeight_pos {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (τ a b : Spins n) : 0 < jointWeight G h I J F τ a b := by
  classical
  apply constrainedSum_pos G h _ (fun v => if v ∈ I then a v else if v ∈ J then b v else τ v)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    simp [hv]
  · intro v hv
    have hi : v ∉ I := fun hvi => (Finset.disjoint_left.mp hIJ) hvi hv
    simp [hi, hv]
  · intro v hv
    have hi : v ∉ I := fun hvi => (Finset.disjoint_left.mp hIF) hvi hv
    have hj : v ∉ J := fun hvj => (Finset.disjoint_left.mp hJF) hvj hv
    simp [hi, hj]

lemma spin_modular (a b : Bool) :
    spin a + spin b = spin (a ⊓ b) + spin (a ⊔ b) := by
  cases a <;> cases b <;> norm_num [spin]

lemma spin_product_supermodular (a b c d : Bool) :
    spin a * spin b + spin c * spin d ≤
      spin (a ⊓ c) * spin (b ⊓ d) + spin (a ⊔ c) * spin (b ⊔ d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [spin]

lemma energy_supermodular {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (σ ρ : Spins n) :
    energy G h σ + energy G h ρ ≤ energy G h (σ ⊓ ρ) + energy G h (σ ⊔ ρ) := by
  have he : (∑ e, (G.coupling e * spin (σ (G.left e)) * spin (σ (G.right e)) +
      G.coupling e * spin (ρ (G.left e)) * spin (ρ (G.right e)))) ≤
      ∑ e, (G.coupling e * spin ((σ ⊓ ρ) (G.left e)) * spin ((σ ⊓ ρ) (G.right e)) +
      G.coupling e * spin ((σ ⊔ ρ) (G.left e)) * spin ((σ ⊔ ρ) (G.right e))) := by
    apply Finset.sum_le_sum
    intro e _
    have H := mul_le_mul_of_nonneg_left
      (spin_product_supermodular (σ (G.left e)) (σ (G.right e))
        (ρ (G.left e)) (ρ (G.right e))) (G.coupling_nonneg e)
    simpa only [Pi.inf_apply, Pi.sup_apply, mul_add, mul_assoc] using H
  have hv : (∑ v, (h v * spin (σ v) + h v * spin (ρ v))) =
      ∑ v, (h v * spin ((σ ⊓ ρ) v) + h v * spin ((σ ⊔ ρ) v)) := by
    apply Finset.sum_congr rfl
    intro v _
    simpa only [Pi.inf_apply, Pi.sup_apply, mul_add] using
      congrArg (fun x => h v * x) (spin_modular (σ v) (ρ v))
  dsimp [energy]
  simp only [Finset.sum_add_distrib] at he hv
  dsimp at he hv
  linarith

lemma weight_logSupermodular {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (σ ρ : Spins n) :
    weight G h σ * weight G h ρ ≤ weight G h (σ ⊓ ρ) * weight G h (σ ⊔ ρ) := by
  unfold weight
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (energy_supermodular G h σ ρ)

lemma agreesOn_inf {n : ℕ} {S : Finset (Fin n)} {σ ρ a b : Spins n}
    (ha : AgreesOn S σ a) (hb : AgreesOn S ρ b) : AgreesOn S (σ ⊓ ρ) (a ⊓ b) := by
  intro v hv
  simp only [Pi.inf_apply, ha v hv, hb v hv]

lemma agreesOn_sup {n : ℕ} {S : Finset (Fin n)} {σ ρ a b : Spins n}
    (ha : AgreesOn S σ a) (hb : AgreesOn S ρ b) : AgreesOn S (σ ⊔ ρ) (a ⊔ b) := by
  intro v hv
  simp only [Pi.sup_apply, ha v hv, hb v hv]

end BufferedIsing

end OAI
