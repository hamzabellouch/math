import OAI.Analysis.CircleDomains.Topology.PathEndpoints

namespace OAI

/-! Countably many closed collar gates give Borel restrictions on path codes. -/

open Set Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def separatedGateViolation (C K : Set X) (r : ℝ) : Set C(PathTime, X) :=
  {γ | ∃ t : PathTime, γ t ∈ C ∧ ∀ p ∈ K, r ≤ dist (γ t) p}

theorem isClosed_separatedGateViolation {C : Set X} (hC : IsClosed C)
    (K : Set X) (r : ℝ) : IsClosed (separatedGateViolation C K r) := by
  let S : Set (C(PathTime, X) × PathTime) :=
    {q | q.1 q.2 ∈ C ∧ ∀ p ∈ K, r ≤ dist (q.1 q.2) p}
  have hS : IsClosed S := by
    refine (hC.preimage continuous_eval).inter ?_
    change IsClosed {q : C(PathTime, X) × PathTime |
      ∀ p ∈ K, r ≤ dist (q.1 q.2) p}
    simp only [ofPred_forall]
    exact isClosed_iInter fun p => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_eval.dist continuous_const)
  have heq : Prod.fst '' S = separatedGateViolation C K r := by
    ext γ
    constructor
    · rintro ⟨⟨γ, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(γ, t), ht, rfl⟩
  rw [← heq]
  exact isClosedMap_fst_of_compactSpace S hS

def GateRule (C K : Set X) (γ : C(PathTime, X)) : Prop :=
  ∀ t : PathTime, γ t ∈ C → γ t ∈ K

theorem gateRule_iff {C K : Set X} (hK : IsClosed K) (γ : C(PathTime, X)) :
    GateRule C K γ ↔ ∀ n : ℕ, γ ∉ separatedGateViolation C K (1 / ((n : ℝ) + 1)) := by
  constructor
  · intro h n ⟨t, ht, hsep⟩
    have hz := hsep (γ t) (h t ht)
    rw [dist_self] at hz
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro h t ht
    by_contra hn
    obtain ⟨ε, hε, hball⟩ := isOpen_iff.mp hK.isOpen_compl (γ t) hn
    obtain ⟨n, hne⟩ := exists_nat_one_div_lt hε
    apply h n
    refine ⟨t, ht, fun p hp => hne.le.trans ?_⟩
    by_contra hdist
    have hd : dist p (γ t) < ε := by simpa only [dist_comm] using not_le.mp hdist
    exact hball hd hp

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_gateRule {C K : Set X} (hC : IsClosed C) (hK : IsClosed K) :
    MeasurableSet {γ | GateRule C K γ} := by
  simp only [gateRule_iff hK, ofPred_forall]
  exact MeasurableSet.iInter fun n =>
    (isClosed_separatedGateViolation hC K (1 / ((n : ℝ) + 1))).measurableSet.compl

def GateRules (C K : ℕ → Set X) (γ : C(PathTime, X)) : Prop :=
  ∀ n, GateRule (C n) (K n) γ

theorem measurableSet_gateRules {C K : ℕ → Set X}
    (hC : ∀ n, IsClosed (C n)) (hK : ∀ n, IsClosed (K n)) :
    MeasurableSet {γ | GateRules C K γ} := by
  simp only [GateRules, ofPred_forall]
  exact MeasurableSet.iInter fun n => measurableSet_gateRule (hC n) (hK n)

end CircleDomainRigidity

end

end OAI
