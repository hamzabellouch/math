import OAI.Analysis.CircleDomains.Topology.PathTags

namespace OAI

/-! Borel endpoint and first-arrival restrictions for the base path codes. -/

open Set Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

def earlyHitSet (b : X) (n : ℕ) : Set C(PathTime, X) :=
  {γ | ∃ t : PathTime, (t : ℝ) ≤ 1 - 1 / ((n : ℝ) + 1) ∧ γ t = b}

theorem isClosed_earlyHitSet (b : X) (n : ℕ) : IsClosed (earlyHitSet b n) := by
  let H : Set (C(PathTime, X) × PathTime) :=
    {q | (q.2 : ℝ) ≤ 1 - 1 / ((n : ℝ) + 1) ∧ q.1 q.2 = b}
  have hH : IsClosed H :=
    (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).inter
      (isClosed_eq continuous_eval continuous_const)
  have heq : Prod.fst '' H = earlyHitSet b n := by
    ext γ
    constructor
    · rintro ⟨⟨γ, t⟩, ht, rfl⟩
      exact ⟨t, ht⟩
    · rintro ⟨t, ht⟩
      exact ⟨(γ, t), ht, rfl⟩
  rw [← heq]
  exact isClosedMap_fst_of_compactSpace H hH

def FirstArrival (b : X) (γ : C(PathTime, X)) : Prop :=
  γ ⊤ = b ∧ ∀ t : PathTime, t < ⊤ → γ t ≠ b

theorem firstArrival_iff (b : X) (γ : C(PathTime, X)) :
    FirstArrival b γ ↔ γ ⊤ = b ∧ ∀ n : ℕ, γ ∉ earlyHitSet b n := by
  constructor
  · rintro ⟨he, hfirst⟩
    refine ⟨he, fun n hn => ?_⟩
    obtain ⟨t, ht, htb⟩ := hn
    apply hfirst t _ htb
    change (t : ℝ) < 1
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · rintro ⟨he, hnone⟩
    refine ⟨he, fun t ht htb => ?_⟩
    have ht' : (t : ℝ) < 1 := ht
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr ht')
    exact hnone n ⟨t, by linarith, htb⟩

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurableSet_firstArrival (b : X) : MeasurableSet {γ | FirstArrival b γ} := by
  simp only [firstArrival_iff, ofPred_and, ofPred_forall]
  apply MeasurableSet.inter
  · exact (isClosed_eq (continuous_eval_const ⊤) continuous_const).measurableSet
  · exact MeasurableSet.iInter fun n => (isClosed_earlyHitSet b n).measurableSet.compl

variable [MeasurableSpace X] [BorelSpace X]

theorem measurableSet_endpointCodes {E : Set X} (hE : MeasurableSet E) (b : X) :
    MeasurableSet {Γ : TaggedPath X | Γ.1 ⊥ ∈ E ∧ FirstArrival b Γ.1} := by
  exact (((continuous_eval_const ⊥).measurable hE).preimage measurable_fst).inter
    ((measurableSet_firstArrival b).preimage measurable_fst)

end CircleDomainRigidity

end

end OAI
