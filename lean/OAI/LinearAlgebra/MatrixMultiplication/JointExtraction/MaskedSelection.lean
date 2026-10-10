import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CoarseHashing
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.AssignmentLoss
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.ExtractionRates

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointMaskedSelection

open JointCoarseHashing JointExtractionRates

attribute [local instance] Classical.propDecidable

variable {P E O V : Type*}

structure OrbitData (P E O V : Type*) where
  ambient : Finset (Triple P)
  support : P → ℕ
  coarse : E → Triple P
  support_ambient : ∀ f ∈ ambient, HasSupportSum support f
  target_mem : ∀ e, coarse e ∈ ambient
  orbits : E → Finset O
  full : E → O → Finset V
  passing : E → O → Finset V
  full_pos : ∀ e, ∀ o ∈ orbits e, 0 < (full e o).card
  passing_subset : ∀ e, ∀ o ∈ orbits e, passing e o ⊆ full e o
  competitors : E → O → V → Finset (Triple P)
  competitor_mem : ∀ e, ∀ o ∈ orbits e, ∀ v ∈ passing e o,
    ∀ f ∈ competitors e o v, f ∈ ambient
  competitor_ne : ∀ e, ∀ o ∈ orbits e, ∀ v ∈ passing e o,
    ∀ f ∈ competitors e o v, f ≠ coarse e
  competitor_shares : ∀ e, ∀ o ∈ orbits e, ∀ v ∈ passing e o,
    ∀ f ∈ competitors e o v, SharesSide (coarse e) f

namespace OrbitData

def eligibilityCompetitors (d : OrbitData P E O V) (e : E) : Finset (Triple P) :=
  d.ambient.filter (fun f => f ≠ d.coarse e ∧ f.1 = (d.coarse e).1)

@[simp] theorem mem_eligibilityCompetitors (d : OrbitData P E O V) (e : E) (f : Triple P) :
    f ∈ d.eligibilityCompetitors e ↔
      f ∈ d.ambient ∧ f ≠ d.coarse e ∧ f.1 = (d.coarse e).1 := by
  simp only [eligibilityCompetitors, Finset.mem_filter]

section Finite

variable [Fintype P]

def variableBad (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (e : E) (o : O) (v : V) (s : Sample P k) : Prop :=
  ∃ f ∈ d.competitors e o v, Survives k U f s

def eligibilityGood (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (e : E) (s : Sample P k) : Prop :=
  ¬ ∃ f ∈ d.eligibilityCompetitors e, Survives k U f s

def Failure (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (N : ℝ) (e : E) (s : Sample P k) : Prop :=
  JointLossCounts.targetBad (d.orbits e) (d.full e) (d.passing e)
    (d.variableBad k U e) (d.eligibilityGood k U e) N s

def Good (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (N : ℝ) (e : E) (s : Sample P k) : Prop :=
  Survives k U (d.coarse e) s ∧ ¬ d.Failure k U N e s

def goodEvent (d : OrbitData P E O V) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (N : ℝ) (e : E) : Finset (Sample P k) :=
  (ownEvent k U (d.coarse e)).filter (fun s => ¬ d.Failure k U N e s)

@[simp] theorem mem_goodEvent (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (e : E) (s : Sample P k) :
    s ∈ d.goodEvent k U N e ↔ d.Good k U N e s := by
  simp only [goodEvent, ownEvent, Finset.mem_filter, Finset.mem_univ, true_and, Good]

theorem variableBad_card_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (e : E) (o : O) (ho : o ∈ d.orbits e)
    (v : V) (hv : v ∈ d.passing e o) (D : ℕ)
    (hdegree : (d.competitors e o v).card ≤ D) :
    (((ownEvent k U (d.coarse e)).filter (d.variableBad k U e o v)).card : ℝ) ≤
      ((D : ℝ) / ((37 ^ k : ℕ) : ℝ)) * ((ownEvent k U (d.coarse e)).card : ℝ) := by
  have h := competitor_union_card_le k U d.support (d.coarse e)
    (d.support_ambient _ (d.target_mem e)) (d.competitors e o v)
    (fun f hf => d.support_ambient f (d.competitor_mem e o ho v hv f hf))
    (d.competitor_ne e o ho v hv) (d.competitor_shares e o ho v hv)
  have hdegreeR : ((d.competitors e o v).card : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast hdegree
  have hfilter : (ownEvent k U (d.coarse e)).filter (d.variableBad k U e o v) =
      (ownEvent k U (d.coarse e)).filter
        (fun s => ∃ f ∈ d.competitors e o v, Survives k U f s) := by
    ext s
    simp only [Finset.mem_filter, variableBad]
  rw [hfilter]
  exact h.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hdegreeR (Nat.cast_nonneg _))
    (Nat.cast_nonneg _))

theorem eligibilityFailure_card_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (e : E) :
    (((ownEvent k U (d.coarse e)).filter (fun s => ¬ d.eligibilityGood k U e s)).card : ℝ) ≤
      (((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ)) *
        ((ownEvent k U (d.coarse e)).card : ℝ) := by
  have h := competitor_union_card_le k U d.support (d.coarse e)
    (d.support_ambient _ (d.target_mem e)) (d.eligibilityCompetitors e)
    (fun f hf => d.support_ambient f ((d.mem_eligibilityCompetitors e f).1 hf).1)
    (fun f hf => ((d.mem_eligibilityCompetitors e f).1 hf).2.1)
    (fun f hf => Or.inl ((d.mem_eligibilityCompetitors e f).1 hf).2.2)
  simpa only [eligibilityGood, not_not] using h

theorem failure_card_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (hN : 0 < N) (e : E) (D : ℕ)
    (hdegree : ∀ o ∈ d.orbits e, ∀ v ∈ d.passing e o, (d.competitors e o v).card ≤ D) :
    (((ownEvent k U (d.coarse e)).filter (d.Failure k U N e)).card : ℝ) ≤
      (((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) +
        ((d.orbits e).card : ℝ) * N * ((D : ℝ) / ((37 ^ k : ℕ) : ℝ))) *
          ((ownEvent k U (d.coarse e)).card : ℝ) := by
  exact JointLossCounts.targetBad_card_le (ownEvent k U (d.coarse e))
    (d.orbits e) (d.full e) (d.passing e) (d.variableBad k U e)
    (d.eligibilityGood k U e) ((D : ℝ) / ((37 ^ k : ℕ) : ℝ))
    (((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ)) N
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hN (d.full_pos e)
    (d.passing_subset e)
    (fun o ho v hv => d.variableBad_card_le k U e o ho v hv D (hdegree o ho v hv))
    (d.eligibilityFailure_card_le k U e)

theorem ownEvent_card_real (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (e : E) :
    ((ownEvent k U (d.coarse e)).card : ℝ) =
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2) * (Fintype.card (Sample P k) : ℝ) := by
  have hsample : (Fintype.card (Sample P k) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hf : ((ownEvent k U (d.coarse e)).card : ℝ) / (Fintype.card (Sample P k) : ℝ) =
      (U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 := by
    change
      ((Finset.univ.filter (fun s =>
        JointHashing.Survives (U : Set (ZMod (37 ^ k)))
          (castWord k (d.coarse e).1) (castWord k (d.coarse e).2.1) s)).card : ℝ) /
        (Fintype.card (JointHashing.Sample P (ZMod (37 ^ k))) : ℝ) = _
    simpa only [Fintype.card_subtype, ZMod.card] using
      JointHashing.survival_fraction U (castWord k (d.coarse e).1) (castWord k (d.coarse e).2.1)
  exact (div_eq_iff hsample).mp hf

theorem goodEvent_card_lower (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (hN : 0 < N) (e : E) (D : ℕ)
    (hdegree : ∀ o ∈ d.orbits e, ∀ v ∈ d.passing e o, (d.competitors e o v).card ≤ D)
    (hsmall : ((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) +
      ((d.orbits e).card : ℝ) * N * ((D : ℝ) / ((37 ^ k : ℕ) : ℝ)) ≤ 1 / 2) :
    ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2) *
      (Fintype.card (Sample P k) : ℝ) ≤ (d.goodEvent k U N e).card := by
  have hb : (((ownEvent k U (d.coarse e)).filter (d.Failure k U N e)).card : ℝ) ≤
      (1 / 2) * ((ownEvent k U (d.coarse e)).card : ℝ) :=
    (d.failure_card_le k U N hN e D hdegree).trans
      (mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _))
  have hg := JointLossCounts.good_card_lower (ownEvent k U (d.coarse e))
    (d.Failure k U N e) (1 / 2) hb
  rw [d.ownEvent_card_real] at hg
  change _ ≤ ((d.goodEvent k U N e).card : ℝ) at hg
  convert hg using 1
  ring

theorem goodIncidence_eq (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (e : E) :
    goodIncidence (fun s e => d.Good k U N e s) e = (d.goodEvent k U N e).card := by
  unfold goodIncidence
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_goodEvent]

theorem good_eligibility (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (e : E) (s : Sample P k)
    (hg : d.Good k U N e s) : d.eligibilityGood k U e s := by
  by_contra h
  exact hg.2 (Or.inl h)

theorem good_no_shared_x (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (N : ℝ) (e f : E) (s : Sample P k)
    (he : d.Good k U N e s) (hf : d.Good k U N f s)
    (hne : d.coarse f ≠ d.coarse e) : (d.coarse f).1 ≠ (d.coarse e).1 := by
  intro hx
  exact d.good_eligibility k U N e s he
    ⟨d.coarse f, (d.mem_eligibilityCompetitors e _).2 ⟨d.target_mem f, hne, hx⟩, hf.1⟩

theorem good_missingFraction_le (d : OrbitData P E O V) (k : ℕ)
    (U : Finset (ZMod (37 ^ k))) (C₀ N : ℝ) (e : E) (s : Sample P k)
    (hg : d.Good k U N e s)
    (hdet : ∀ o ∈ d.orbits e,
      JointLossCounts.deterministicLossFraction (d.full e o) (d.passing e o) ≤ C₀ / N)
    (o : O) (ho : o ∈ d.orbits e) :
    JointLossCounts.missingFraction (d.full e o) (d.passing e o)
      (d.variableBad k U e o) s ≤ (C₀ + 1) / N :=
  JointLossCounts.good_missingFraction_le (d.orbits e) (d.full e) (d.passing e)
    (d.variableBad k U e) (d.eligibilityGood k U e) C₀ N s hg.2
    (d.passing_subset e) hdet o ho

theorem exists_selection [Fintype E] (d : OrbitData P E O V)
    (hinj : Function.Injective d.coarse) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (C₀ N : ℝ) (hN : 0 < N) (D K : ℕ)
    (hdegree : ∀ e, ∀ o ∈ d.orbits e, ∀ v ∈ d.passing e o,
      (d.competitors e o v).card ≤ D)
    (hsmall : ∀ e, ((d.eligibilityCompetitors e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) +
      ((d.orbits e).card : ℝ) * N * ((D : ℝ) / ((37 ^ k : ℕ) : ℝ)) ≤ 1 / 2)
    (hdet : ∀ e, ∀ o ∈ d.orbits e,
      JointLossCounts.deterministicLossFraction (d.full e o) (d.passing e o) ≤ C₀ / N)
    (hK : (K : ℝ) ≤ (Fintype.card E : ℝ) *
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2)) :
    ∃ (s : Sample P k) (G : Finset E), G.card = K ∧
      (∀ e ∈ G, d.Good k U N e s) ∧
      (∀ e ∈ G, ∀ f ∈ G, e ≠ f → (d.coarse e).1 ≠ (d.coarse f).1) ∧
      ∀ e ∈ G, ∀ o ∈ d.orbits e,
        JointLossCounts.missingFraction (d.full e o) (d.passing e o)
          (d.variableBad k U e o) s ≤ (C₀ + 1) / N := by
  classical
  have hi (e : E) :
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2) *
        (Fintype.card (Sample P k) : ℝ) ≤
      (goodIncidence (fun s e => d.Good k U N e s) e : ℝ) := by
    rw [d.goodIncidence_eq]
    exact d.goodEvent_card_lower k U N hN e D (hdegree e) (hsmall e)
  obtain ⟨s, hs⟩ := exists_goodCount_ge (fun s e => d.Good k U N e s) _ hi
  have hk : K ≤ goodCount (fun s e => d.Good k U N e s) s := by exact_mod_cast hK.trans hs
  obtain ⟨G, hcard, hgood⟩ := exists_good_subfamily (fun s e => d.Good k U N e s) s K hk
  refine ⟨s, G, hcard, hgood, ?_, ?_⟩
  · intro e he f hf hne
    exact d.good_no_shared_x k U N f e s (hgood f hf) (hgood e he)
      (fun h => hne (hinj h))
  · intro e he o ho
    exact d.good_missingFraction_le k U C₀ N e s (hgood e he) (hdet e) o ho

end Finite

end OrbitData

end MatrixMultiplication.JointMaskedSelection

end

end OAI
