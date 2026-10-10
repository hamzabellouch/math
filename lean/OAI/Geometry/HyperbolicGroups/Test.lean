import Mathlib
import OAI.Geometry.HyperbolicGroups.StarRate
import OAI.Geometry.HyperbolicGroups.CouplingError

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate

/-- A literal conditional test of Section 4, with k+1 branches. -/
structure ConditionalTest where
  fields : Finset Field
  leaf : Field
  newLeaf : leaf ∉ fields
  admissible : Admissible (insert leaf fields)
  k : ℕ

namespace ConditionalTest

def closure (t : ConditionalTest) : Finset Field :=
  (exists_critical_closure t.fields t.leaf t.newLeaf t.admissible).choose

lemma closure_spec (t : ConditionalTest) : t.fields ⊆ t.closure ∧
    criticalExponent t.closure = t.fields.card ∧ t.leaf ∉ t.closure ∧
    ∀ W, W.Nonempty → Disjoint W t.closure →
      1 ≤ criticalExponent (t.closure ∪ W) - criticalExponent t.closure :=
  (exists_critical_closure t.fields t.leaf t.newLeaf t.admissible).choose_spec

lemma closure_gap (t : ConditionalTest) (W : Finset Field) (hW : W.Nonempty) (hd : Disjoint t.closure W) :
    1 ≤ pattern.exponent (t.closure ∪ W) - pattern.exponent t.closure := by
  simp only [pattern_exponent]
  exact t.closure_spec.2.2.2 W hW hd.symm

def threshold (t : ConditionalTest) : ℕ :=
  max (4 * Fintype.card (StarModel.Var (B := Fin (t.k+1)) t.closure)) (t.k+1)

def rate (t : ConditionalTest) (N : ℕ) : ℝ :=
  errorRate (B := Fin (t.k+1)) t.closure t.leaf N

lemma rate_tendsto (t : ConditionalTest) : Tendsto t.rate atTop (𝓝 0) :=
  errorRate_tendsto t.closure t.leaf

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def embedding (t : ConditionalTest) (hN : t.threshold ≤ Fintype.card A) : Fin (t.k+1) ↪ A :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_fin] using (le_max_right _ _).trans hN :
      Fintype.card (Fin (t.k+1)) ≤ Fintype.card A))

def error (t : ConditionalTest) (α β δ : ℝ) (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ)
    (hN : t.threshold ≤ Fintype.card A) (w : TableModel.Entry (A := A) rowSupport → Bool) : ℝ :=
  StarModel.normalizedError rowSupport t.closure t.leaf (actualProbability α β δ A)
    (actualProbability_mem ha hb hd) (Classical.choice inferInstance) (t.embedding hN) w

lemma error_nonneg (t : ConditionalTest) (α β δ : ℝ) (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ)
    (hN : t.threshold ≤ Fintype.card A) (w : TableModel.Entry (A := A) rowSupport → Bool) :
    0 ≤ t.error α β δ ha hb hd hN w := StarModel.normalizedError_nonneg _ _ _ _ _ _ _ _

lemma expectedError (t : ConditionalTest) {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ)
    (hsmall : (t.k+1:ℝ)*(β+90*δ) ≤ 1/2) (hN : t.threshold ≤ Fintype.card A) :
    (TableModel.law rowSupport (actualProbability α β δ A) (actualProbability_mem ha hb hd)).expect
      (t.error α β δ ha hb hd hN) ≤ t.rate (Fintype.card A) := by
  apply expectedError_le ha hb hd (by simpa using hsmall)
    t.closure t.leaf t.closure_spec.2.2.1 t.closure_gap
  exact (le_max_left _ _).trans hN

/-- The coupling is on actual master matches. Its branches agree on exactly the
prescribed named fields, with no assumptions about numerical cross-field values. -/
def Satisfies (t : ConditionalTest) (w : TableModel.Entry (A := A) rowSupport → Bool) (η : ℝ) : Prop :=
  ∃ h : Nonempty (StarModel.Matches rowSupport w), letI := h
    ∃ κ : FiniteLaw (ConditionalStar (fun a : StarModel.Matches rowSupport w => a.val) t.fields t.k),
      (∀ j, (κ.map (ConditionalStar.branch j)).totalVariation FiniteLaw.uniform ≤ η) ∧
      (κ.map (fun z j => (ConditionalStar.branch j z).val t.leaf)).totalVariation
        (FiniteLaw.uniform : FiniteLaw (Fin (t.k+1) → A)) ≤ η

lemma satisfies_of_error (t : ConditionalTest) {α β δ ε : ℝ} (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ)
    (hN : t.threshold ≤ Fintype.card A) (w : TableModel.Entry (A := A) rowSupport → Bool)
    (hε : ε < 1) (hw : t.error α β δ ha hb hd hN w ≤ ε) :
    t.Satisfies w (ε/(1-ε) +
      (1-((Fintype.card A).descFactorial (t.k+1):ℝ)/(Fintype.card A:ℝ)^(t.k+1))) := by
  let a₀ : A := Classical.choice inferInstance
  let b₀ : Fin (t.k+1) ↪ A := t.embedding hN
  let : Nonempty (Fin (t.k+1) ↪ A) := ⟨b₀⟩
  have hM := StarModel.starMean_pos rowSupport t.closure (0 : Fin (t.k+1))
    (actualProbability α β δ A) (actualProbability_mem ha hb hd)
    (actualProbability_pos α β δ) (fun _ => a₀) ((le_max_left _ _).trans hN)
  have hz := StarModel.starCount_pos_of_error rowSupport t.closure t.leaf t.closure_spec.2.2.1
    (actualProbability α β δ A) (actualProbability_mem ha hb hd) a₀ b₀ w hε hM hw
  let : Nonempty (StarModel.Stars (B := Fin (t.k+1)) rowSupport t.closure w) := Fintype.card_pos_iff.mp hz
  let : Nonempty (StarModel.Matches rowSupport w) :=
    ⟨StarModel.starBranch rowSupport t.closure w (0 : Fin (t.k+1)) (Classical.choice inferInstance)⟩
  have hh := StarModel.coupling_of_error rowSupport t.closure t.fields t.closure_spec.1
    t.leaf t.closure_spec.2.2.1 (actualProbability α β δ A) (actualProbability_mem ha hb hd)
    a₀ b₀ w hε hM hw
  refine ⟨inferInstance,StarModel.coupling (k := t.k) rowSupport t.closure t.fields t.closure_spec.1 w,?_,?_⟩
  · intro j
    apply (hh.1 j).trans
    have he := (FiniteLaw.distinct_tv (α := Fin (t.k+1)) (β := A))
    have hp := FiniteLaw.totalVariation_nonneg
      (((FiniteLaw.uniform : FiniteLaw (Fin (t.k+1) ↪ A)).map (fun b => (b : Fin (t.k+1) → A))))
      FiniteLaw.uniform
    rw [he] at hp
    simp only [Fintype.card_fin] at hp
    linarith
  · exact hh.2

end ConditionalTest
end IncidenceTemplate
end HyperbolicObstruction
end
end

section

end
end

end OAI
