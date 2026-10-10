import OAI.Probability.DilutedSpin.AnchorExtension
import OAI.Probability.DilutedSpin.HistoryGeometry

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

/-- Every nonroot vertex is retained, including unary vertices. -/
def Edge : {n : ℕ} → PrescribedTree n → Type
  | 0, .leaf => Empty
  | _+1, .node _ C => (i : _) × Option (Edge (C i))

instance edgeFintype : {n : ℕ} → (S : PrescribedTree n) → Fintype (Edge S)
  | 0, .leaf => inferInstanceAs (Fintype Empty)
  | _+1, .node _ C => by
    letI : ∀ i, Fintype (Edge (C i)) := fun i => edgeFintype (C i)
    exact inferInstanceAs (Fintype ((i : _) × Option (Edge (C i))))

def edgeDepth : {n : ℕ} → (S : PrescribedTree n) → Edge S → Fin n
  | 0, .leaf, e => nomatch e
  | _+1, .node k C, e => by
    change (i : Fin k) × Option (Edge (C i)) at e
    obtain ⟨i,e⟩ := e
    cases e with
    | none => exact 0
    | some e => exact (edgeDepth (C i) e).succ

variable {Ω : Type}

def vertexValues : {n : ℕ} → (S : PrescribedTree n) → Sample Ω S → Edge S → Ω
  | 0, .leaf, _, e => nomatch e
  | _+1, .node k C, x, e => by
    change (i : Fin k) × Option (Edge (C i)) at e
    obtain ⟨i,e⟩ := e
    cases e with
    | none => exact (x i).1
    | some e => exact vertexValues (C i) (x i).2 e

def ofVertexValues : {n : ℕ} → (S : PrescribedTree n) → (Edge S → Ω) → Sample Ω S
  | 0, .leaf, _ => ()
  | _+1, .node _ C, v => fun i => (v ⟨i,none⟩, ofVertexValues (C i) (fun e => v ⟨i,some e⟩))

@[simp] lemma vertexValues_of {n : ℕ} (S : PrescribedTree n) (v : Edge S → Ω) :
    vertexValues S (ofVertexValues S v) = v := by
  induction S with
  | leaf => funext e; exact Empty.elim e
  | node k C ih =>
    funext ⟨i,e⟩
    cases e with
    | none => rfl
    | some e => exact congrFun (ih i (fun e => v ⟨i,some e⟩)) e

@[simp] lemma of_vertexValues {n : ℕ} (S : PrescribedTree n) (x : Sample Ω S) :
    ofVertexValues S (vertexValues S x) = x := by
  induction S with
  | leaf => change () = x; exact Subsingleton.elim _ _
  | node k C ih =>
    funext i
    change ((x i).1, ofVertexValues (C i) (vertexValues (C i) (x i).2)) = x i
    rw [ih]

def vertexEquiv {n : ℕ} (S : PrescribedTree n) : Sample Ω S ≃ (Edge S → Ω) where
  toFun := vertexValues S
  invFun := ofVertexValues S
  left_inv := of_vertexValues S
  right_inv := vertexValues_of S

variable [Fintype Ω]
noncomputable local instance treeMarkLawEdgeDecidableEq {n : ℕ}
    (S : PrescribedTree n) : DecidableEq (Edge S) := Classical.decEq _

/-- Under the genuine independent mark prior, vertex marks have the product
law at their actual depths. This is a law statement, not a coupling assumption. -/
lemma sampleLaw_markPrior_weight {n : ℕ} (S : PrescribedTree n)
    (Q : Fin n → FiniteLaw Ω) (x : Sample Ω S) :
    (S.sampleLaw (markPrior n Q)).weight x =
      ∏ e : Edge S, (Q (edgeDepth S e)).weight (vertexValues S x e) := by
  classical
  induction S with
  | leaf =>
    change 1 = ∏ e : Empty, (Q (edgeDepth .leaf e)).weight (vertexValues .leaf x e)
    simp
  | @node n k C ih =>
    change (∏ i, (Q 0).weight (x i).1 *
      ((C i).sampleLaw (markPrior n (fun j => Q j.succ))).weight (x i).2) = _
    change _ = ∏ e : ((i : Fin k) × Option (Edge (C i))),
      (Q (edgeDepth (.node k C) e)).weight (vertexValues (.node k C) x e)
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    rw [Fintype.prod_option,ih]
    rfl

lemma expect_markPrior {n : ℕ} (S : PrescribedTree n)
    (Q : Fin n → FiniteLaw Ω) (f : Sample Ω S → ℝ) :
    (S.sampleLaw (markPrior n Q)).expect f =
      (FiniteLaw.pi (fun e : Edge S => Q (edgeDepth S e))).expect
        (fun v => f (ofVertexValues S v)) := by
  classical
  unfold FiniteLaw.expect
  exact Fintype.sum_equiv (vertexEquiv S) _ _ (fun x => by
    simp only [vertexEquiv,Equiv.coe_fn_mk,of_vertexValues,FiniteLaw.pi,sampleLaw_markPrior_weight])

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance treeMarkLawPropDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω : Type} [Fintype Ω]

@[simp] theorem freshEval_const {n : ℕ} (S : PrescribedTree n)
    (K : KernelTower Ω n) (v : Internal S) (c : ℝ) (x : Sample Ω S) :
    freshEval S K v (fun _ => c) x = c := by
  induction S with
  | leaf => nomatch v
  | @node n k C ih =>
    cases v with
    | none => exact FiniteLaw.expect_const _ _
    | some v => exact ih v.1 (K.2 (x v.1).1) v.2 (x v.1).2

/-- Deleting a newly sampled branch preserves the joint law of ALL old paths.
The old test may be arbitrarily correlated with any retained old prefixes. -/
theorem grow_projectivity {n : ℕ} (S : PrescribedTree n) (K : KernelTower Ω n)
    (v : Internal S) (H : Sample Ω S → ℝ) :
    (sampleLaw (grow S v) K).expect (fun x => H (oldSample S v x)) =
      (sampleLaw S K).expect H := by
  simpa only [mul_one,freshEval_const] using
    extension_sampling S K v H (fun _ => (1:ℝ))


end DilutedSpinGlass.PrescribedTree
end

end

end OAI
