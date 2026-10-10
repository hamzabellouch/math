import OAI.Analysis.CircleDomains.Probability.AnalyticFiniteMeasurability
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

namespace OAI

/-! A measurable least-child choice constructs a Baire branch when each
finite-prefix membership set is measurable for the completed measure. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

 theorem exists_nullMeasurable_baire_branch {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (A : List ℕ → Set X)
    (hA : ∀ s, NullMeasurableSet (A s) μ)
    (hroot : A [] = univ) (hchild : ∀ s, A s ⊆ ⋃ k, A (k::s)) :
    ∃ b : X → (ℕ → ℕ), NullMeasurable b μ ∧
      ∀ x n, x ∈ A (PiNat.res (b x) n) := by
  classical
  let : MeasurableSpace (List ℕ) := ⊤
  have hAm (s : List ℕ) : @MeasurableSet (NullMeasurableSpace X μ) _ (A s) := hA s
  let p (s : List ℕ) (x : NullMeasurableSpace X μ) (k : ℕ) : Prop :=
    (x ∈ A s ∧ x ∈ A (k::s)) ∨ (x ∉ A s ∧ k = 0)
  have hp (s : List ℕ) (x : NullMeasurableSpace X μ) : ∃ k, p s x k := by
    by_cases hx : x ∈ A s
    · obtain ⟨k,hk⟩ := mem_iUnion.mp (hchild s hx)
      exact ⟨k,Or.inl ⟨hx,hk⟩⟩
    · exact ⟨0,Or.inr ⟨hx,rfl⟩⟩
  let next (s : List ℕ) (x : NullMeasurableSpace X μ) : ℕ := Nat.find (hp s x)
  have hnext (s : List ℕ) : Measurable (next s) := by
    apply measurable_find (hp s)
    intro k
    by_cases hk : k = 0
    · convert ((hAm s).inter (hAm (k::s))).union (hAm s).compl using 1
      ext x
      simp only [p,hk,and_true,mem_union,mem_ofPred_eq]
      rfl
    · convert (hAm s).inter (hAm (k::s)) using 1
      ext x
      simp only [p,hk,and_false,or_false,mem_ofPred_eq]
      rfl
  have hchosen (s : List ℕ) (x : NullMeasurableSpace X μ) (hx : x ∈ A s) :
      x ∈ A (next s x :: s) := by
    rcases Nat.find_spec (hp s x) with h | h
    · exact h.2
    · exact (h.1 hx).elim
  have hnextJoint : Measurable (fun q : List ℕ × NullMeasurableSpace X μ => next q.1 q.2) :=
    measurable_from_prod_countable_right hnext
  let state : ℕ → NullMeasurableSpace X μ → List ℕ :=
    Nat.rec (fun _ => []) (fun _ q x => next (q x) x :: q x)
  have hstate (n : ℕ) : Measurable (state n) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      exact (measurable_of_countable (fun q : ℕ × List ℕ => q.1::q.2)).comp
        ((hnextJoint.comp (ih.prodMk measurable_id)).prodMk ih)
  have hinside (n : ℕ) (x : NullMeasurableSpace X μ) : x ∈ A (state n x) := by
    induction n with
    | zero => change x ∈ A []; rw [hroot]; trivial
    | succ n ih => exact hchosen (state n x) x ih
  let b (x : NullMeasurableSpace X μ) (n : ℕ) : ℕ := next (state n x) x
  have hb : Measurable b := Measurable.of_eval (fun n =>
    hnextJoint.comp ((hstate n).prodMk measurable_id))
  have hres (x : NullMeasurableSpace X μ) (n : ℕ) : PiNat.res (b x) n = state n x := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change b x n :: PiNat.res (b x) n = b x n :: state n x
      rw [ih]
  refine ⟨b,hb,?_⟩
  intro x n
  exact (congrArg (fun s : List ℕ => x ∈ A s)
    (hres (show NullMeasurableSpace X μ from x) n)).mpr
    (hinside n (show NullMeasurableSpace X μ from x))

end CircleDomainRigidity

end

end OAI
