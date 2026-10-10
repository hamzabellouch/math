import OAI.Combinatorics.BalancedRyser.Probability.FiniteUniformConditioning
import OAI.Combinatorics.BalancedRyser.Probability.UniformRestriction

namespace OAI

namespace Balanced.ConditionalRestriction
open TupleAlignment

noncomputable section
attribute [local instance] Classical.propDecidable

variable {D ι A : Type*}

abbrev FixedArray (P : D → Prop) (a : D → A) :=
  {o : D → A // ∀ d, P d → o d = a d}

instance (P : D → Prop) (a : D → A) : Nonempty (FixedArray P a) :=
  ⟨⟨a, by intro d hd; rfl⟩⟩

def fixedFreshEquiv (P : D → Prop) (a : D → A) :
    FixedArray P a ≃ ({d : D // ¬ P d} → A) where
  toFun o d := o.1 d.1
  invFun f := ⟨fun d => if hd : P d then a d else f ⟨d,hd⟩, by
    intro d hd
    simp only [dite_eq_left hd]⟩
  left_inv o := by
    apply Subtype.ext
    funext d
    by_cases hd : P d
    · simp only [dite_eq_left hd]
      exact (o.2 d hd).symm
    · simp only [dite_eq_right hd]
  right_inv f := by
    funext d
    simp only [dite_eq_right d.2]

def fixedRestrict (e : ι ↪ D) (P : D → Prop) (a : D → A)
    (o : FixedArray P a) : FixedArray (fun i => P (e i)) (fun i => a (e i)) :=
  ⟨fun i => o.1 (e i), fun i hi => o.2 (e i) hi⟩

def freshEmbedding (e : ι ↪ D) (P : D → Prop) :
    {i : ι // ¬ P (e i)} ↪ {d : D // ¬ P d} where
  toFun i := ⟨e i.1, i.2⟩
  inj' := by
    intro i j h
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val h)

theorem fixedRestriction_commutes (e : ι ↪ D) (P : D → Prop) (a : D → A) :
    fixedRestrict e P a ∘ (fixedFreshEquiv P a).symm =
      (fixedFreshEquiv (fun i => P (e i)) (fun i => a (e i))).symm ∘
        (fun f i => f (freshEmbedding e P i)) := by
  funext f
  apply Subtype.ext
  funext i
  rfl

variable [Fintype D] [Fintype ι] [Fintype A]
  [DecidableEq D] [DecidableEq ι] [Nonempty A]

theorem uniform_fixed_restrict (e : ι ↪ D) (P : D → Prop) (a : D → A) :
    (PMF.uniformOfFintype (FixedArray P a)).map (fixedRestrict e P a) =
      PMF.uniformOfFintype (FixedArray (fun i => P (e i)) (fun i => a (e i))) := by
  have hsource := uniform_map_equiv (fixedFreshEquiv P a).symm
  have htarget := uniform_map_equiv (fixedFreshEquiv (fun i => P (e i)) (fun i => a (e i))).symm
  have hrestrict := uniform_map_restrict (A := A) (freshEmbedding e P)
  rw [← hsource, PMF.map_comp, fixedRestriction_commutes,
    ← PMF.map_comp, hrestrict, htarget]

theorem fixed_supported (P : D → Prop) (a : D → A) :
    ∃ o ∈ {o : D → A | ∀ d, P d → o d = a d},
      o ∈ (PMF.uniformOfFintype (D → A)).support :=
  ⟨a, by intro d hd; rfl, PMF.mem_support_uniformOfFintype _⟩

theorem uniform_fixed_filter (P : D → Prop) (a : D → A) :
    (PMF.uniformOfFintype (D → A)).filter
      {o | ∀ d, P d → o d = a d} (fixed_supported P a) =
      (PMF.uniformOfFintype (FixedArray P a)).map Subtype.val := by
  let : Nonempty ({o : D → A | ∀ d, P d → o d = a d} : Set (D → A)) :=
    ⟨⟨a, by intro d hd; rfl⟩⟩
  exact Balanced.uniform_filter_eq_subtype_map _ _

theorem uniform_conditional_restrict (e : ι ↪ D) (P : D → Prop) (a : D → A) :
    ((PMF.uniformOfFintype (D → A)).filter
      {o | ∀ d, P d → o d = a d} (fixed_supported P a)).map
      (fun o i => o (e i)) =
    (PMF.uniformOfFintype (ι → A)).filter
      {o | ∀ i, P (e i) → o i = a (e i)}
      (fixed_supported (fun i => P (e i)) (fun i => a (e i))) := by
  rw [uniform_fixed_filter, uniform_fixed_filter, PMF.map_comp]
  change (PMF.uniformOfFintype (FixedArray P a)).map
    (Subtype.val ∘ fixedRestrict e P a) = _
  rw [← PMF.map_comp, uniform_fixed_restrict]

end
end Balanced.ConditionalRestriction

end OAI
