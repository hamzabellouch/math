import OAI.Analysis.CircleDomains.Modulus.TwoEndedFragmentBudget

namespace OAI

/-! A retained prefix and all final collar fragments share the original
path budget; no initial endpoint toll is discarded. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem oneEnded_restricted_budget
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) (b : ℕ → PathTime)
    (hb : Monotone b) (hprefix : ⊥ < b 0) (F : Finset ℕ)
    (hright : ∀j ∈ F, b j < b (j+1))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hzero : m (γ.val ⊥) = 0) (hb0 : m (γ.val (b 0)) = 0)
    (hbm : ∀j ∈ F, m (γ.val (b j)) = 0 ∧ m (γ.val (b (j+1))) = 0) :
    physicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ hprefix) +
      (∑j : F, physicalTollCost d g m
        (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ (hright j j.property))) ≤
      physicalTollCost d g m γ := by
  classical
  let emb : F ↪ ℕ ⊕ ℕ := ⟨fun j => .inr j, fun _ _ h => Subtype.ext (Sum.inr.inj h)⟩
  let index : Option F ↪ CollarFragmentIndex := emb.optionMap
  let a : ℕ → PathTime := fun _ => ⊥
  let l : Option F → PathTime := fun i => collarFragmentLeft a b (index i)
  let r : Option F → PathTime := fun i => collarFragmentRight a b (index i)
  have hlr (i : Option F) : l i < r i := by
    cases i with
    | none => exact hprefix
    | some j => exact hright j j.property
  have hd : Pairwise (Disjoint on fun i => Ioo (l i) (r i)) := by
    intro i j hij
    exact twoEnded_interval_interiors_disjoint a b antitone_const hb hprefix
      (fun h => hij (index.injective h))
  have hml (i : Option F) : m (γ.val (l i)) = 0 := by
    cases i with
    | none => exact hzero
    | some j => exact (hbm j j.property).1
  have hmr (i : Option F) : m (γ.val (r i)) = 0 := by
    cases i with
    | none => exact hb0
    | some j => exact (hbm j j.property).2
  have h := sum_restricted_physicalTollCost_le d hU γ l r hlr hd g hg m hml hmr
  simpa only [tsum_fintype, Fintype.sum_option, l, r, index, emb, a,
    Function.Embedding.optionMap, Function.Embedding.coeFn_mk, Option.map_none, Option.map_some,
    collarFragmentLeft, collarFragmentRight] using h

end CircleDomainRigidity

end

end OAI
