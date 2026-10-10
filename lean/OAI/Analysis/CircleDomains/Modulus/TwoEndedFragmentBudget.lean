import OAI.Analysis.CircleDomains.Selection.TwoEndedFragmentGeometry
import OAI.Analysis.CircleDomains.Modulus.RestrictedFragmentCosts

namespace OAI

/-! A single original path pays simultaneously for its retained middle
and both endpoint fragment families. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem twoEnded_restricted_budget
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) (a b : ℕ → PathTime)
    (ha : Antitone a) (hb : Monotone b) (hab : a 0 < b 0)
    (F : Finset ℕ) (hleft : ∀j ∈ F, a (j+1) < a j) (hright : ∀j ∈ F, b j < b (j+1))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hmiddle : m (γ.val (a 0)) = 0 ∧ m (γ.val (b 0)) = 0)
    (ham : ∀j ∈ F, m (γ.val (a j)) = 0 ∧ m (γ.val (a (j+1))) = 0)
    (hbm : ∀j ∈ F, m (γ.val (b j)) = 0 ∧ m (γ.val (b (j+1))) = 0) :
    physicalTollCost d g m (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ hab) +
      (∑j : F, (physicalTollCost d g m
        (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ (hleft j j.property)) +
        physicalTollCost d g m
        (affineFinitePhysicalPath d.domainEquiv hU d.basePoint γ (hright j j.property)))) ≤
      physicalTollCost d g m γ := by
  classical
  let emb : F ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  let index : Option (F ⊕ F) ↪ CollarFragmentIndex := (emb.sumMap emb).optionMap
  let l : Option (F ⊕ F) → PathTime := fun i => collarFragmentLeft a b (index i)
  let r : Option (F ⊕ F) → PathTime := fun i => collarFragmentRight a b (index i)
  have hlr (i : Option (F ⊕ F)) : l i < r i := by
    cases i with
    | none => exact hab
    | some i =>
      cases i with
      | inl j => exact hleft j j.property
      | inr j => exact hright j j.property
  have hd : Pairwise (Disjoint on fun i => Ioo (l i) (r i)) := by
    intro i j hij
    exact twoEnded_interval_interiors_disjoint a b ha hb hab (fun h => hij (index.injective h))
  have hml (i : Option (F ⊕ F)) : m (γ.val (l i)) = 0 := by
    cases i with
    | none => exact hmiddle.1
    | some i => cases i with
      | inl j => exact (ham j j.property).2
      | inr j => exact (hbm j j.property).1
  have hmr (i : Option (F ⊕ F)) : m (γ.val (r i)) = 0 := by
    cases i with
    | none => exact hmiddle.2
    | some i => cases i with
      | inl j => exact (ham j j.property).1
      | inr j => exact (hbm j j.property).2
  have h := sum_restricted_physicalTollCost_le d hU γ l r hlr hd g hg m hml hmr
  simpa only [tsum_fintype, Fintype.sum_option, Fintype.sum_sum_type,
    l, r, index, emb, Function.Embedding.optionMap, Function.Embedding.sumMap,
    Function.Embedding.coeFn_mk, Option.map_none, Option.map_some, Sum.map_inl, Sum.map_inr,
    collarFragmentLeft, collarFragmentRight,
    ← Finset.sum_add_distrib] using h

end CircleDomainRigidity

end

end OAI
