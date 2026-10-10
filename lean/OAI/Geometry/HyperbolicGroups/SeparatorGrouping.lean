import Mathlib
import OAI.Geometry.HyperbolicGroups.SeparatorDecomposition
import OAI.Geometry.HyperbolicGroups.BalancedGrouping

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Convert the connected-remainder formulation into the literal three
regions required by the recursive partition theorem. -/
theorem label_of_component_separator (G : SimpleGraph V) (U S : Finset V)
    (hSU : S ⊆ U)
    (hsep : ∀ W : Finset V, W ⊆ U → Disjoint W S →
      (G.induce (W : Set V)).Preconnected → 2*W.card ≤ U.card) :
    ∃ t : V → Fin 3, region U t 0 = S ∧
      3*(region U t 1).card ≤ 2*U.card ∧
      3*(region U t 2).card ≤ 2*U.card ∧
      ∀ x ∈ region U t 1, ∀ y ∈ region U t 2, ¬G.Adj x y := by
  classical
  let R := U \ S
  let H := G.induce (R : Set V)
  let : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let color : V → Option H.ConnectedComponent := fun v =>
    if hv : v ∈ R then some (H.connectedComponentMk ⟨v,hv⟩) else none
  have hcolor (v : V) (hv : v ∈ R) : color v = some (H.connectedComponentMk ⟨v,hv⟩) :=
    dite_eq_left hv
  let fiber := fun i => R.filter (fun v => color v = i)
  have htotal : ∑ i, (fiber i).card ≤ U.card := by
    have he := Finset.sum_card_fiberwise_eq_card_filter R
      (Finset.univ : Finset (Option H.ConnectedComponent)) color
    simp only [Finset.mem_univ,Finset.filter_true] at he
    exact he.le.trans (Finset.card_le_card Finset.sdiff_subset)
  have hblock : ∀ i, 2*(fiber i).card ≤ U.card := by
    intro i
    have hsub : fiber i ⊆ U := (Finset.filter_subset _ _).trans Finset.sdiff_subset
    have hdisj : Disjoint (fiber i) S := by
      apply Finset.disjoint_left.mpr
      intro v hv hvs
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2 hvs
    cases i with
    | none =>
      have he : fiber none = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        have hvR := (Finset.mem_filter.mp hv).1
        have hn := (Finset.mem_filter.mp hv).2
        rw [hcolor v hvR] at hn
        cases hn
      simp [he]
    | some c =>
      apply hsep _ hsub hdisj
      let g : c.toSimpleGraph →g G.induce (fiber (some c) : Set V) := {
        toFun := fun v => ⟨v.val.val,Finset.mem_filter.mpr ⟨v.val.property,by
          rw [hcolor _ v.val.property]
          exact congrArg some v.property⟩⟩
        map_rel' := fun h => h }
      apply c.connected_toSimpleGraph.preconnected.map g
      intro v
      have hvR := (Finset.mem_filter.mp v.property).1
      have hvC := (Finset.mem_filter.mp v.property).2
      rw [hcolor v.val hvR] at hvC
      exact ⟨⟨⟨v.val,hvR⟩,Option.some.inj hvC⟩,Subtype.ext rfl⟩
  obtain ⟨A,hA,hAc⟩ := balanced_grouping (fun i => (fiber i).card) U.card htotal hblock
  let t : V → Fin 3 := fun v => if v ∈ S then 0 else if color v ∈ A then 1 else 2
  have hzero : region U t 0 = S := by
    ext v
    simp only [mem_region,t]
    by_cases hs : v ∈ S
    · simp [hs,hSU hs]
    · by_cases hc : color v ∈ A <;> simp [hs,hc]
  have hone : region U t 1 = R.filter (fun v => color v ∈ A) := by
    ext v
    simp only [mem_region,Finset.mem_filter,Finset.mem_sdiff,t,R]
    by_cases hs : v ∈ S <;> by_cases hc : color v ∈ A <;> simp [hs,hc]
  have htwo : region U t 2 = R.filter (fun v => color v ∈ Aᶜ) := by
    ext v
    simp only [mem_region,Finset.mem_filter,Finset.mem_sdiff,t,R,Finset.mem_compl]
    by_cases hs : v ∈ S <;> by_cases hc : color v ∈ A <;> simp [hs,hc]
  have hcardA := Finset.sum_card_fiberwise_eq_card_filter R A color
  have hcardAc := Finset.sum_card_fiberwise_eq_card_filter R Aᶜ color
  refine ⟨t,hzero,?_,?_,?_⟩
  · rw [hone,← hcardA]
    exact hA
  · rw [htwo,← hcardAc]
    exact hAc
  · intro x hx y hy hadj
    rw [hone] at hx
    rw [htwo] at hy
    obtain ⟨hxR,hxA⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyR,hyA⟩ := Finset.mem_filter.mp hy
    have he : color x = color y := by
      rw [hcolor x hxR,hcolor y hyR]
      exact congrArg some (ConnectedComponent.sound (show H.Reachable ⟨x,hxR⟩ ⟨y,hyR⟩ from
        (show H.Adj ⟨x,hxR⟩ ⟨y,hyR⟩ from hadj).reachable))
    rw [← he] at hyA
    exact Finset.mem_compl.mp hyA hxA

/-- A uniform sqrt component-separator theorem supplies the exact recursive
separator interface, with no factor depending on the carrier or graph. -/
theorem balanced_separators_of_component_separators (G : SimpleGraph V) (c : ℕ)
    (h : ∀ U : Finset V, ∃ S : Finset V, S ⊆ U ∧ S.card ≤ c*Nat.sqrt U.card ∧
      ∀ W : Finset V, W ⊆ U → Disjoint W S →
        (G.induce (W : Set V)).Preconnected → 2*W.card ≤ U.card) :
    HasBalancedSeparators G c := by
  intro U
  obtain ⟨S,hSU,hSc,hsep⟩ := h U
  obtain ⟨t,ht,h1,h2,hno⟩ := label_of_component_separator G U S hSU hsep
  refine ⟨t,?_,h1,h2,hno⟩
  rw [ht]
  have hroot : (Nat.sqrt U.card : ℝ) ≤ Real.sqrt U.card := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    have hh := Nat.sqrt_le U.card
    norm_cast
    simpa only [pow_two] using hh
  have hh : (S.card : ℝ) ≤ (c : ℝ)*(Nat.sqrt U.card : ℝ) := by exact_mod_cast hSc
  exact hh.trans (mul_le_mul_of_nonneg_left hroot (by positivity))

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
