import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Logic.Equiv.Basic
import Mathlib.SetTheory.Cardinal.Finite
import OAI.Computability.UniqueGames.Inverse.KMSAnalyticHybridCoordinatesRankLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.KMS

noncomputable section
open scoped BigOperators Classical

section FiniteDensity

variable {Ω : Type*} [DecidableEq Ω]

/-- Relative density, with value zero when the conditioning set is empty. -/
def relativeDensity (S I : Finset Ω) : ℝ :=
  ((S ∩ I).card : ℝ) / I.card

/-- Restricting the denominator to a chart containing the set preserves the
numerator. This is the exact finite-set step used after Grassmann expansion. -/
theorem inter_chart_eq (S I C : Finset Ω) (hSC : S ⊆ C) :
    S ∩ (I ∩ C) = S ∩ I := by
  ext x
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hS, hI, _⟩
    exact ⟨hS, hI⟩
  · rintro ⟨hS, hI⟩
    exact ⟨hS, hI, hSC hS⟩

/-- A nonempty part of the set in an interval witnesses that the chart and
interval meet. No positive denominator is silently assumed. -/
theorem chart_inter_nonempty (S I C : Finset Ω) (hSC : S ⊆ C)
    (hSI : (S ∩ I).Nonempty) : (I ∩ C).Nonempty := by
  obtain ⟨x, hx⟩ := hSI
  exact ⟨x, Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hx).2, hSC (Finset.mem_inter.mp hx).1⟩⟩

/-- Intersecting a nonempty conditioning interval with a chart containing the
set can only increase its relative density. -/
theorem relativeDensity_le_chart (S I C : Finset Ω) (hSC : S ⊆ C)
    (hIC : (I ∩ C).Nonempty) :
    relativeDensity S I ≤ relativeDensity S (I ∩ C) := by
  unfold relativeDensity
  rw [inter_chart_eq S I C hSC]
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
  · exact Nat.cast_pos.mpr (Finset.card_pos.mpr hIC)
  · exact Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)

/-- The quantitative density conclusion passes to the matrix chart without
losing any factor. -/
theorem density_bound_passes_to_chart (S I C : Finset Ω) (hSC : S ⊆ C)
    (hSI : (S ∩ I).Nonempty) {α : ℝ} (hα : α ≤ relativeDensity S I) :
    (I ∩ C).Nonempty ∧ α ≤ relativeDensity S (I ∩ C) := by
  have hIC := chart_inter_nonempty S I C hSC hSI
  exact ⟨hIC, hα.trans (relativeDensity_le_chart S I C hSC hIC)⟩

end FiniteDensity

abbrev F2 := ZMod 2
abbrev Ambient (n : ℕ) := Fin n → F2

/-- Actual `ell`-dimensional subspaces of the ambient binary vector space. -/
def Vertex (n ell : ℕ) :=
  {L : Submodule F2 (Ambient n) // Module.finrank F2 L = ell}

instance vertexFinite (n ell : ℕ) : Finite (Vertex n ell) := by
  let : Finite (Submodule F2 (Ambient n)) :=
    Finite.of_injective (fun L : Submodule F2 (Ambient n) => (L : Set (Ambient n)))
      SetLike.coe_injective
  exact inferInstanceAs (Finite {L : Submodule F2 (Ambient n) //
    Module.finrank F2 L = ell})

instance vertexFintype (n ell : ℕ) : Fintype (Vertex n ell) := Fintype.ofFinite _

/-- A neighbor is distinct and meets the vertex in a hyperplane. The explicit
distinctness also makes the definition harmless at dimension zero. -/
def Adjacent {n ell : ℕ} (L M : Vertex n ell) : Prop :=
  L ≠ M ∧ Module.finrank F2 ↥(L.val ⊓ M.val : Submodule F2 (Ambient n)) + 1 = ell

def neighbors {n ell : ℕ} (L : Vertex n ell) : Finset (Vertex n ell) :=
  Finset.univ.filter (Adjacent L)

/-- Uniform start in `S`, followed by a uniform Grassmann neighbor. -/
def retention {n ell : ℕ} (S : Finset (Vertex n ell)) : ℝ :=
  (∑ L ∈ S, relativeDensity S (neighbors L)) / S.card

/-- The actual interval `A ≤ L ≤ B` among the `ell`-dimensional vertices. -/
def interval {n ell : ℕ} (A B : Submodule F2 (Ambient n)) :
    Finset (Vertex n ell) :=
  Finset.univ.filter fun L => A ≤ L.val ∧ L.val ≤ B

/-- The parameter order needed from KMS, including a nonempty dense interval.
The parameters `r` and `alpha` must be fixed before `ell`, and the ambient threshold may then depend
on `ell`. A bound with `alpha = 2^(-ell)` does not meet this interface. -/
def ExpansionPrinciple : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      ∃ r : ℕ, 1 ≤ r ∧ ∃ ell₀ : ℕ, ∀ ell : ℕ, ell₀ ≤ ell →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∀ S : Finset (Vertex n ell), S.Nonempty → ζ ≤ retention S →
            ∃ A B : Submodule F2 (Ambient n),
              A ≤ B ∧ Module.finrank F2 A + (n - Module.finrank F2 B) ≤ r ∧
                (S ∩ interval A B).Nonempty ∧ α ≤ relativeDensity S (interval A B)

end
end UniqueGamesTheorem.Inverse.KMS

end

section

/-!
An independent frame inside `L` can be completed using vectors from `W` whenever
`L` lies in the sum of the frame's span and `W`.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped Classical
open UniqueGamesTheorem.Inverse.KMS

/-- Restricted completion of an independent frame. The original vectors need
not belong to `W`; only the newly chosen vectors are required to do so. -/
theorem exists_restricted_completion {n q t : ℕ}
    (Q : Fin q → Ambient n) (W L : Submodule F2 (Ambient n))
    (hQ : LinearIndependent F2 Q)
    (hQL : Submodule.span F2 (Set.range Q) ≤ L)
    (hLW : L ≤ Submodule.span F2 (Set.range Q) ⊔ W)
    (hL : Module.finrank F2 L = q + t) :
    ∃ z : Fin t → W,
      LinearIndependent F2 (Sum.elim Q (fun i => (z i : Ambient n))) ∧
        Submodule.span F2
          (Set.range (Sum.elim Q (fun i => (z i : Ambient n)))) = L := by
  classical
  let T : Set (Ambient n) := Set.range Q ∪ (W ⊓ L : Submodule F2 (Ambient n))
  have hQT : Set.range Q ⊆ T := Set.subset_union_left
  have hTspan : Submodule.span F2 T = L := by
    change Submodule.span F2
      (Set.range Q ∪ ((W ⊓ L : Submodule F2 (Ambient n)) : Set (Ambient n))) = L
    rw [Submodule.span_union, Submodule.span_eq,
      ← sup_inf_assoc_of_le W hQL, inf_eq_right.mpr hLW]
  obtain ⟨B, hBT, hQB, hTB, hB⟩ :=
    exists_linearIndepOn_id_extension hQ.linearIndepOn_id hQT
  have hBspan : Submodule.span F2 B = L := by
    rw [← hTspan]
    exact le_antisymm (Submodule.span_mono hBT) (Submodule.span_le.mpr hTB)
  let D : Set (Ambient n) := B \ Set.range Q
  let f : Fin q ⊕ D → Ambient n := Sum.elim Q Subtype.val
  have hf_inj : Function.Injective f := by
    apply Sum.elim_injective.mpr
    refine ⟨hQ.injective, Subtype.val_injective, ?_⟩
    intro i d hid
    exact d.property.2 ⟨i, hid⟩
  have hf_range : Set.range f = B := by
    ext x
    constructor
    · rintro ⟨i | d, rfl⟩
      · exact hQB (Set.mem_range_self i)
      · exact d.property.1
    · intro hx
      by_cases hxQ : x ∈ Set.range Q
      · obtain ⟨i, rfl⟩ := hxQ
        exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr ⟨x, hx, hxQ⟩, rfl⟩
  have hf : LinearIndependent F2 f := by
    apply (linearIndepOn_id_range_iff hf_inj).mp
    rw [hf_range]
    exact hB
  have hcard := finrank_span_eq_card hf
  rw [hf_range, hBspan, hL] at hcard
  have hDcard : Fintype.card D = t := by
    apply Nat.add_left_cancel (n := q)
    simpa using hcard.symm
  let e : Fin t ≃ D := (Fintype.equivFinOfCardEq hDcard).symm
  let z : Fin t → W := fun i =>
    ⟨(e i).val, ((hBT (e i).property.1).resolve_left (e i).property.2).1⟩
  let g : (Fin q ⊕ Fin t) ≃ (Fin q ⊕ D) := Equiv.sumCongr (Equiv.refl _) e
  have hz : Sum.elim Q (fun i => (z i : Ambient n)) = f ∘ g := by
    funext i
    cases i <;> rfl
  refine ⟨z, ?_, ?_⟩
  · rw [hz]
    exact hf.comp g g.injective
  · rw [hz, g.surjective.range_comp, hf_range, hBspan]

end
end UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

end

section

/-! Exact finite counting for the restricted-basis lift.  In particular, failed
independent completions contribute zero rather than an additive error. -/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Decompose a finite domain by its exact fibers. -/
theorem nat_card_eq_sum_fibers (f : X → Y) :
    Nat.card X = ∑ y : Y, Nat.card {x : X // f x = y} := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]

/-- The event count is the sum of the same fibers over the event. -/
theorem nat_card_event_eq_sum_fibers (f : X → Y) (p : Y → Prop) :
    Nat.card {x : X // p (f x)} =
      ∑ y : {y : Y // p y}, Nat.card {x : X // f x = y.val} := by
  let e : (Σ y : {y : Y // p y}, {x : X // f x = y.val}) ≃
      {x : X // p (f x)} :=
    { toFun := fun a => ⟨a.2.val, a.2.property.symm ▸ a.1.property⟩
      invFun := fun a => ⟨⟨f a.val, a.property⟩, ⟨a.val, rfl⟩⟩
      left_inv := by rintro ⟨⟨y, hy⟩, ⟨x, hx⟩⟩; cases hx; rfl
      right_inv := by intro a; rfl }
  rw [← Nat.card_congr e, Nat.card_sigma]

/-- Constant fibers give an exact density identity, including an empty target.
The nonzero fiber size is established geometrically for restricted bases. -/
theorem uniformFiber_card_ratio (f : X → Y) (p : Y → Prop)
    (c : ℕ) (hc : 0 < c)
    (hf : ∀ y, Nat.card {x : X // f x = y} = c) :
    (Nat.card {x : X // p (f x)} : ℝ) / Nat.card X =
      (Nat.card {y : Y // p y} : ℝ) / Nat.card Y := by
  have hX : Nat.card X = Nat.card Y * c := by
    rw [nat_card_eq_sum_fibers f]
    simp only [hf]
    simp [Nat.card_eq_fintype_card]
  have hE : Nat.card {x : X // p (f x)} = Nat.card {y : Y // p y} * c := by
    rw [nat_card_event_eq_sum_fibers f p]
    simp only [hf]
    simp [Nat.card_eq_fintype_card]
  rw [hE, hX, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ (ne_of_gt (Nat.cast_pos.mpr hc))

/-- Sampling from a larger finite space and accepting only a subset never
increases the density of an event within that subset. Empty subsets are handled
explicitly, so this statement makes no hidden nonemptiness assumption. -/
theorem subtype_event_ratio_le {Z : Type*} [Fintype Z] (D : Z → Prop)
    (p : {z : Z // D z} → Prop) :
    (Nat.card {z : {z : Z // D z} // p z} : ℝ) / Nat.card Z ≤
      (Nat.card {z : {z : Z // D z} // p z} : ℝ) / Nat.card {z : Z // D z} := by
  by_cases hD : Nat.card {z : Z // D z} = 0
  · have hE : Nat.card {z : {z : Z // D z} // p z} = 0 := by
      apply Nat.eq_zero_of_le_zero
      rw [← hD]
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    rw [hE]
    simp
  · apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
    · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hD)
    · exact Nat.cast_le.mpr
        (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

end
end UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

end

section

/-!
# Restricted densities in the ordered-basis lift

The prefix vectors are arbitrary: they may be dependent, and they need not lie
in the subspace from which the remaining vectors are sampled. The relevant
Grassmann interval has lower endpoint `span Q` and upper endpoint `span Q ⊔ W`.
-/

namespace UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped BigOperators Classical
open KMS

variable {n q t : ℕ}

def prefixSpan (Q : Fin q → Ambient n) : Submodule F2 (Ambient n) :=
  Submodule.span F2 (Set.range Q)

def joinedTuple (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : Fin t → W) : (Fin q ⊕ Fin t) → Ambient n :=
  Sum.elim Q (fun i => (z i : Ambient n))

abbrev IndependentCompletion (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :=
  {z : Fin t → W // LinearIndependent F2 (joinedTuple Q W z)}

def completionVertex (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) : Vertex n (q + t) :=
  ⟨Submodule.span F2 (Set.range (joinedTuple Q W z.val)), by
    simpa using finrank_span_eq_card z.property⟩

theorem prefix_le_completion (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) :
    prefixSpan Q ≤ (completionVertex Q W z).val := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨Sum.inl i, rfl⟩

theorem completion_le_sup (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) :
    (completionVertex Q W z).val ≤ prefixSpan Q ⊔ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl i =>
      exact (le_sup_left : prefixSpan Q ≤ prefixSpan Q ⊔ W)
        (Submodule.subset_span ⟨i, rfl⟩)
  | inr i =>
      exact (le_sup_right : W ≤ prefixSpan Q ⊔ W) (z.val i).property

theorem completion_mem_interval (Q : Fin q → Ambient n)
    (W : Submodule F2 (Ambient n)) (z : IndependentCompletion (t := t) Q W) :
    completionVertex Q W z ∈ interval (prefixSpan Q) (prefixSpan Q ⊔ W) := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    prefix_le_completion Q W z, completion_le_sup Q W z⟩

theorem prefix_independent (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) : LinearIndependent F2 Q :=
  z.property.comp Sum.inl Sum.inl_injective

/-- The restriction's Grassmann interval satisfies the same total complexity
budget. This uses only `W ≤ span Q ⊔ W`, never the false assumption `Q ⊆ W`. -/
theorem interval_complexity_le (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hQ : LinearIndependent F2 Q) :
    Module.finrank F2 (prefixSpan Q) +
      (n - Module.finrank F2 ↥(prefixSpan Q ⊔ W : Submodule F2 (Ambient n))) ≤
        q + (n - Module.finrank F2 W) := by
  have hA : Module.finrank F2 (prefixSpan Q) = q := by
    change Module.finrank F2 ↥(Submodule.span F2 (Set.range Q)) = q
    exact (finrank_span_eq_card hQ).trans (Fintype.card_fin q)
  have hW : Module.finrank F2 W ≤
      Module.finrank F2 ↥(prefixSpan Q ⊔ W : Submodule F2 (Ambient n)) :=
    Submodule.finrank_mono le_sup_right
  rw [hA]
  omega

def GrassmannPseudorandom {ell : ℕ} (S : Finset (Vertex n ell))
    (r : ℕ) (ε : ℝ) : Prop :=
  ∀ A B : Submodule F2 (Ambient n), A ≤ B →
    Module.finrank F2 A + (n - Module.finrank F2 B) ≤ r →
      relativeDensity S (interval A B) ≤ ε

def completionEvent (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) (z : Fin t → W) : Prop :=
  ∃ h : LinearIndependent F2 (joinedTuple Q W z), completionVertex Q W ⟨z, h⟩ ∈ S

/-- The denominator counts *all* remaining tuples drawn uniformly from W.
Dependent completions are rejected, without conditioning away their mass. -/
def restrictedLiftDensity (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) : ℝ :=
  (Nat.card {z : Fin t → W // completionEvent S Q W z} : ℝ) /
    Nat.card (Fin t → W)

def TuplePseudorandom {ell : ℕ} (S : Finset (Vertex n ell))
    (r : ℕ) (ε : ℝ) : Prop :=
  ∀ q t : ℕ, ∀ h : q + t = ell, ∀ Q : Fin q → Ambient n,
    ∀ W : Submodule F2 (Ambient n), q + (n - Module.finrank F2 W) ≤ r →
      restrictedLiftDensity (h.symm ▸ S) Q W ≤ ε

theorem restrictedLiftDensity_eq_zero_of_dependent (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hQ : ¬ LinearIndependent F2 Q) : restrictedLiftDensity S Q W = 0 := by
  have hE : IsEmpty {z : Fin t → W // completionEvent S Q W z} := by
    refine ⟨fun z => ?_⟩
    obtain ⟨h, _⟩ := z.property
    exact hQ (prefix_independent Q W ⟨z.val, h⟩)
  let := hE
  simp [restrictedLiftDensity]

abbrev IntervalVertex (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :=
  ↥(interval (ell := q + t) (prefixSpan Q) (prefixSpan Q ⊔ W))

def completionIntervalVertex (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) : IntervalVertex (t := t) Q W :=
  ⟨completionVertex Q W z, completion_mem_interval Q W z⟩

def completionFiberEquiv (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (L : IntervalVertex (t := t) Q W) :
    {z : IndependentCompletion (t := t) Q W // completionIntervalVertex Q W z = L} ≃
      RestrictedCompletion (t := t) Q W L.val.val where
  toFun z := ⟨z.val.val, z.val.property,
    congrArg (fun M => M.val.val) z.property⟩
  invFun z := ⟨⟨z.val, z.property.1⟩, Subtype.ext (Subtype.ext z.property.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem interval_completion_nonempty (Q : Fin q → Ambient n)
    (W : Submodule F2 (Ambient n)) (hQ : LinearIndependent F2 Q)
    (L : IntervalVertex (t := t) Q W) :
    Nonempty (RestrictedCompletion (t := t) Q W L.val.val) := by
  have hL := (Finset.mem_filter.mp L.property).2
  obtain ⟨z, hz, hspan⟩ := exists_restricted_completion Q W L.val.val hQ
    hL.1 hL.2 L.val.property
  exact ⟨⟨z, hz, hspan⟩⟩

def completionEventEquiv (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :
    {z : Fin t → W // completionEvent S Q W z} ≃
      {z : IndependentCompletion (t := t) Q W // completionVertex Q W z ∈ S} where
  toFun z := ⟨⟨z.val, z.property.choose⟩, z.property.choose_spec⟩
  invFun z := ⟨z.val.val, z.val.property, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def intervalEventEquiv (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :
    {L : IntervalVertex (t := t) Q W // L.val ∈ S} ≃
      ↥(S ∩ interval (prefixSpan Q) (prefixSpan Q ⊔ W)) where
  toFun L := ⟨L.val.val, Finset.mem_inter.mpr ⟨L.property, L.val.property⟩⟩
  invFun L := ⟨⟨L.val, (Finset.mem_inter.mp L.property).2⟩,
    (Finset.mem_inter.mp L.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The uniform law on successful completions is exactly the uniform
Grassmann interval law, even when the fixed prefix is not contained in W. -/
theorem independent_density_eq_interval (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hQ : LinearIndependent F2 Q)
    (z₀ : IndependentCompletion (t := t) Q W) :
    (Nat.card {z : IndependentCompletion (t := t) Q W // completionVertex Q W z ∈ S} : ℝ) /
      Nat.card (IndependentCompletion (t := t) Q W) =
        relativeDensity S (interval (prefixSpan Q) (prefixSpan Q ⊔ W)) := by
  let f := completionIntervalVertex (t := t) Q W
  let c := Nat.card {z : IndependentCompletion (t := t) Q W // f z = f z₀}
  have hc : 0 < c := by
    let : Nonempty {z : IndependentCompletion (t := t) Q W // f z = f z₀} :=
      ⟨⟨z₀, rfl⟩⟩
    exact Nat.card_pos
  have hf (L : IntervalVertex (t := t) Q W) :
      Nat.card {z : IndependentCompletion (t := t) Q W // f z = L} = c := by
    obtain ⟨a⟩ := interval_completion_nonempty Q W hQ L
    obtain ⟨b⟩ := interval_completion_nonempty Q W hQ (f z₀)
    exact (Nat.card_congr (completionFiberEquiv Q W L)).trans
      ((restrictedCompletionCard_eq a b).trans
        (Nat.card_congr (completionFiberEquiv Q W (f z₀))).symm)
  have he := uniformFiber_card_ratio f (fun L => L.val ∈ S) c hc hf
  change (Nat.card {z : IndependentCompletion (t := t) Q W // completionVertex Q W z ∈ S} : ℝ) /
      Nat.card (IndependentCompletion (t := t) Q W) =
    (Nat.card {L : IntervalVertex (t := t) Q W // L.val ∈ S} : ℝ) /
      Nat.card (IntervalVertex (t := t) Q W) at he
  rw [he, Nat.card_congr (intervalEventEquiv S Q W)]
  simp only [IntervalVertex, Nat.card_eq_finsetCard, relativeDensity]

/-- The unconditioned restricted lift has density at most that of its exact
Grassmann interval. Unlike a union-bound argument, no independence-error term
is needed because dependent tuples are rejected by the lift. -/
theorem restrictedLiftDensity_le_interval (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hQ : LinearIndependent F2 Q) :
    restrictedLiftDensity S Q W ≤
      relativeDensity S (interval (prefixSpan Q) (prefixSpan Q ⊔ W)) := by
  unfold restrictedLiftDensity
  rw [Nat.card_congr (completionEventEquiv S Q W)]
  by_cases h : Nonempty (IndependentCompletion (t := t) Q W)
  · obtain ⟨z₀⟩ := h
    exact (subtype_event_ratio_le
      (fun z : Fin t → W => LinearIndependent F2 (joinedTuple Q W z))
      (fun z => completionVertex Q W z ∈ S)).trans
        (le_of_eq (independent_density_eq_interval S Q W hQ z₀))
  · let : IsEmpty (IndependentCompletion (t := t) Q W) := not_nonempty_iff.mp h
    simp only [Nat.card_of_isEmpty, Nat.cast_zero, zero_div]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The full KMS restriction transfer, with the stronger exact ε bound. -/
theorem grassmann_pseudorandom_restricted {r : ℕ} {ε : ℝ}
    (S : Finset (Vertex n (q + t))) (hS : GrassmannPseudorandom S r ε)
    (hε : 0 ≤ ε) (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hbudget : q + (n - Module.finrank F2 W) ≤ r) :
    restrictedLiftDensity S Q W ≤ ε := by
  by_cases hQ : LinearIndependent F2 Q
  · exact (restrictedLiftDensity_le_interval S Q W hQ).trans
      (hS (prefixSpan Q) (prefixSpan Q ⊔ W) le_sup_left
        ((interval_complexity_le Q W hQ).trans hbudget))
  · rw [restrictedLiftDensity_eq_zero_of_dependent S Q W hQ]
    exact hε

theorem grassmann_pseudorandom_lift {ell r : ℕ} {ε : ℝ}
    (S : Finset (Vertex n ell)) (hS : GrassmannPseudorandom S r ε)
    (hε : 0 ≤ ε) : TuplePseudorandom S r ε := by
  intro q t h Q W hb
  subst ell
  exact grassmann_pseudorandom_restricted S hS hε Q W hb

end
end UniqueGamesTheorem.Inverse.KMSBasisComparisonPseudorandom

end

section

/-! Exact relative-density transport across an injective finite matrix chart. -/

namespace UniqueGamesTheorem.Inverse.KMS

noncomputable section
open scoped Classical

variable {Ω Γ : Type*} [DecidableEq Ω] [DecidableEq Γ]

/-- An embedding preserves the numerator and denominator of relative density. -/
theorem relativeDensity_map (e : Ω ↪ Γ) (S I : Finset Ω) :
    relativeDensity (S.map e) (I.map e) = relativeDensity S I := by
  unfold relativeDensity
  rw [← Finset.map_inter]
  simp

theorem relativeDensity_equiv (e : Ω ≃ Γ) (S I : Finset Ω) :
    relativeDensity (S.map e.toEmbedding) (I.map e.toEmbedding) =
      relativeDensity S I :=
  relativeDensity_map e.toEmbedding S I

variable [Fintype Ω]

/-- The image of the entire finite matrix domain. -/
def finiteChart (e : Ω ↪ Γ) : Finset Γ := Finset.univ.map e

/-- Matrices whose chart images lie in an ambient interval. -/
def intervalPreimage (e : Ω ↪ Γ) (I : Finset Γ) : Finset Ω :=
  Finset.univ.filter fun x => e x ∈ I

omit [DecidableEq Ω] in
theorem map_intervalPreimage (e : Ω ↪ Γ) (I : Finset Γ) :
    (intervalPreimage e I).map e = I ∩ finiteChart e := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hx).2,
      Finset.mem_map.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
  · intro hy
    obtain ⟨x, _, hxy⟩ := Finset.mem_map.mp (Finset.mem_inter.mp hy).2
    refine Finset.mem_map.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩, hxy⟩
    simpa only [hxy] using (Finset.mem_inter.mp hy).1

omit [DecidableEq Ω] [DecidableEq Γ] in
theorem mapped_subset_finiteChart (e : Ω ↪ Γ) (S : Finset Ω) :
    S.map e ⊆ finiteChart e := by
  intro y hy
  obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hy
  exact Finset.mem_map.mpr ⟨x, Finset.mem_univ x, rfl⟩

/-- Pulling the chart-intersected interval back to matrices preserves density
exactly; matrices are sampled uniformly on this actual preimage. -/
theorem relativeDensity_intervalPreimage (e : Ω ↪ Γ) (S : Finset Ω) (I : Finset Γ) :
    relativeDensity (S.map e) (I ∩ finiteChart e) =
      relativeDensity S (intervalPreimage e I) := by
  rw [← map_intervalPreimage]
  exact relativeDensity_map e S (intervalPreimage e I)

/-- A nonempty lifted fiber in an ambient interval yields a nonempty matrix
slice and loses no relative-density factor on transport. -/
theorem ambient_density_passes_to_preimage (e : Ω ↪ Γ)
    (S : Finset Ω) (I : Finset Γ) (hSI : (S.map e ∩ I).Nonempty)
    {α : ℝ} (hα : α ≤ relativeDensity (S.map e) I) :
    (intervalPreimage e I).Nonempty ∧ α ≤ relativeDensity S (intervalPreimage e I) := by
  obtain ⟨y, hy⟩ := hSI
  obtain ⟨x, _, hxy⟩ := Finset.mem_map.mp (Finset.mem_inter.mp hy).1
  have hx : x ∈ intervalPreimage e I := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ x, by simpa only [hxy] using (Finset.mem_inter.mp hy).2⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  have h := density_bound_passes_to_chart (S.map e) I (finiteChart e)
    (mapped_subset_finiteChart e S) ⟨y, hy⟩ hα
  rw [relativeDensity_intervalPreimage] at h
  exact h.2

end
end UniqueGamesTheorem.Inverse.KMS

end

end OAI
