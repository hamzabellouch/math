import Mathlib
import OAI.Computability.MaxCut.Games.KMSAnalyticRestrictionTransport

namespace OAI

/-! Explicit dimension-independent constants for the new KMS mixed-energy
argument and the generic A5 aggregation. The eventual expansion theorem only
uses positivity and finiteness of these constants, so no rank cutoff exception
or comparison with an earlier rank-level constant is needed. -/

namespace MaxCutGames.Inverse.KMSMomentConstants
noncomputable section
open KMSFourthMoment

/-- The constant after the genuine mixed-energy estimate and A5 aggregation. -/
def fourthMomentConstant (r : ℕ) : ℝ := 2 ^ (109 * r * r + 2 * r)

theorem fourthMomentConstant_pos (r : ℕ) : 0 < fourthMomentConstant r := by
  unfold fourthMomentConstant
  positivity

theorem fourthMomentConstant_nonneg (r : ℕ) : 0 ≤ fourthMomentConstant r :=
  (fourthMomentConstant_pos r).le

/-- The closed mixed estimate's literal constant has a quadratic exponent. -/
theorem mixedRankConstant_eq (r : ℕ) :
    mixedRankConstant r = (2 : ℝ) ^ (6 * r * r + 2 * r) := by
  unfold mixedRankConstant mixedStepFactor
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

/-- Multiplying by the actual selector-count and A5 constant is exact. -/
theorem a5_mul_mixedRankConstant (r : ℕ) :
    (2 : ℝ) ^ (103 * r * r) * mixedRankConstant r = fourthMomentConstant r := by
  rw [mixedRankConstant_eq, ← pow_add]
  unfold fourthMomentConstant
  congr 1
  ring

theorem fourthMomentConstant_mono {i r : ℕ} (hi : i ≤ r) :
    fourthMomentConstant i ≤ fourthMomentConstant r := by
  unfold fourthMomentConstant
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul_left 109 hi) hi)
    (Nat.mul_le_mul_left 2 hi)

/-- The complete numerical closure, retaining the density and projection
energy factors in the order used by the expansion interface. -/
theorem a5_mixed_bound {i r : ℕ} (hi : i ≤ r) (ε η : ℝ)
    (hε : 0 ≤ ε) (hη : 0 ≤ η) :
    (2 : ℝ) ^ (103 * i * i) * (mixedRankConstant i * ε) * η ≤
      fourthMomentConstant r * η * ε := by
  calc
    _ = fourthMomentConstant i * (η * ε) := by
      rw [← a5_mul_mixedRankConstant]
      ring
    _ ≤ fourthMomentConstant r * (η * ε) :=
      mul_le_mul_of_nonneg_right (fourthMomentConstant_mono hi) (mul_nonneg hη hε)
    _ = _ := by ring

end
end MaxCutGames.Inverse.KMSMomentConstants

namespace MaxCutGames.Inverse.KMS

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
OPEN: no inhabitant of this proposition is supplied. In particular `r` and
`alpha` must be fixed before `ell`, and the ambient threshold may then depend
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
end MaxCutGames.Inverse.KMS

/-!
# The ordered-basis lift of a Grassmann set

The ambient sample space contains every linear map, including singular maps.
The lift accepts exactly maps whose range is one of the specified
`ell`-dimensional subspaces. Thus dependence is rejected, rather than silently
conditioning the ambient uniform distribution on independence.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

abbrev BasisMap (n ell : ℕ) := KMS.Ambient ell →ₗ[KMS.F2] KMS.Ambient n

instance basisMapFinite (n ell : ℕ) : Finite (BasisMap n ell) :=
  Finite.of_injective (fun X : BasisMap n ell => (X : KMS.Ambient ell → KMS.Ambient n))
    DFunLike.coe_injective

instance basisMapFintype (n ell : ℕ) : Fintype (BasisMap n ell) := Fintype.ofFinite _

/-- Membership in the lift, expressed by the actual linear-map range. -/
def InLift {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) (X : BasisMap n ell) : Prop :=
  ∃ L ∈ S, LinearMap.range X = L.val

/-- The lifted finite set in the whole map space. -/
def lift {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) : Finset (BasisMap n ell) :=
  Finset.univ.filter (InLift S)

@[simp] theorem mem_lift {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : X ∈ lift S ↔ InLift S X := by
  simp [lift]

/-- Real Boolean indicator, in the orientation used by the matrix Fourier transform. -/
def liftedIndicator {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : ℝ := if InLift S X then 1 else 0

theorem liftedIndicator_nonneg {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : 0 ≤ liftedIndicator S X := by
  unfold liftedIndicator
  split <;> norm_num

theorem liftedIndicator_le_one {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : liftedIndicator S X ≤ 1 := by
  unfold liftedIndicator
  split <;> norm_num

/-- A map accepted by the lift has full column rank. -/
theorem injective_of_inLift {n ell : ℕ} {S : Finset (KMS.Vertex n ell)}
    {X : BasisMap n ell} (h : InLift S X) : Function.Injective X := by
  obtain ⟨L, _, hL⟩ := h
  have hr : Module.finrank KMS.F2 (LinearMap.range X) = ell := by
    rw [hL]
    exact L.property
  have hd := X.finrank_range_add_finrank_ker
  have he : Module.finrank KMS.F2 (KMS.Ambient ell) = ell := by
    simp [KMS.Ambient]
  have hk : Module.finrank KMS.F2 (LinearMap.ker X) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

/-- The actual Grassmann vertex represented by an injective map. -/
def rangeVertex {n ell : ℕ} (X : BasisMap n ell) (hX : Function.Injective X) :
    KMS.Vertex n ell :=
  ⟨LinearMap.range X, by
    rw [LinearMap.finrank_range_of_inj hX]
    simp [KMS.Ambient]⟩

theorem inLift_iff_rangeVertex_mem {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    InLift S X ↔ rangeVertex X hX ∈ S := by
  constructor
  · rintro ⟨L, hL, hXL⟩
    have he : rangeVertex X hX = L := Subtype.ext hXL
    simpa only [he] using hL
  · intro h
    exact ⟨rangeVertex X hX, h, rfl⟩

/-- A change of the ordered domain basis leaves the range unchanged. -/
theorem inLift_comp_iff {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (g : KMS.Ambient ell ≃ₗ[KMS.F2] KMS.Ambient ell) (X : BasisMap n ell) :
    InLift S (X.comp g.toLinearMap) ↔ InLift S X := by
  unfold InLift
  rw [LinearMap.range_comp_of_range_eq_top X g.range]

/-- The lift is basis-invariant in precisely the Fourier theorem's sense. -/
theorem liftedIndicator_basisInvariant {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) :
    KMSBasisInvariant.IsBasisInvariant (liftedIndicator S) := by
  intro g X
  simp only [liftedIndicator, inLift_comp_iff]

end
end MaxCutGames.Inverse.KMSBasisComparison

/-! Exact finite counting for the restricted-basis lift.  In particular, failed
independent completions contribute zero rather than an additive error. -/

namespace MaxCutGames.Inverse.KMSBasisComparisonPseudorandom

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

/-!
An independent frame inside `L` can be completed using vectors from `W` whenever
`L` lies in the sum of the frame's span and `W`.
-/

noncomputable section
open scoped Classical
open MaxCutGames.Inverse.KMS

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

/-!
# Equal fibers for restricted basis completion

A fixed independent tuple may have vectors outside the restricting submodule.
Nevertheless, any two nonempty fibers of independent completions inside that
submodule are equivalent. The change of basis fixes the fixed tuple, and its
difference from the identity has image in the restricting submodule.
-/

noncomputable section
open scoped Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {q t : ℕ}

/-- Ordered completions in `W` of `Q` to an independent spanning tuple for `L`. -/
def RestrictedCompletion (Q : Fin q → V) (W L : Submodule K V) :=
  {z : Fin t → W //
    LinearIndependent K (Sum.elim Q (fun i => (z i : V))) ∧
      Submodule.span K (Set.range (Sum.elim Q (fun i => (z i : V)))) = L}

variable {Q : Fin q → V} {W L M N : Submodule K V}

/-- A completion, regarded as a basis of the resulting subspace. -/
def completionBasis (z : RestrictedCompletion (t := t) Q W L) :
    Module.Basis (Fin q ⊕ Fin t) K L :=
  (Module.Basis.span z.property.1).map (LinearEquiv.ofEq _ _ z.property.2)

@[simp] theorem completionBasis_coe
    (z : RestrictedCompletion (t := t) Q W L) (i : Fin q ⊕ Fin t) :
    (completionBasis z i : V) = Sum.elim Q (fun j => (z.val j : V)) i := by
  simp [completionBasis]

/-- Recover a restricted completion from a basis having the prescribed prefix. -/
def completionOfBasis (b : Module.Basis (Fin q ⊕ Fin t) K L)
    (hQ : ∀ i, (b (Sum.inl i) : V) = Q i)
    (hW : ∀ i, (b (Sum.inr i) : V) ∈ W) :
    RestrictedCompletion (t := t) Q W L := by
  have hb : Sum.elim Q (fun i => ((⟨b (Sum.inr i), hW i⟩ : W) : V)) =
      fun i => (b i : V) := by
    funext i
    cases i with
    | inl i => exact (hQ i).symm
    | inr i => rfl
  refine ⟨fun i => ⟨b (Sum.inr i), hW i⟩, ?_, ?_⟩
  · rw [hb]
    exact b.linearIndependent.map' L.subtype (by simp)
  · rw [hb]
    calc
      Submodule.span K (Set.range fun i => (b i : V)) =
          (Submodule.span K (Set.range b)).map L.subtype := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = L := by rw [b.span_eq]; simp

/-- The unique basis change carrying the first completion to the second. -/
def completionSpanEquiv
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) : L ≃ₗ[K] M :=
  (completionBasis x).equiv (completionBasis y) (Equiv.refl _)

@[simp] theorem completionSpanEquiv_basis
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (i : Fin q ⊕ Fin t) :
    completionSpanEquiv x y (completionBasis x i) = completionBasis y i := by
  simp [completionSpanEquiv]

@[simp] theorem completionSpanEquiv_symm
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    (completionSpanEquiv x y).symm = completionSpanEquiv y x := by
  simp [completionSpanEquiv]

/-- Changing the completion changes every vector by an element of `W`. -/
theorem completionSpanEquiv_sub_mem
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (v : L) :
    (completionSpanEquiv x y v : V) - (v : V) ∈ W := by
  let d : L →ₗ[K] V := M.subtype.comp (completionSpanEquiv x y).toLinearMap - L.subtype
  have hd : (⊤ : Submodule K L) ≤ W.comap d := by
    rw [← (completionBasis x).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change d (completionBasis x i) ∈ W
    change (completionSpanEquiv x y (completionBasis x i) : V) -
      (completionBasis x i : V) ∈ W
    rw [completionSpanEquiv_basis]
    cases i with
    | inl i => simp
    | inr i =>
      simpa only [completionBasis_coe, Sum.elim_inr] using
        W.sub_mem (y.val i).property (x.val i).property
  exact hd (Submodule.mem_top : v ∈ (⊤ : Submodule K L))

/-- The basis change preserves membership in `W`, without requiring `Q ⊆ W`. -/
theorem completionSpanEquiv_mem_iff
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (v : L) :
    (completionSpanEquiv x y v : V) ∈ W ↔ (v : V) ∈ W := by
  have hd := completionSpanEquiv_sub_mem x y v
  constructor
  · intro hv
    exact (W.sub_mem_iff_right hv).mp hd
  · intro hv
    exact (W.sub_mem_iff_left hv).mp hd

/-- Transport every restricted completion along one fixed basis change. -/
def transportCompletion
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) :
    RestrictedCompletion (t := t) Q W M :=
  completionOfBasis ((completionBasis z).map (completionSpanEquiv x y))
    (by
      intro i
      have h : completionBasis z (Sum.inl i) = completionBasis x (Sum.inl i) := by
        apply Subtype.ext
        simp
      simp [Module.Basis.map_apply, h])
    (by
      intro i
      change (completionSpanEquiv x y (completionBasis z (Sum.inr i)) : V) ∈ W
      apply (completionSpanEquiv_mem_iff x y _).mpr
      simp)

@[simp] theorem transportCompletion_coe
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) (i : Fin t) :
    ((transportCompletion x y z).val i : V) =
      (completionSpanEquiv x y (completionBasis z (Sum.inr i)) : V) := rfl

theorem transportCompletion_inverse
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) :
    transportCompletion y x (transportCompletion x y z) = z := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  rw [transportCompletion_coe]
  have hb : completionBasis (transportCompletion x y z) (Sum.inr i) =
      completionSpanEquiv x y (completionBasis z (Sum.inr i)) := by
    apply Subtype.ext
    simp
  rw [hb, ← completionSpanEquiv_symm, LinearEquiv.symm_apply_apply]
  simp

/-- All nonempty restricted-completion fibers are equivalent. -/
def restrictedCompletionEquiv
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    RestrictedCompletion (t := t) Q W L ≃ RestrictedCompletion (t := t) Q W M where
  toFun := transportCompletion x y
  invFun := transportCompletion y x
  left_inv := transportCompletion_inverse x y
  right_inv := transportCompletion_inverse y x

/-- Equal fiber cardinality follows from the explicit completion equivalence. -/
theorem restrictedCompletionCard_eq
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    Nat.card (RestrictedCompletion (t := t) Q W L) =
      Nat.card (RestrictedCompletion (t := t) Q W M) :=
  Nat.card_congr (restrictedCompletionEquiv x y)

end

/-!
# Restricted densities in the ordered-basis lift

The prefix vectors are arbitrary: they may be dependent, and they need not lie
in the subspace from which the remaining vectors are sampled. The relevant
Grassmann interval has lower endpoint `span Q` and upper endpoint `span Q ⊔ W`.
-/

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
end MaxCutGames.Inverse.KMSBasisComparisonPseudorandom

end OAI
