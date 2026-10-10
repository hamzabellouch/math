import Mathlib
import OAI.Computability.DirectedFeedback.Probability.KMSMomentConstants

namespace OAI

namespace DFVSGames.Inverse.KMSBasisComparisonPseudorandom

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
end DFVSGames.Inverse.KMSBasisComparisonPseudorandom

namespace DFVSGames.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison

variable {n q t : ℕ}

def tupleBasis (q t : ℕ) : Module.Basis (Fin q ⊕ Fin t) F2 (Ambient (q + t)) :=
  (Pi.basisFun F2 (Fin (q + t))).reindex finSumFinEquiv.symm

def tupleMapEquiv : ((Fin q ⊕ Fin t) → Ambient n) ≃ BasisMap n (q + t) :=
  ((tupleBasis q t).constr F2).toEquiv

def tupleMap (x : (Fin q ⊕ Fin t) → Ambient n) : BasisMap n (q + t) :=
  (tupleBasis q t).constr F2 x

theorem tupleMap_range (x : (Fin q ⊕ Fin t) → Ambient n) :
    LinearMap.range (tupleMap x) = Submodule.span F2 (Set.range x) :=
  (tupleBasis q t).constr_range F2

@[simp] theorem tupleMap_basis (x : (Fin q ⊕ Fin t) → Ambient n)
    (i : Fin q ⊕ Fin t) : tupleMap x (tupleBasis q t i) = x i :=
  (tupleBasis q t).constr_basis F2 x i

theorem tupleMap_injective_iff (x : (Fin q ⊕ Fin t) → Ambient n) :
    Function.Injective (tupleMap x) ↔ LinearIndependent F2 x := by
  constructor
  · intro h
    have hi := (tupleBasis q t).linearIndependent.map' (tupleMap x)
      (LinearMap.ker_eq_bot.mpr h)
    simpa only [Function.comp_def, tupleMap_basis] using hi
  · intro h
    exact (tupleBasis q t).injective_constr_of_linearIndependent h

theorem inLift_tupleMap_iff (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) (z : Fin t → W) :
    InLift S (tupleMap (joinedTuple Q W z)) ↔ completionEvent S Q W z := by
  constructor
  · intro h
    have hi := (tupleMap_injective_iff _).mp (injective_of_inLift h)
    obtain ⟨L, hLS, hr⟩ := h
    refine ⟨hi, ?_⟩
    have he : completionVertex Q W ⟨z, hi⟩ = L := by
      apply Subtype.ext
      exact (tupleMap_range _).symm.trans hr
    simpa only [he] using hLS
  · rintro ⟨hi, hmem⟩
    exact ⟨completionVertex Q W ⟨z, hi⟩, hmem, tupleMap_range _⟩

theorem restrictedLiftDensity_eq_expect (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :
    restrictedLiftDensity S Q W =
      𝔼 z : Fin t → W, liftedIndicator S (tupleMap (joinedTuple Q W z)) := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [liftedIndicator, inLift_tupleMap_iff]
  rw [Finset.sum_boole]
  simp only [restrictedLiftDensity, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem grassmann_pseudorandom_lift_expect {r : ℕ} {ε : ℝ}
    (S : Finset (Vertex n (q + t))) (hS : GrassmannPseudorandom S r ε)
    (hε : 0 ≤ ε) (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hbudget : q + (n - Module.finrank F2 W) ≤ r) :
    (𝔼 z : Fin t → W, liftedIndicator S (tupleMap (joinedTuple Q W z))) ≤ ε := by
  rw [← restrictedLiftDensity_eq_expect]
  exact grassmann_pseudorandom_restricted S hS hε Q W hbudget

end
end DFVSGames.Inverse.KMSBasisComparisonPseudorandom

namespace DFVSGames.Inverse.KMSAffineRestriction
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom

variable {n ell q t r : ℕ} {ε : ℝ}

theorem lifted_expect_in_basis (S : Finset (Vertex n ell))
    (hS : GrassmannPseudorandom S r ε) (hε : 0 ≤ ε)
    (b : Module.Basis (Fin q ⊕ Fin t) F2 (Ambient ell))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (hbudget : q + (n - Module.finrank F2 W) ≤ r) :
    (𝔼 z : Fin t → W, liftedIndicator S (b.constr F2 (joinedTuple Q W z))) ≤ ε := by
  have hdim : ell = q + t := by
    simpa [Ambient] using Module.finrank_eq_card_basis b
  subst ell
  have hc := grassmann_pseudorandom_lift_expect S hS hε Q W hbudget
  convert hc using 1
  apply Finset.expect_congr rfl
  intro z _
  unfold liftedIndicator InLift
  rw [b.constr_range F2, tupleMap_range]

def affineCoordinates {E W : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup W] [Module F2 W]
    (b : Module.Basis (Fin t) F2 E) (T : E →ₗ[F2] W) :
    (E →ₗ[F2] W) ≃ (Fin t → W) :=
  ((b.constr F2).toEquiv).symm.trans (Equiv.addLeft (fun i => T (b i)))

@[simp] theorem affineCoordinates_apply {E W : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup W] [Module F2 W]
    (b : Module.Basis (Fin t) F2 E) (T H : E →ₗ[F2] W) (i : Fin t) :
    affineCoordinates b T H i = T (b i) + H (b i) := rfl

theorem lifted_expect_shifted_basis {E0 : Type*}
    [AddCommGroup E0] [Module F2 E0]
    (S : Finset (Vertex n ell)) (hS : GrassmannPseudorandom S r ε) (hε : 0 ≤ ε)
    (b : Module.Basis (Fin q ⊕ Fin t) F2 (Ambient ell))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    [Fintype (E0 →ₗ[F2] W)]
    (b0 : Module.Basis (Fin t) F2 E0) (T0 : E0 →ₗ[F2] W)
    (hbudget : q + (n - Module.finrank F2 W) ≤ r) :
    (𝔼 H : E0 →ₗ[F2] W, liftedIndicator S
      (b.constr F2 (joinedTuple Q W (fun i => T0 (b0 i) + H (b0 i))))) ≤ ε := by
  have heq : (𝔼 H : E0 →ₗ[F2] W, liftedIndicator S
      (b.constr F2 (joinedTuple Q W (fun i => T0 (b0 i) + H (b0 i))))) =
      𝔼 z : Fin t → W, liftedIndicator S (b.constr F2 (joinedTuple Q W z)) := by
    apply Fintype.expect_equiv (affineCoordinates b0 T0)
    intro H
    rfl
  rw [heq]
  exact lifted_expect_in_basis S hS hε b Q W hbudget

end
end DFVSGames.Inverse.KMSAffineRestriction

namespace DFVSGames.Inverse.KMSAffineRestrictionComplement

variable {K E F : Type*} [DivisionRing K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F]

theorem exists_bounded_complement_of_linearMap
    (V1 : Submodule K E) (L : E →ₗ[K] F) :
    ∃ U E0 : Submodule K E,
      V1 ≤ U ∧ E0 ≤ LinearMap.ker L ∧ IsCompl U E0 ∧
      Module.finrank K U ≤
        Module.finrank K V1 + Module.finrank K (LinearMap.range L) := by
  obtain ⟨D, hD⟩ := (LinearMap.ker L).exists_isCompl
  let U : Submodule K E := V1 ⊔ D
  have hcover : Codisjoint (LinearMap.ker L) U :=
    hD.codisjoint.mono_right le_sup_right
  obtain ⟨E0, hE0, hcompl⟩ := hcover.exists_isCompl
  refine ⟨U, E0, le_sup_left, hE0, hcompl.symm, ?_⟩
  have hdim := Submodule.finrank_add_eq_of_isCompl hD
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hDdim : Module.finrank K D = Module.finrank K (LinearMap.range L) := by
    omega
  exact (Submodule.finrank_add_le_finrank_add_finrank V1 D).trans
    (by rw [hDdim])

theorem exists_bounded_complement [FiniteDimensional K F]
    (V1 : Submodule K E) (W : Submodule K F) (T : E →ₗ[K] F) :
    ∃ U E0 : Submodule K E,
      V1 ≤ U ∧ E0 ≤ LinearMap.ker (W.mkQ.comp T) ∧ IsCompl U E0 ∧
      Module.finrank K U ≤
        Module.finrank K V1 + Module.finrank K (F ⧸ W) := by
  obtain ⟨U, E0, hV1, hE0, hcompl, hdim⟩ :=
    exists_bounded_complement_of_linearMap V1 (W.mkQ.comp T)
  refine ⟨U, E0, hV1, hE0, hcompl, hdim.trans ?_⟩
  exact Nat.add_le_add_left (Submodule.finrank_le (LinearMap.range (W.mkQ.comp T))) _

end DFVSGames.Inverse.KMSAffineRestrictionComplement

namespace DFVSGames.Inverse.KMSAffineRestrictionSplit

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Fourier.MatrixRestrictions
open scoped BigOperators

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

abbrev localVanishing (D U : Submodule F2 E) : Submodule F2 U :=
  D.comap U.subtype

def splitLeft (D U : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) : Parameter (localVanishing D U) W :=
  (localVanishing D U).liftQ (A.comp (D.mkQ.comp U.subtype)) (by
    intro x hx
    change A (D.mkQ (x : E)) = 0
    have hz : D.mkQ (x : E) = 0 :=
      (Submodule.Quotient.mk_eq_zero D).mpr hx
    rw [hz, map_zero])

@[simp] theorem splitLeft_apply (D U : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) (x : U) :
    splitLeft D U W A ((localVanishing D U).mkQ x) =
      A (D.mkQ (x : E)) := rfl

def splitRight (D E₀ : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) : E₀ →ₗ[F2] W :=
  A.comp (D.mkQ.comp E₀.subtype)

@[simp] theorem splitRight_apply (D E₀ : Submodule F2 E) (W : Submodule F2 F)
    (A : Parameter D W) (x : E₀) :
    splitRight D E₀ W A x = A (D.mkQ (x : E)) := rfl

def joinMap (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hc : IsCompl U E₀) (B : Parameter (localVanishing D U) W)
    (C : E₀ →ₗ[F2] W) : E →ₗ[F2] W :=
  B.comp ((localVanishing D U).mkQ.comp (U.projectionOnto E₀ hc)) +
    C.comp (E₀.projectionOnto U hc.symm)

@[simp] theorem joinMap_apply_left (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : U) :
    joinMap D U E₀ W hc B C (x : E) = B ((localVanishing D U).mkQ x) := by
  simp [joinMap]

@[simp] theorem joinMap_apply_right (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : E₀) :
    joinMap D U E₀ W hc B C (x : E) = C x := by
  simp [joinMap]

theorem joinMap_vanishes (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    D ≤ (joinMap D U E₀ W hc B C).ker := by
  intro x hx
  let u : U := ⟨x, hDU hx⟩
  change joinMap D U E₀ W hc B C (u : E) = 0
  rw [joinMap_apply_left]
  have hz : (localVanishing D U).mkQ u = 0 :=
    (Submodule.Quotient.mk_eq_zero (localVanishing D U)).mpr hx
  rw [hz, map_zero]

def join (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) : Parameter D W :=
  D.liftQ (joinMap D U E₀ W hc B C) (joinMap_vanishes D U E₀ W hDU hc B C)

@[simp] theorem join_apply (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : E) :
    join D U E₀ W hDU hc B C (D.mkQ x) = joinMap D U E₀ W hc B C x := rfl

@[simp] theorem join_embed_apply_left (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : U) :
    embed D W (join D U E₀ W hDU hc B C) (x : E) =
      (B ((localVanishing D U).mkQ x) : F) := by
  rw [embed_apply, join_apply, joinMap_apply_left]

@[simp] theorem join_embed_apply_right (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) (x : E₀) :
    embed D W (join D U E₀ W hDU hc B C) (x : E) = (C x : F) := by
  rw [embed_apply, join_apply, joinMap_apply_right]

theorem splitLeft_join (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    splitLeft D U W (join D U E₀ W hDU hc B C) = B := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := (localVanishing D U).mkQ_surjective q
  rw [splitLeft_apply, join_apply, joinMap_apply_left]

theorem splitRight_join (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    splitRight D E₀ W (join D U E₀ W hDU hc B C) = C := by
  apply LinearMap.ext
  intro x
  rw [splitRight_apply, join_apply, joinMap_apply_right]

theorem join_split (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀) (A : Parameter D W) :
    join D U E₀ W hDU hc (splitLeft D U W A) (splitRight D E₀ W A) = A := by
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := D.mkQ_surjective q
  obtain ⟨⟨u, v⟩, hx⟩ := (Submodule.prodEquivOfIsCompl U E₀ hc).surjective x
  change (u : E) + (v : E) = x at hx
  rw [← hx]
  simp only [map_add, join_apply, joinMap_apply_left, joinMap_apply_right,
    splitLeft_apply, splitRight_apply]

def splitEquiv (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀) :
    Parameter D W ≃ₗ[F2]
      (Parameter (localVanishing D U) W × (E₀ →ₗ[F2] W)) where
  toFun A := (splitLeft D U W A, splitRight D E₀ W A)
  invFun P := join D U E₀ W hDU hc P.1 P.2
  left_inv := join_split D U E₀ W hDU hc
  right_inv P := Prod.ext (splitLeft_join D U E₀ W hDU hc P.1 P.2)
    (splitRight_join D U E₀ W hDU hc P.1 P.2)
  map_add' A B := by
    apply Prod.ext
    · apply LinearMap.ext
      intro q
      obtain ⟨x, rfl⟩ := (localVanishing D U).mkQ_surjective q
      rfl
    · rfl
  map_smul' a A := by
    apply Prod.ext
    · apply LinearMap.ext
      intro q
      obtain ⟨x, rfl⟩ := (localVanishing D U).mkQ_surjective q
      rfl
    · rfl

@[simp] theorem splitEquiv_symm_apply (D U E₀ : Submodule F2 E)
    (W : Submodule F2 F) (hDU : D ≤ U) (hc : IsCompl U E₀)
    (B : Parameter (localVanishing D U) W) (C : E₀ →ₗ[F2] W) :
    (splitEquiv D U E₀ W hDU hc).symm (B, C) = join D U E₀ W hDU hc B C := rfl

instance freeFintype [Finite E] [Finite F] (E₀ : Submodule F2 E)
    (W : Submodule F2 F) : Fintype (E₀ →ₗ[F2] W) := by
  classical
  letI : Fintype E₀ := Fintype.ofFinite E₀
  letI : Fintype W := Fintype.ofFinite W
  exact Fintype.ofInjective (fun C : E₀ →ₗ[F2] W => (C : E₀ → W))
    DFunLike.coe_injective

theorem expect_join [Finite E] [Finite F]
    (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀) (f : Parameter D W → ℝ) :
    (𝔼 A : Parameter D W, f A) =
      𝔼 B : Parameter (localVanishing D U) W,
        𝔼 C : E₀ →ₗ[F2] W, f (join D U E₀ W hDU hc B C) := by
  calc
    _ = 𝔼 P : Parameter (localVanishing D U) W × (E₀ →ₗ[F2] W),
        f (join D U E₀ W hDU hc P.1 P.2) :=
      Fintype.expect_equiv (splitEquiv D U E₀ W hDU hc).toEquiv _ _
        (fun A => congrArg f (join_split D U E₀ W hDU hc A).symm)
    _ = _ := by
      rw [← Finset.univ_product_univ, Finset.expect_product]

theorem expect_restrict [Finite E] [Finite F]
    (D U E₀ : Submodule F2 E) (W : Submodule F2 F)
    (hDU : D ≤ U) (hc : IsCompl U E₀) (T : E →ₗ[F2] F)
    (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 A : Parameter D W, restrict f D W T A) =
      𝔼 B : Parameter (localVanishing D U) W,
        𝔼 C : E₀ →ₗ[F2] W, f (translate D W T (join D U E₀ W hDU hc B C)) :=
  expect_join D U E₀ W hDU hc (restrict f D W T)

end
end DFVSGames.Inverse.KMSAffineRestrictionSplit

namespace DFVSGames.Inverse.KMSAffineRestriction
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom
open DFVSGames.Fourier.MatrixRestrictions
open KMSAffineRestrictionSplit

variable {n ell q t : ℕ}

def complementBasis (U E0 : Submodule F2 (Ambient ell)) (hc : IsCompl U E0)
    (bU : Module.Basis (Fin q) F2 U) (b0 : Module.Basis (Fin t) F2 E0) :
    Module.Basis (Fin q ⊕ Fin t) F2 (Ambient ell) :=
  (bU.prod b0).map (Submodule.prodEquivOfIsCompl U E0 hc)

@[simp] theorem complementBasis_inl (U E0 : Submodule F2 (Ambient ell))
    (hc : IsCompl U E0) (bU : Module.Basis (Fin q) F2 U)
    (b0 : Module.Basis (Fin t) F2 E0) (i : Fin q) :
    complementBasis U E0 hc bU b0 (Sum.inl i) = (bU i : Ambient ell) := by
  simp [complementBasis, Module.Basis.prod_apply]

@[simp] theorem complementBasis_inr (U E0 : Submodule F2 (Ambient ell))
    (hc : IsCompl U E0) (bU : Module.Basis (Fin q) F2 U)
    (b0 : Module.Basis (Fin t) F2 E0) (i : Fin t) :
    complementBasis U E0 hc bU b0 (Sum.inr i) = (b0 i : Ambient ell) := by
  simp [complementBasis, Module.Basis.prod_apply]

def freeCenter (E0 : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (T : BasisMap n ell) (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T)) : E0 →ₗ[F2] W :=
  (T.comp E0.subtype).codRestrict W fun x =>
    (Submodule.Quotient.mk_eq_zero W).mp (hE0 x.property)

@[simp] theorem freeCenter_coe (E0 : Submodule F2 (Ambient ell))
    (W : Submodule F2 (Ambient n)) (T : BasisMap n ell)
    (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T)) (x : E0) :
    (freeCenter E0 W T hE0 x : Ambient n) = T x := rfl

theorem translate_join_eq_constr
    (D U E0 : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (hDU : D ≤ U) (hc : IsCompl U E0) (T : BasisMap n ell)
    (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T))
    (bU : Module.Basis (Fin q) F2 U) (b0 : Module.Basis (Fin t) F2 E0)
    (B : Parameter (localVanishing D U) W) (C : E0 →ₗ[F2] W) :
    DFVSGames.Fourier.MatrixRestrictions.translate D W T (join D U E0 W hDU hc B C) =
      (complementBasis U E0 hc bU b0).constr F2
        (joinedTuple
          (fun i => T (bU i) + (B ((localVanishing D U).mkQ (bU i)) : Ambient n)) W
          (fun i => freeCenter E0 W T hE0 (b0 i) + C (b0 i))) := by
  apply (complementBasis U E0 hc bU b0).ext
  intro i
  rw [Module.Basis.constr_basis]
  cases i with
  | inl i =>
      simp only [complementBasis_inl, joinedTuple, Sum.elim_inl,
        DFVSGames.Fourier.MatrixRestrictions.translate, LinearMap.add_apply]
      rw [join_embed_apply_left]
  | inr i =>
      simp only [complementBasis_inr, joinedTuple, Sum.elim_inr,
        DFVSGames.Fourier.MatrixRestrictions.translate, LinearMap.add_apply]
      rw [join_embed_apply_right]
      rfl

theorem affine_expect_of_complement {r : ℕ} {ε : ℝ}
    (S : Finset (Vertex n ell)) (hS : GrassmannPseudorandom S r ε) (hε : 0 ≤ ε)
    (D U E0 : Submodule F2 (Ambient ell)) (W : Submodule F2 (Ambient n))
    (hDU : D ≤ U) (hc : IsCompl U E0) (T : BasisMap n ell)
    (hE0 : E0 ≤ LinearMap.ker (W.mkQ.comp T))
    (hbudget : Module.finrank F2 U + (n - Module.finrank F2 W) ≤ r) :
    (𝔼 A : Parameter D W, restrict (liftedIndicator S) D W T A) ≤ ε := by
  rw [expect_restrict D U E0 W hDU hc T]
  apply Finset.expect_le Finset.univ_nonempty
  intro B _
  let bU := Module.finBasis F2 U
  let b0 := Module.finBasis F2 E0
  have heq :
      (𝔼 C : E0 →ₗ[F2] W,
        liftedIndicator S (DFVSGames.Fourier.MatrixRestrictions.translate D W T (join D U E0 W hDU hc B C))) =
      𝔼 C : E0 →ₗ[F2] W,
        liftedIndicator S ((complementBasis U E0 hc bU b0).constr F2
          (joinedTuple
            (fun i => T (bU i) + (B ((localVanishing D U).mkQ (bU i)) : Ambient n)) W
            (fun i => freeCenter E0 W T hE0 (b0 i) + C (b0 i)))) := by
    apply Finset.expect_congr rfl
    intro C _
    rw [translate_join_eq_constr D U E0 W hDU hc T hE0 bU b0 B C]
  rw [heq]
  exact lifted_expect_shifted_basis S hS hε (complementBasis U E0 hc bU b0)
    _ W b0 (freeCenter E0 W T hE0) hbudget

theorem affine_expect_bound {d : ℕ} {ε : ℝ}
    (S : Finset (Vertex n ell)) (hS : GrassmannPseudorandom S (2 * d) ε)
    (hε : 0 ≤ ε) (D : Submodule F2 (Ambient ell))
    (W : Submodule F2 (Ambient n)) (T : BasisMap n ell)
    (horder : order D W ≤ d) :
    (𝔼 A : Parameter D W, restrict (liftedIndicator S) D W T A) ≤ ε := by
  obtain ⟨U, E0, hDU, hE0, hc, hdim⟩ :=
    KMSAffineRestrictionComplement.exists_bounded_complement D W T
  have hcodim : n - Module.finrank F2 W = Module.finrank F2 (KMS.Ambient n ⧸ W) := by
    have hd := W.finrank_quotient_add_finrank
    have hn : Module.finrank F2 (KMS.Ambient n) = n := by simp [KMS.Ambient]
    rw [hn] at hd
    omega
  apply affine_expect_of_complement S hS hε D U E0 W hDU hc T hE0
  rw [hcodim]
  change Module.finrank F2 D + Module.finrank F2 (KMS.Ambient n ⧸ W) ≤ d at horder
  omega

theorem affine_squared_expect_bound {d : ℕ} {ε : ℝ}
    (S : Finset (Vertex n ell)) (hS : GrassmannPseudorandom S (2 * d) ε)
    (hε : 0 ≤ ε) (D : Submodule F2 (Ambient ell))
    (W : Submodule F2 (Ambient n)) (T : BasisMap n ell)
    (horder : order D W ≤ d) :
    (𝔼 A : Parameter D W, (restrict (liftedIndicator S) D W T A) ^ 2) ≤ ε := by
  have heq : (𝔼 A : Parameter D W, (restrict (liftedIndicator S) D W T A) ^ 2) =
      𝔼 A : Parameter D W, restrict (liftedIndicator S) D W T A := by
    apply Finset.expect_congr rfl
    intro A _
    unfold restrict liftedIndicator
    split <;> norm_num
  rw [heq]
  exact affine_expect_bound S hS hε D W T horder

end
end DFVSGames.Inverse.KMSAffineRestriction

namespace DFVSGames.Inverse.KMSAffineRestrictionPresentation

open DFVSGames.Integration.BinaryLinear
open DFVSGames.Fourier.MatrixRestrictions
open scoped BigOperators

noncomputable section

variable {E F D C : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [AddCommGroup D] [Module F2 D] [AddCommGroup C] [Module F2 C]

def parameterEquiv (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J) :
    (D →ₗ[F2] C) ≃ₗ[F2] Parameter L.ker J.range :=
  LinearEquiv.arrowCongr (L.quotKerEquivOfSurjective hL).symm
    (LinearEquiv.ofInjective J hJ)

@[simp] theorem parameterEquiv_apply_mk (L : E →ₗ[F2] D)
    (hL : Function.Surjective L) (J : C →ₗ[F2] F)
    (hJ : Function.Injective J) (X : D →ₗ[F2] C) (x : E) :
    ((parameterEquiv L hL J hJ X) (L.ker.mkQ x) : F) = J (X (L x)) := rfl

@[simp] theorem embed_parameterEquiv (L : E →ₗ[F2] D)
    (hL : Function.Surjective L) (J : C →ₗ[F2] F)
    (hJ : Function.Injective J) (X : D →ₗ[F2] C) :
    embed L.ker J.range (parameterEquiv L hL J hJ X) = J.comp (X.comp L) := by
  apply LinearMap.ext
  intro x
  rfl

@[simp] theorem translate_parameterEquiv (L : E →ₗ[F2] D)
    (hL : Function.Surjective L) (J : C →ₗ[F2] F)
    (hJ : Function.Injective J) (T : E →ₗ[F2] F) (X : D →ₗ[F2] C) :
    DFVSGames.Fourier.MatrixRestrictions.translate L.ker J.range T (parameterEquiv L hL J hJ X) =
      T + J.comp (X.comp L) := by
  rw [DFVSGames.Fourier.MatrixRestrictions.translate, embed_parameterEquiv]

theorem expect_presentation [Finite E] [Finite F] [Fintype (D →ₗ[F2] C)]
    (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J)
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X : D →ₗ[F2] C, f (T + J.comp (X.comp L))) =
      𝔼 A : Parameter L.ker J.range, restrict f L.ker J.range T A := by
  apply Fintype.expect_equiv (parameterEquiv L hL J hJ).toEquiv
  intro X
  exact congrArg f (translate_parameterEquiv L hL J hJ T X).symm

theorem expect_presentation_sq [Finite E] [Finite F] [Fintype (D →ₗ[F2] C)]
    (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J)
    (T : E →ₗ[F2] F) (f : (E →ₗ[F2] F) → ℝ) :
    (𝔼 X : D →ₗ[F2] C, f (T + J.comp (X.comp L)) ^ 2) =
      𝔼 A : Parameter L.ker J.range, (restrict f L.ker J.range T A) ^ 2 :=
  expect_presentation L hL J hJ T (fun X => f X ^ 2)

theorem order_add_dimensions [FiniteDimensional F2 E] [FiniteDimensional F2 F]
    (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J) :
    order L.ker J.range + Module.finrank F2 D + Module.finrank F2 C =
      Module.finrank F2 E + Module.finrank F2 F := by
  have hD := L.ker.finrank_quotient_add_finrank
  have hD' := (L.quotKerEquivOfSurjective hL).finrank_eq
  have hF := J.range.finrank_quotient_add_finrank
  have hC := (LinearEquiv.ofInjective J hJ).finrank_eq
  unfold order
  omega

theorem order_le_of_dimensions [FiniteDimensional F2 E] [FiniteDimensional F2 F]
    (L : E →ₗ[F2] D) (hL : Function.Surjective L)
    (J : C →ₗ[F2] F) (hJ : Function.Injective J) (r : ℕ)
    (h : Module.finrank F2 E + Module.finrank F2 F ≤
      Module.finrank F2 D + Module.finrank F2 C + r) :
    order L.ker J.range ≤ r := by
  have hdim := order_add_dimensions L hL J hJ
  omega

end
end DFVSGames.Inverse.KMSAffineRestrictionPresentation

end OAI
