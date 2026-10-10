import OAI.Computability.UniqueGames.Analysis.AntecedentCountLemmas
import OAI.Computability.UniqueGames.Analysis.BadConvolution
import OAI.Computability.UniqueGames.Analysis.FiberEnergyLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.A5ReverseIndex

open UniqueGamesTheorem.Integration.BinaryLinear
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W : Type*} [AddCommGroup V] [Module F2 V]
  [AddCommGroup W] [Module F2 W]

/-- Earlier codomain constraints inside the final codomain constraint. -/
abbrev EarlierA (A' : Submodule F2 V) (i : ℕ) :=
  {A : Submodule F2 V // A ≤ A' ∧ Module.finrank F2 A = i}

/-- Earlier retained domains containing the final retained domain. -/
abbrev EarlierB (B' : Submodule F2 W) (j : ℕ) :=
  {B : Submodule F2 W // B' ≤ B ∧ Module.finrank F2 (W ⧸ B) = j}

/-- Natural frequency coordinates for an earlier pair inside a fixed final
pair. This is a change of domain and codomain separately. -/
def frequencyEquiv (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B) :
    (B' →ₗ[F2] (V ⧸ A')) ≃ₗ[F2]
      ((B'.comap B.subtype) →ₗ[F2] ((V ⧸ A) ⧸ A'.map A.mkQ)) :=
  LinearEquiv.arrowCongr
    (SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩)
    (Submodule.quotientQuotientEquivQuotient A A' hA).symm

def relativeFrequency (A A' : Submodule F2 V) (B' B : Submodule F2 W)
    (hA : A ≤ A') (hB : B' ≤ B) (Y : B' →ₗ[F2] (V ⧸ A')) :=
  frequencyEquiv A A' B' B hA hB Y

theorem relativeFrequency_rank (A A' : Submodule F2 V)
    (B' B : Submodule F2 W) (hA : A ≤ A') (hB : B' ≤ B)
    (Y : B' →ₗ[F2] (V ⧸ A')) :
    Module.finrank F2 (relativeFrequency A A' B' B hA hB Y).range =
      Module.finrank F2 Y.range :=
  CoordinateTransport.finrank_range_transport
    (SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩)
    (Submodule.quotientQuotientEquivQuotient A A' hA).symm Y

/-- The exact reverse fiber after the earlier dimensions are fixed. -/
abbrev Ancestor (A' : Submodule F2 V) (B' : Submodule F2 W)
    (Y : B' →ₗ[F2] (V ⧸ A')) (i j : ℕ) :=
  Σ A : EarlierA A' i, Σ B : EarlierB B' j,
    AntecedentCount.Antecedent (B'.comap B.val.subtype) (A'.map A.val.mkQ)
      (relativeFrequency A.val A' B' B.val A.property.1 B.property.1 Y)

variable [FiniteDimensional F2 V] [FiniteDimensional F2 W]

theorem relative_codomain_dimension (A A' : Submodule F2 V) (hA : A ≤ A') :
    Module.finrank F2 (A'.map A.mkQ) + Module.finrank F2 A =
      Module.finrank F2 A' := by
  have h₁ := (A'.map A.mkQ).finrank_quotient_add_finrank
  have h₂ := A.finrank_quotient_add_finrank
  have h₃ := A'.finrank_quotient_add_finrank
  have h₄ := (Submodule.quotientQuotientEquivQuotient A A' hA).finrank_eq
  omega

theorem relative_domain_codimension_le (B' B : Submodule F2 W) (hB : B' ≤ B) :
    Module.finrank F2 (B ⧸ B'.comap B.subtype) ≤
      Module.finrank F2 (W ⧸ B') := by
  have h₁ := (B'.comap B.subtype).finrank_quotient_add_finrank
  have h₂ := B'.finrank_quotient_add_finrank
  have h₃ := B.finrank_le
  have h₄ := (SubmoduleInterval.lowerIntervalSpaceEquiv B ⟨B', hB⟩).finrank_eq
  change Module.finrank F2 B' = Module.finrank F2 (B'.comap B.subtype) at h₄
  omega

/-- Each fixed earlier pair contributes at most two graph-parameter budgets. -/
theorem card_local_antecedent_le (A A' : Submodule F2 V)
    (B' B : Submodule F2 W) (hA : A ≤ A') (hB : B' ≤ B)
    (Y : B' →ₗ[F2] (V ⧸ A')) (d k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hAd : Module.finrank F2 A' ≤ d)
    (hBd : Module.finrank F2 (W ⧸ B') ≤ d) :
    Nat.card (AntecedentCount.Antecedent
      (B'.comap B.subtype) (A'.map A.mkQ)
      (relativeFrequency A A' B' B hA hB Y)) ≤ 2 ^ (2 * d * k) := by
  apply AntecedentCount.card_antecedent_le
  · simpa only [relativeFrequency_rank] using hY
  · have h := relative_codomain_dimension A A' hA
    omega
  · exact (relative_domain_codimension_le B' B hB).trans hBd

local instance quotientFinite {U : Type*} [AddCommGroup U] [Module F2 U]
    [Finite U] (P : Submodule F2 U) : Finite (U ⧸ P) :=
  Finite.of_surjective P.mkQ P.mkQ_surjective

local instance linearMapFinite {U Z : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup Z] [Module F2 Z] [Finite U] [Finite Z] :
    Finite (U →ₗ[F2] Z) :=
  Finite.of_injective (fun f : U →ₗ[F2] Z => (f : U → Z)) DFunLike.coe_injective

private theorem card_sigma_le {I : Type*} [Fintype I]
    (fiber : I → Type*) [∀ i, Finite (fiber i)] (N : ℕ)
    (h : ∀ i, Nat.card (fiber i) ≤ N) :
    Nat.card (Σ i, fiber i) ≤ Nat.card I * N := by
  rw [Nat.card_sigma]
  calc
    (∑ i, Nat.card (fiber i)) ≤ ∑ _i : I, N := Finset.sum_le_sum (fun i _ => h i)
    _ = Nat.card I * N := by simp [Nat.card_eq_fintype_card]

variable [Finite V] [Finite W]
variable [Fintype (Submodule F2 V)] [Fintype (Submodule F2 W)]

/-- Sharp graph-based upper bound for the entire actual reverse fiber. -/
theorem card_ancestor_le (A' : Submodule F2 V) (B' : Submodule F2 W)
    (Y : B' →ₗ[F2] (V ⧸ A')) (d i j k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hA : Module.finrank F2 A' ≤ d)
    (hB : Module.finrank F2 (W ⧸ B') ≤ d) :
    Nat.card (Ancestor A' B' Y i j) ≤ 2 ^ (d * (i + j) + 2 * d * k) := by
  have hlocal (A : EarlierA A' i) (B : EarlierB B' j) :=
    card_local_antecedent_le A.val A' B' B.val A.property.1 B.property.1
      Y d k hY hA hB
  have hinner (A : EarlierA A' i) :
      Nat.card (Σ B : EarlierB B' j,
        AntecedentCount.Antecedent (B'.comap B.val.subtype) (A'.map A.val.mkQ)
          (relativeFrequency A.val A' B' B.val A.property.1 B.property.1 Y)) ≤
        Nat.card (EarlierB B' j) * 2 ^ (2 * d * k) :=
    card_sigma_le _ _ (hlocal A)
  have htotal : Nat.card (Ancestor A' B' Y i j) ≤
      Nat.card (EarlierA A' i) * (Nat.card (EarlierB B' j) * 2 ^ (2 * d * k)) :=
    card_sigma_le _ _ hinner
  calc
    Nat.card (Ancestor A' B' Y i j) ≤
        Nat.card (EarlierA A' i) * (Nat.card (EarlierB B' j) * 2 ^ (2 * d * k)) := htotal
    _ ≤ 2 ^ (d * i) * (2 ^ (d * j) * 2 ^ (2 * d * k)) :=
      Nat.mul_le_mul (BadConvolution.card_lower_rank_le A' d i hA)
        (Nat.mul_le_mul_right _ (BadConvolution.card_upper_codim_le B' d j hB))
    _ = 2 ^ (d * (i + j) + 2 * d * k) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring

theorem card_ancestor_le_source (A' : Submodule F2 V) (B' : Submodule F2 W)
    (Y : B' →ₗ[F2] (V ⧸ A')) (d i j k : ℕ)
    (hY : Module.finrank F2 Y.range ≤ k)
    (hA : Module.finrank F2 A' ≤ d)
    (hB : Module.finrank F2 (W ⧸ B') ≤ d) (ht : i + j + k ≤ d) :
    Nat.card (Ancestor A' B' Y i j) ≤ 2 ^ (3 * (d * (i + j + k))) := by
  apply (card_ancestor_le A' B' Y d i j k hY hA hB).trans
  apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
  have h := Induction.antecedent_exponent_budget d i j k (i + j + k) rfl ht
  calc
    d * (i + j) + 2 * d * k ≤ d * (i + j) + 2 * d * k + k * k :=
      Nat.le_add_right _ _
    _ ≤ 3 * (d * (i + j + k)) := by simpa only [Nat.mul_assoc] using h

end

end UniqueGamesTheorem.Appendix.A5ReverseIndex

end

end OAI
