import Mathlib

namespace OAI

universe u

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

structure RelModel (L : ℕ → Type) where
  carrier : ZFSet.{u}
  rel : (n : ℕ) → L n → (Fin n → carrier) → Prop

namespace RelModel

variable {L : ℕ → Type}

structure IsSubstructure (M N : RelModel.{u} L) : Prop where
  subset : M.carrier ⊆ N.carrier
  restrict : ∀ (n) (r : L n) (a : Fin n → M.carrier),
    M.rel n r a ↔ N.rel n r (fun i => ⟨(a i).val, subset (a i).property⟩)

structure Iso (M N : RelModel.{u} L) where
  toEquiv : M.carrier ≃ N.carrier
  map_rel : ∀ (n) (r : L n) (a : Fin n → M.carrier),
    M.rel n r a ↔ N.rel n r (toEquiv ∘ a)

def IsUnion {ι : Type u} (F : ι → RelModel.{u} L) (U : RelModel.{u} L) : Prop :=
  (∀ i, IsSubstructure (F i) U) ∧
  ∀ x : U.carrier, ∃ i, x.val ∈ (F i).carrier

end RelModel

structure ClassData (L : ℕ → Type) where
  objects : RelModel.{u} L → Prop
  strong : RelModel.{u} L → RelModel.{u} L → Prop

namespace ClassData

variable {L : ℕ → Type} (K : ClassData.{u} L)

def LSBound (θ : Cardinal.{u}) : Prop :=
  ℵ₀ ≤ θ ∧ Cardinal.lift.{u, 0} (# (Σ n, L n)) ≤ θ ∧
  ∀ M, K.objects M → ∀ A : ZFSet.{u}, A ⊆ M.carrier →
    ∃ N, K.objects N ∧ K.strong N M ∧ A ⊆ N.carrier ∧ N.carrier.card ≤ A.card + θ

def HasLSNumber (θ : Cardinal.{u}) : Prop :=
  K.LSBound θ ∧ ∀ θ', K.LSBound θ' → θ ≤ θ'

structure IsAEC : Prop where
  strong_objects : ∀ {M N}, K.strong M N → K.objects M ∧ K.objects N
  refl : ∀ {M}, K.objects M → K.strong M M
  antisymm : ∀ {M N}, K.strong M N → K.strong N M → M = N
  trans : ∀ {M N P}, K.strong M N → K.strong N P → K.strong M P
  substructure : ∀ {M N}, K.strong M N → M.IsSubstructure N
  iso_objects : ∀ {M N}, K.objects M → Nonempty (M.Iso N) → K.objects N
  iso_strong : ∀ {M N M' N'} (h : K.strong M N)
    (e : M.Iso M') (f : N.Iso N'),
    (∀ x : M.carrier,
      (e.toEquiv x).val =
        (f.toEquiv ⟨x.val, (substructure h).subset x.property⟩).val) →
    K.strong M' N'
  coherence : ∀ {M₀ M₁ M₂}, M₀.IsSubstructure M₁ →
    K.strong M₀ M₂ → K.strong M₁ M₂ → K.strong M₀ M₁
  chain_union : ∀ (γ : Ordinal.{u}), γ ≠ 0 →
    ∀ (F : γ.ToType → RelModel.{u} L),
    (∀ i, K.objects (F i)) →
    (∀ i j, i ≤ j → K.strong (F i) (F j)) →
    ∃ U, K.objects U ∧ RelModel.IsUnion F U ∧
      (∀ i, K.strong (F i) U) ∧
      (∀ N, K.objects N → (∀ i, K.strong (F i) N) → K.strong U N)
  downward : ∃ θ, K.LSBound θ

def Categorical (μ : Cardinal.{u}) : Prop :=
  (∃ M, K.objects M ∧ M.carrier.card = μ) ∧
  ∀ M N, K.objects M → K.objects N →
    M.carrier.card = μ → N.carrier.card = μ → Nonempty (M.Iso N)

def TwoModels (μ : Cardinal.{u}) : Prop :=
  ∃ M N, K.objects M ∧ K.objects N ∧
    M.carrier.card = μ ∧ N.carrier.card = μ ∧ ¬ Nonempty (M.Iso N)

end ClassData

def CH : Prop := (2 : Cardinal.{u}) ^ ℵ₀ = ℵ_ 1

def hanf (κ : Cardinal.{u}) : Cardinal.{u} := beth (succ ((2 : Cardinal.{u}) ^ κ)).ord

def endpoint : Cardinal.{u} := beth (ω_ 2)

def tailThreshold : Cardinal.{u} := beth (succ ((2 : Cardinal.{u}) ^ (ℵ_ 1))).ord

theorem main (hCH : CH.{u}) :
    ∃ (L : ℕ → Type), Countable (Σ n, L n) ∧
      ∃ K : ClassData.{u} L, K.IsAEC ∧ K.HasLSNumber ℵ₀ ∧
        endpoint = hanf (ℵ₀ : Cardinal.{u}) ∧ K.TwoModels endpoint ∧
        ∀ μ, tailThreshold ≤ μ → K.Categorical μ := by
  sorry

end CHObstruction

end

end OAI
