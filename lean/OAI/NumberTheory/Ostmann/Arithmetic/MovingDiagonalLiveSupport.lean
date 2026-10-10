import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeLiveSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeTerms
import OAI.NumberTheory.Ostmann.Construction.SupportedAlphabetSum

namespace OAI

/-! # The literal diagonal is unchanged on removing zero-weight giant labels -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem pivotDiagonal_embedding_support {A B : Type*} [Fintype A] [Fintype B]
    (e : B ↪ A) (L : A → ℕ) (v : A → ℤ) (c : A → ℂ)
    (hc : ∀ a, a ∉ Set.range e → c a = 0) :
    pivotDiagonal L v c = pivotDiagonal (L ∘ e) (v ∘ e) (c ∘ e) := by
  unfold pivotDiagonal
  rw [finite_sum_embedding_support e _ (fun a ha => by simp only [hc a ha, zero_mul, ite_self, Finset.sum_const_zero])]
  apply Finset.sum_congr rfl
  intro a _
  exact finite_sum_embedding_support e _ (fun b hb => by simp only [hc b hb, map_zero, mul_zero, ite_self])

theorem smoothGiantPrior_live_embed (P : Finset ℕ) (φ : ℝ → ℝ) (H : ℝ)
    (p : smoothGiantLivePrimes P φ H) :
    smoothGiantPrior (smoothGiantLivePrimes P φ H) φ H p =
      smoothGiantPrior P φ H ⟨p, smoothGiantLivePrimes_subset P φ H p.property⟩ := by
  simp only [smoothGiantPrior, smoothGiantLogNormalizer, smoothGiantMass_live]

theorem movingAmplitudeDiagonal_live {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (P I : Finset ℕ) (H : ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) :
    movingAmplitudeDiagonal value outside μ childBound pivotBound V F φ G n r m P I
      (smoothGiantPrior P φ H) ν greg ggiant favorable =
    movingAmplitudeDiagonal value outside μ childBound pivotBound V F φ G n r m
      (smoothGiantLivePrimes P φ H) I (smoothGiantPrior (smoothGiantLivePrimes P φ H) φ H)
      ν greg ggiant favorable := by
  let e : MovingAmplitudeIndex σ (smoothGiantLivePrimes P φ H) n r m V ↪
      MovingAmplitudeIndex σ P n r m V :=
    ⟨fun a => (⟨a.1, smoothGiantLivePrimes_subset P φ H a.1.property⟩, a.2), by
      intro a b hab
      rcases a with ⟨a, a'⟩
      rcases b with ⟨b, b'⟩
      have hfirst : a = b := Subtype.ext (congrArg (fun z => (z.1 : ℕ)) hab)
      have hsecond : a' = b' := congrArg Prod.snd hab
      cases hfirst
      cases hsecond
      rfl⟩
  unfold movingAmplitudeDiagonal
  dsimp only
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  congr 2
  have hsupport (a : MovingAmplitudeIndex σ P n r m V) (ha : a ∉ Set.range e) :
      smoothGiantPrior P φ H a.1 = 0 := by
    have hp : (a.1 : ℕ) ∉ smoothGiantLivePrimes P φ H := by
      intro hp
      apply ha
      refine ⟨(⟨a.1, hp⟩, a.2), ?_⟩
      rfl
    have hz : φ (Real.log (a.1 : ℕ) - H) = 0 := by
      by_contra hn
      exact hp (Finset.mem_filter.mpr ⟨a.1.property, hn⟩)
    simp only [smoothGiantPrior, hz, mul_zero, zero_div]
  rw [pivotDiagonal_embedding_support e _ _ _ (fun a ha => by
    simp only [movingTemplateTransferWeight, movingAmplitudePrior, hsupport a ha,
      zero_mul, Complex.ofReal_zero])]
  apply congrArg (pivotDiagonal _ _)
  funext a
  have heval (b : MovingAmplitudeIndex σ (smoothGiantLivePrimes P φ H) n r m V) :
      e b = (⟨b.1, smoothGiantLivePrimes_subset P φ H b.1.property⟩, b.2) := rfl
  simp only [Function.comp_apply, heval, movingTemplateTransferWeight,
    movingAmplitudePrior, smoothGiantPrior_live_embed]

end Ostmann

end OAI
