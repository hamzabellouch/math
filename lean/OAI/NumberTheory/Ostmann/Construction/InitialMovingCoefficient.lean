import OAI.NumberTheory.Ostmann.Construction.InitialMovingTests
import OAI.NumberTheory.Ostmann.Construction.InitialMovingAverage

namespace OAI

/-! # The original Fourier coefficient after fixing the actual spectator list -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

/-- Freezing spectators changes the Fourier scale by their exact product. -/
theorem initialMovingTuple_scale (P : Finset ℕ) (b d r : ℕ)
    (sl sr : Fin d → P) (XL XR : P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) (X : ℝ) :
    ((∏ i, ((initialMovingTuple b d r sl sr XL XR y i : P) : ℕ) : ℕ) : ℝ) / X =
      ((XL : ℕ) * (XR : ℕ) * (∏ i, (y i : ℕ)) : ℕ) /
        (X / ((∏ i, ((Fin.append sl sr i : P) : ℕ)) : ℕ)) := by
  rw [initialMovingTuple_product, Nat.cast_mul, div_div_eq_mul_div]
  ring

/-- Distinct original spectators give precisely the cofactor units used by
all later histories. Their transforms and the retained phase transform factor
without changing the original Fourier weight. -/
theorem initial_moving_coefficient (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (hP : ∀ p ∈ P, p.Prime) (b d r : ℕ)
    (S : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool)
    (sl sr : Fin d → P) (hdistinct : Function.Injective (Fin.append sl sr))
    (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (V : ℕ) :
    let q : Fin (d + d) → ℕ := fun i => ((Fin.append sl sr i : P) : ℕ)
    let hc : Pairwise (fun i j => (q i).Coprime (q j)) := fun i j hij =>
      (Nat.coprime_primes (hP _ (Fin.append sl sr i).property)
        (hP _ (Fin.append sl sr j).property)).mpr
          (fun h => hij (hdistinct (Subtype.ext h)))
    let M := (XL : ℕ) * (XR : ℕ) * ∏ i, (y i : ℕ)
    let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (Fin.append sl sr i).property⟩
    primeTupleFourierCoefficient P
      (Fin.append (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p))
        (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p)))
      ψ X V (initialMovingTuple b d r sl sr XL XR y) =
    ∑ s ∈ transferFrequencyRange V,
      normalizedFourierProfile (fun t => 𝓕 ψ t) s ((M : ℝ) / (X / (∏ i, q i : ℕ))) *
        (∏ i, spectatorHistoryLeaf (fun _ : Unit => M) (normalizedResidueFamily S (q i))
          (initialSpectatorCofactor q hc i) () s) *
        movingTaggedTransform
          (Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (fun i => (y i : ℕ)))
          (Sum.elim (fun _ => true) (fun _ => false))
          (normalizedResidueFamily S) (normalizedResidueFamily S) fav (∏ i, q i) s := by
  intro q hc M
  have : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (Fin.append sl sr i).property⟩
  unfold primeTupleFourierCoefficient
  apply Finset.sum_congr rfl
  intro s _
  rw [initialMovingTuple_scale]
  have hp : (∏ i, Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ))
      (fun i => (y i : ℕ)) i) = M := by
    simp only [Fintype.prod_sum_type, Fintype.prod_bool, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true,
      ite_false, ite_true]
    rfl
  have ht := initial_moving_transform P b d r S fav sl sr XL XR y s
  dsimp only at ht
  rw [hp] at ht
  change _ = movingRegularTransform q (fun i => normalizedResidueFamily S (q i)) M s * _ at ht
  rw [initial_spectator_transform q hc] at ht
  rw [ht]
  dsimp only [M, q]
  simp only [mul_assoc]

end Ostmann

end OAI
