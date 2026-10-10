import OAI.NumberTheory.Ostmann.Construction.InitialMovingData

namespace OAI

/-! # Exact original kernel at level zero of the moving iteration -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem initial_moving_kernel (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (hP : ∀ p ∈ P, p.Prime) (b d r : ℕ) (cb cd : ℝ)
    (sl sr : Fin d → P) (hdistinct : Function.Injective (Fin.append sl sr))
    (fallback XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P)
    (S : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (hXL : V 0 < (XL : ℕ)) (hXR : V 0 < (XR : ℕ))
    (hwindow : initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd sl sr y ≠ 0 →
      ((∏ i, ((initialMovingTuple b d r sl sr XL XR y i : P) : ℕ) : ℕ) : ℝ) / X ∈
        Set.Icc lo hi) :
    let q : Fin (d + d) → ℕ := fun i => ((Fin.append sl sr i : P) : ℕ)
    let hc : Pairwise (fun i j => (q i).Coprime (q j)) := fun i j hij =>
      (Nat.coprime_primes (hP _ (Fin.append sl sr i).property)
        (hP _ (Fin.append sl sr j).property)).mpr (fun h => hij (hdistinct (Subtype.ext h)))
    let _ : ∀ i, Fact (q i).Prime := fun i => ⟨hP _ (Fin.append sl sr i).property⟩
    let F := movingOriginalLeaf (fun p : P => (p : ℕ)) q
      (initialMovingDataCutoff (fun p : P => (p : ℕ)) b d r cb cd sl sr fallback)
      (fun i => normalizedResidueFamily S (q i)) (initialSpectatorCofactor q hc) Finset.univ
      (𝓕 ψ) (X / (∏ i, q i : ℕ)) lo hi
    initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd sl sr y *
      (if Function.Injective (initialMovingTuple b d r sl sr XL XR y) then
        primeTupleFourierCoefficient P
          (Fin.append (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p))
            (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p)))
          ψ X (V 0) (initialMovingTuple b d r sl sr XL XR y) else 0) =
    ∑ s ∈ transferFrequencyRange (V 0),
      movingTemplateCoefficient (fun p : P => (p : ℕ)) (List.ofFn q) μ childBound pivotBound V
        F φ G 0 (r + r) (b + b) s y XL XR *
      movingTaggedTransform
        (Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (fun i => (y i : ℕ)))
        (Sum.elim (fun _ => true) (fun _ => false))
        (normalizedResidueFamily S) (normalizedResidueFamily S) fav (∏ i, q i) s := by
  intro q hc inst F
  have : ∀ i, Fact (q i).Prime := inst
  let W := initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd sl sr y
  let M := (XL : ℕ) * (XR : ℕ) * ∏ i, (y i : ℕ)
  let T := fun s : ℤ => movingTaggedTransform
    (Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (fun i => (y i : ℕ)))
    (Sum.elim (fun _ => true) (fun _ => false))
    (normalizedResidueFamily S) (normalizedResidueFamily S) fav (∏ i, q i) s
  have hwin : W ≠ 0 → (M : ℝ) / (X / (∏ i, q i : ℕ)) ∈ Set.Icc lo hi := by
    intro hw
    have hh := hwindow hw
    rw [initialMovingTuple_scale] at hh
    exact hh
  have hpoint (s : ℤ) (hs : s ∈ transferFrequencyRange (V 0)) :
      movingTemplateCoefficient (fun p : P => (p : ℕ)) (List.ofFn q) μ childBound pivotBound V
        F φ G 0 (r + r) (b + b) s y XL XR * T s =
      W * (if Function.Injective (initialMovingTuple b d r sl sr XL XR y) then
        normalizedFourierProfile (fun t => 𝓕 ψ t) s ((M : ℝ) / (X / (∏ i, q i : ℕ))) *
          (∏ i, spectatorHistoryLeaf (fun _ : Unit => M) (normalizedResidueFamily S (q i))
            (initialSpectatorCofactor q hc i) () s) * T s else 0) := by
    by_cases hs0 : s = 0
    · subst s
      have ht : T 0 = 0 := initial_moving_tagged_zero P b r S fav XL XR y _
      rw [ht]
      split_ifs <;> simp only [mul_zero]
    · have hsV := (mem_transferFrequencyRange (V 0) s).mp hs
      rw [movingTemplateCoefficient_initial_supported P hP b d r sl sr μ childBound pivotBound V
        F φ G XL XR y s hs0 (hsV.trans_lt hXL) (hsV.trans_lt hXR)]
      have hv := initialMovingLeaf_value P b d r cb cd sl sr fallback XL XR y s hs0
        q (fun i => normalizedResidueFamily S (q i)) (initialSpectatorCofactor q hc) ψ
        (X / (∏ i, q i : ℕ)) lo hi hwin
      change F (initialMovingState P b r XL XR y s) s = _ at hv
      rw [hv]
      split_ifs <;> ring
  by_cases hx : Function.Injective (initialMovingTuple b d r sl sr XL XR y)
  · simp only [hx, ite_true]
    rw [initial_moving_coefficient P hP b d r S fav sl sr hdistinct XL XR y ψ X (V 0)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    simpa only [hx, ite_true] using (hpoint s hs).symm
  · simp only [hx, ite_false, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro s hs
    simpa only [hx, ite_false, mul_zero] using hpoint s hs

end Ostmann

end OAI
