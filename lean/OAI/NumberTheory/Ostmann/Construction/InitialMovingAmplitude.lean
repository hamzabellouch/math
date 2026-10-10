import OAI.NumberTheory.Ostmann.Construction.InitialMovingKernel
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateAmplitude

namespace OAI

namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

theorem initial_frozen_moving_amplitude (P : Finset ℕ) [∀ p : P, NeZero (p : ℕ)]
    (hP : ∀ p ∈ P, p.Prime) (b d r : ℕ) (cb cd : ℝ)
    (sl sr : Fin d → P) (hdistinct : Function.Injective (Fin.append sl sr)) (fallback : P)
    (μg : P → ℝ) (μb : Fin b → P → ℝ) (μc : Fin r → P → ℝ)
    (S : ∀ q : ℕ, Finset (ZMod q)) (fav : ℕ → Bool)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (μ : ℕ → P → ℝ) (childBound pivotBound V : ℕ → ℕ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (hlarge : ∀ p : P, μg p ≠ 0 → V 0 < (p : ℕ))
    (hwindow : ∀ (XL XR : P) (y : MovingRegularSlot 0 (r + r) (b + b) → P),
      μg XL ≠ 0 → μg XR ≠ 0 →
      (∏ i, initialMovingRegularPrior b r μb μc i (y i)) ≠ 0 →
      initialMovingCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd sl sr y ≠ 0 →
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
    initialFrozenAmplitude P b d r μg μb μc
      (Fin.append (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p))
        (primeHalfTests (n := b + (d + r)) P (fun p => S p) (fun p => fav p)))
      ψ X (V 0)
      (doubledHalfWeight (fun x : Fin (b + (d + r) + 1) → P =>
        (initialHalfCutoffWeight (fun p : P => (p : ℕ)) b d r cb cd (Fin.tail x) : ℂ))) sl sr =
    movingTemplatePrimeAmplitude (fun p : P => (p : ℕ)) (List.ofFn q) μ childBound pivotBound V
      F φ G 0 (r + r) (b + b) P μg (initialMovingRegularPrior b r μb μc)
      (normalizedResidueFamily S) (normalizedResidueFamily S) fav := by
  intro q hc inst F
  have : ∀ i, Fact (q i).Prime := inst
  rw [initialFrozenAmplitude_moving]
  unfold movingTemplatePrimeAmplitude
  apply Finset.sum_congr rfl
  intro XL _
  by_cases hXL : μg XL = 0
  · simp only [hXL, Complex.ofReal_zero, zero_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro XR _
  by_cases hXR : μg XR = 0
  · simp only [hXR, Complex.ofReal_zero, zero_mul]
  congr 1
  have hsum := Finset.sum_coe_sort (transferFrequencyRange (V 0)) (fun s : ℤ =>
    ∑ y : MovingRegularSlot 0 (r + r) (b + b) → P,
      ((∏ i, initialMovingRegularPrior b r μb μc i (y i) : ℝ) : ℂ) *
        (movingTemplateCoefficient (fun p : P => (p : ℕ)) (List.ofFn q)
          μ childBound pivotBound V F φ G 0 (r + r) (b + b) s y XL XR *
          movingTaggedTransform
            (Sum.elim (fun a : Bool => if a then (XL : ℕ) else (XR : ℕ)) (fun i => (y i : ℕ)))
            (Sum.elim (fun _ => true) (fun _ => false))
            (normalizedResidueFamily S) (normalizedResidueFamily S) fav (List.ofFn q).prod s))
  simp only [finite_univ_canonical, Function.comp_def] at hsum ⊢
  rw [hsum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : (∏ i, initialMovingRegularPrior b r μb μc i (y i)) = 0
  · simp only [finite_univ_canonical] at hy
    simp only [hy, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero]
  rw [← Finset.mul_sum]
  congr 1
  rw [initialMovingTuple_cutoff]
  simpa only [List.prod_ofFn, Function.comp_def] using
    initial_moving_kernel P hP b d r cb cd sl sr hdistinct fallback XL XR y S fav ψ X lo hi
      μ childBound pivotBound V φ G (hlarge XL hXL) (hlarge XR hXR) (hwindow XL XR y hXL hXR hy)

end Ostmann

end OAI
