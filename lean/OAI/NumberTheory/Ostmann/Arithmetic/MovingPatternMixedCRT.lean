import OAI.NumberTheory.Ostmann.Arithmetic.MovingSeparatedAverages
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternArithmeticComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternPrimeObservable

namespace OAI

/-! # Identifying the actual mixed-giant pattern with its corrected CRT mean -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- Each equality class contributes exactly one prime-square factor. -/
theorem movingPatternHaarProduct_eq_image {A B C : Type*} [Fintype C] {N n : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List B) n)
    (pattern : Bool × MovingSampleIndex n → C) (x : Fin (N + 1) → A)
    (P : Finset ℕ) [∀ p : P, Fact p.val.Prime]
    (hP : P = Finset.univ.image (fun c : C => prime (x (e.symm (.inr c)))))
    (hinj : Function.Injective (fun c : C => prime (x (e.symm (.inr c))))) :
    movingPatternHaarProduct e prime hprime n t small bulk pattern x =
      ∏ p : P, movingInternalHaarAverage (fun i => prime (x i))
        (movingPatternFinData e n t small bulk pattern) p.val := by
  let f : C → P := fun c => ⟨prime (x (e.symm (.inr c))), by
    rw [hP]
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact hinj (congrArg Subtype.val hab)
    · intro p
      have hp : p.val ∈ Finset.univ.image (fun c : C => prime (x (e.symm (.inr c)))) := by
        simpa only [hP] using p.property
      obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hp
      exact ⟨c, Subtype.ext hc⟩
  let T := movingPatternFinData e n t small bulk pattern
  let : ∀ c : C, Fact (prime (x (e.symm (.inr c)))).Prime := fun _ => ⟨hprime _⟩
  change (∏ c : C, movingInternalHaarAverage (fun i => prime (x i)) T
    (prime (x (e.symm (.inr c))))) = _
  exact Fintype.prod_equiv (Equiv.ofBijective f hf) _ _ (fun _ => rfl)

section
variable {B C I : Type*} [Fintype C] [Fintype I] {N n m : ℕ}
  (e : Fin (N + 1) ≃ B ⊕ C) (t : Bool → FrequencyTree ℤ n)
  (small : Bool → TreeLeafTuple (List B) n) (slot : (TreeLeafIndex n × Fin m) ↪ B)
  (perm : Equiv.Perm (TreeLeafIndex n × Fin m)) (pattern : Bool × MovingSampleIndex n → C)
  (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime)
  (childBound pivotBound : ℕ → ℕ)
  (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), s ≠ 0)
  (F : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData (Fin (N + 1)) k → ℤ → ℤ → ℤ → ℝ)
  (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
  (p : I → ℕ) [∀ i, Fact (p i).Prime] (g : ∀ i, ZMod (p i) → ℂ)
  (twist : ∀ i, Bool → (ZMod (p i))ˣ) (input : PublishedProgressionInput) (Q : ℕ)
  (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
  (φ : ℝ → ℝ) (G : ℕ → ℝ)

/-- The original mixed-prime observable, including its internal Haar factors,
is the corrected mean of the separated residue coefficient. -/
theorem movingPatternPrimeObservable_crt (x : Fin (N + 1) → primes)
    (P : Finset ℕ) [∀ q : P, Fact q.val.Prime]
    [∀ b, NeZero (movingArithmeticModuli r p P Finset.univ b)]
    [NeZero (∏ b, movingArithmeticModuli r p P Finset.univ b)]
    (hP : P = Finset.univ.image (fun c : C => (x (e.symm (.inr c)) : ℕ)))
    (hinj : Function.Injective (fun c : C => (x (e.symm (.inr c)) : ℕ)))
    (hR : ∀ b, (movingPatternFinBulkData e n m t small slot perm pattern b).frequencyProduct ∣ R)
    (hprecision : R ^ (n + 1) ∣ (r : ℤ))
    (hcover : ∀ b, ∀ o ∈ (movingPatternFinBulkData e n m t small slot perm pattern b).occurrences,
      ∀ i ∈ o.current.compensationSlots, (x i : ℕ) ∈ P)
    (hc : Pairwise (fun b c => (movingArithmeticModuli r p P Finset.univ b).Coprime
      (movingArithmeticModuli r p P Finset.univ c)))
    (hpage : pageAtModulus (∏ b, movingArithmeticModuli r p P Finset.univ b)
      (selectedPageZero input Q) = pageAtModulus r (selectedPageZero input Q)) (u v : ℝ) :
    let value := fun i => (x i : ℕ)
    let T := movingPatternFinBulkData e n m t small slot perm pattern
    let nodes := fun b => (T b).formulaNodes value
      (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound
      (movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq b)
      (.prime false) (.prime true)
    movingPatternPrimeObservable e t small slot perm pattern primes hprimes childBound pivotBound
      hfreq F E outside R r p g twist input Q v ψ X lo hi hlo hhi φ G (Real.exp u) (Real.exp v) x *
      movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
        n t small (movingPatternBulkLeaves n m slot perm) pattern x =
    movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp u) (Real.exp v) *
      correctedMixedPairAverage input Q (∏ b, movingArithmeticModuli r p P Finset.univ b)
        (movingSeparatedPairResidueCoefficient p value outside F E g (fun b i => twist i b)
          Finset.univ T nodes R) v := by
  dsimp only
  let value := fun i => (x i : ℕ)
  let T := movingPatternFinBulkData e n m t small slot perm pattern
  let hf := movingPatternFinBulkData_frequencies e t small slot perm pattern (· ≠ 0) hfreq
  let nodes := fun b => (T b).formulaNodes value
    (fun i => (hprimes _ (x i).property).ne_zero) childBound pivotBound (hf b)
    (.prime false) (.prime true)
  have h := movingSeparatedPairResidueCoefficient_page_factorization p value outside F E g
    (fun b i => twist i b) T nodes R r P Finset.univ hf hR hprecision hcover hc input Q hpage v
  have hspec : (∏ i : (Finset.univ : Finset I),
      movingSpectatorHaarAverage value (p i.val) (g i.val) (fun b => twist i.val b) T) =
      ∏ i : I, movingSpectatorHaarAverage value (p i) (g i) (twist i) T := by
    exact Finset.prod_coe_sort Finset.univ
      (fun i => movingSpectatorHaarAverage value (p i) (g i) (twist i) T)
  rw [hspec] at h
  rw [h, movingPatternHaarProduct_eq_image e (fun q : primes => (q : ℕ))
    (fun q => hprimes _ q.property) t small (movingPatternBulkLeaves n m slot perm) pattern x P hP hinj]
  unfold movingPatternPrimeObservable
  let K := movingRealKernelPair value T nodes ψ X lo hi hlo hhi φ G (Real.exp u) (Real.exp v)
  let A := movingFrequencyPageAverage value outside F E T nodes R r input Q v
  let S := ∏ i, movingSpectatorHaarAverage value (p i) (g i) (twist i) T
  let H := ∏ q : P, movingInternalHaarAverage value T q.val
  change (K * (A * S)) * H = K * ((A * H) * S)
  ring

end
end Ostmann

end OAI
