import OAI.NumberTheory.Ostmann.Construction.FiniteTailSpectators
import OAI.NumberTheory.Ostmann.Construction.TailSieveMasks
import OAI.NumberTheory.Ostmann.Arithmetic.MovingModulusAssembly

namespace OAI

/-! # The actual spectator data used in the arithmetic comparisons -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- Every field refers to the same selected prime family and the original
tail masks. The tolerance is available both for Fourier factors and for all
translated nonprincipal characters. -/
structure TailSpectatorFamily (A : Set ℕ) (N k : ℕ) (L ε : ℝ)
    (cutoff : ℕ) (deleted : Finset ℕ) where
  prime : Fin (spectatorBulkCount k L) → ℕ
  injective : Function.Injective prime
  isPrime : ∀ i, (prime i).Prime
  ge_three : ∀ i, 3 ≤ prime i
  ge_cutoff : ∀ i, cutoff ≤ prime i
  avoids : ∀ i, prime i ∉ deleted
  lower : ∀ i, Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) ≤ prime i
  upper : ∀ i, (prime i : ℝ) ≤ Real.exp (Real.exp ((6 / 10000 : ℝ) * L))
  balanced_lower : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N (prime i))
  balanced_upper : ∀ i, residueDensity (tailDensityMask A N (prime i)) ≤ 2 / 3
  nonempty : ∀ i, (tailDensityMask A N (prime i)).Nonempty
  proper : ∀ i, (tailDensityMask A N (prime i)).card < prime i
  character_bound : ∀ i (χ : DirichletCharacter ℂ (prime i)), χ ≠ 1 →
    ∀ a : ZMod (prime i),
      ‖((tailDensityMask A N (prime i)).card : ℂ)⁻¹ *
        ∑ x ∈ tailDensityMask A N (prime i), χ⁻¹ (-a - x)‖ ≤ ε / 2
  mixed_bound : ∀ i,
    @MixedFourierBound (prime i) ⟨isPrime i⟩
      (@normalizedResidueTransform (prime i) ⟨(isPrime i).ne_zero⟩
        (tailDensityMask A N (prime i))) ε

theorem EventuallyPrimeSumset.tail_spectator_family
    (hBonami : PublishedBonamiBound) (P0 : PublishedProgressionInput)
    (H : PublishedRealZeroInput P0) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {C : ℝ} (hM : MertensEstimate C)
    {A B : Set ℕ} (h : EventuallyPrimeSumset A B) (hA : A.Infinite) (hB : B.Infinite)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (k cutoff : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ D : Finset ℕ, (D.card : ℝ) ≤ Real.exp L →
      Nonempty (TailSpectatorFamily A N k L ε cutoff D) := by
  filter_upwards [h.finite_tail_spectators hBonami P0 H hSiegel sieve hsize hM
    hA hB N hN k (max 3 cutoff) ε hε] with L hL D hD
  obtain ⟨p, hinj, hp⟩ := hL D hD
  have hprime (i) := (hp i).1
  have hthree (i) : 3 ≤ p i := (le_max_left _ _).trans (hp i).2.1
  have hne (i) : p i ≠ 2 := by have := hthree i; omega
  refine ⟨{
    prime := p
    injective := hinj
    isPrime := hprime
    ge_three := hthree
    ge_cutoff := fun i => (le_max_right _ _).trans (hp i).2.1
    avoids := fun i => (hp i).2.2.1
    lower := fun i => (hp i).2.2.2.1
    upper := fun i => (hp i).2.2.2.2.1
    balanced_lower := fun i => (hp i).2.2.2.2.2.1
    balanced_upper := fun i => (hp i).2.2.2.2.2.2.1
    nonempty := fun i => tailDensityMask_nonempty hA N (p i) (hprime i).pos
    proper := ?_
    character_bound := ?_
    mixed_bound := fun i => (hp i).2.2.2.2.2.2.2.2 (hprime i)
  }⟩
  · intro i
    let : NeZero (p i) := ⟨(hprime i).ne_zero⟩
    exact tailDensityMask_card_lt hB N (p i) (hprime i).pos (hN _ (hprime i))
  · intro i χ hχ a
    let : Fact (p i).Prime := ⟨hprime i⟩
    exact (tailDensityMask_reverse_character_mean_bound A N (p i) (hne i) χ hχ a).trans
      (hp i).2.2.2.2.2.2.2.1

theorem TailSpectatorFamily.comparison_upper {A : Set ℕ} {N k cutoff : ℕ}
    {L ε : ℝ} {D : Finset ℕ} (F : TailSpectatorFamily A N k L ε cutoff D)
    (hL : 0 ≤ L) (i) :
    (F.prime i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L)) :=
  (F.upper i).trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith only [hL])))

/-- The same selected spectators work for every bounded frequency array;
the modulus and its coprimality are derived from the actual array. -/
theorem eventual_tail_spectator_moduli (n k : ℕ) (Aexp : ℝ) (hAexp : 0 ≤ Aexp) :
    ∀ᶠ L : ℝ in atTop, ∀ (A : Set ℕ) (N cutoff : ℕ) (ε : ℝ) (D : Finset ℕ)
      (F : TailSpectatorFamily A N k L ε cutoff D)
      (σ : Type) (T : Bool → MovingSlotData σ n) (bound : ℕ),
      (∀ b, (T b).Frequencies (· ≠ 0)) →
      (∀ b, (T b).Frequencies (fun s => s.natAbs ≤ bound)) →
      (bound : ℝ) ≤ Real.exp (Aexp * spectatorBulkCount k L) →
      let r := movingPairFrequencyModulus T
      let M := ∏ i, bulkResidueModuli r F.prime i
      0 < r ∧
      (∀ b, (T b).frequencyProduct ∣ movingPairFrequencyBase T) ∧
      movingPairFrequencyBase T ^ (n + 1) ∣ (r : ℤ) ∧
      Pairwise (fun i j => (bulkResidueModuli r F.prime i).Coprime
        (bulkResidueModuli r F.prime j)) ∧
      0 < M ∧ M ≤ bulkProgressionCutoff L ∧
      (∀ u : ℝ, Real.exp ((39 / 10000 : ℝ) * L) ≤ u → (M : ℝ) ≤ Real.exp u) := by
  filter_upwards [moving_pair_modulus_range n k Aexp (4 / 10000) hAexp (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with L hL hL0 A N cutoff ε D F σ T bound hT hbound hexp
  exact hL σ T bound F.prime hT hbound hexp F.isPrime F.injective F.lower
    (F.comparison_upper hL0)

end Ostmann

end OAI
