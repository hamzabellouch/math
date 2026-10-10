import OAI.NumberTheory.Ostmann.Arithmetic.MovingSelectedDiagonalEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSelectedGoodCorrelation
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalSymmetrization

namespace OAI

/-! # Full bulk symmetrization under the actual selected harmonic priors -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_symmetrized_energy
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (hk : 0 < k) (hn : n + 2 ≤ k)
    (A Wwin Bφ Dφ c K εdiag gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let Cprior := K + 1
      ∀ (B : Type) [Fintype B] (tierB : B → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (small : TreeLeafTuple (List B) (n + 2)) (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ B)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : B → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center : ℝ),
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
      Monotone V → f 0 = 0 →
      (∀ s, ‖f s‖ ≤ if s.natAbs ≤ V 0 then 1 else 0) →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V (n + 2) : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ i ∈ flattenMovingSlots (n + 2) small, i ∉ Set.range slot) →
      (∀ i, (n + 2) ≤ tierB i) → MovingLeafLengthLE (n + 2) small r₀ →
      1 ≤ m → (∀ i, primeCutoff ≤ p i) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      (∀ x, 0 ≤ φ x) → (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) → S ⊆ primes →
      ((global.card + (Fintype.card B + 4 * (n + 2) * 2 ^ (n + 2)) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (∀ j, j < (n + 2) → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
      (∀ j (q : primes), (q : ℕ) ∈ Qν j → tier q = tierB j) →
      V (n + 2) ≤ primeLo → V (n + 2) < cutoff → cutoff ≤ primeLo →
      (primeLo : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
      (∀ a : primes, (a : ℝ) ≤ Real.exp (Real.exp ((11 / 1000 : ℝ) * L))) →
      (∀ i, cutoff ≤ p i ∧ p i ≤ primeLo) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qμ j) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ z, selectedPageZero P (giantProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ j, q ∉ Qν j) →
      (∀ z, selectedPageZero P (bulkProgressionCutoff L) = some z → ∀ q,
        deletedConductorPrime z.modulus cutoff = some q → ∀ i, p i ≠ q) →
      (∀ q, q.Prime → (setsReg q).Nonempty ∧ (setsReg q).card < q) →
      (movingOriginalSymmetrizedEnergy p (fun q : primes => (q : ℕ)) outside μ ν
        childBound pivotBound V f (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ
        ψ X (Real.exp Δ) hi φ G (n + 2) m small slot
        (normalizedResidueFamily setsReg) Jleft Jright diagonal uG vG rG sG center).re ≤
      (((2 ^ (n + 2) + 1) * (2 ^ (n + 2)) ^ (2 * 2 ^ (n + 2)) : ℕ) : ℝ) *
        Real.exp ((2 ^ (n + 2) : ℝ) * m *
          (-(3 / 4 : ℝ) * Real.log (2 ^ (n + 2) : ℕ) + 5 / 4)) *
        (Real.exp ((2 ^ (n + 2) : ℕ) * Δ +
          (Real.log 12 + 1) * (2 ^ (n + 2) : ℕ) * m + εdiag * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
        Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, hgood⟩ :=
    P.moving_selected_good_correlation C hM ψ n r₀ k hk A Wwin Bφ Dφ c K gain
      hA hWwin hBφ hDφ hc hK
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [hgood, P.moving_selected_diagonal_energy C hM ψ (n + 2) r₀ k hk hn
    A Wwin Bφ Dφ c K εdiag hA hWwin hBφ hDφ hc hK hεdiag hdepth] with L hg hd
  dsimp only at hg hd ⊢
  intro B _ tierB primes hprimes _ childBound pivotBound V f outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G small slot global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center
    hV hf0 hf hcard hVn hV0 hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hsmall hB hsmallLen
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange houtcover hinjp huBig hrBig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  have hfnorm (s : ℤ) : ‖f s‖ ≤ 1 := (hf s).trans (by split_ifs <;> norm_num)
  have hdiagonal := hd B tierB primes hprimes childBound pivotBound V f outside p Dq sets
    primeLo cutoff tier X Δ hi φ G small slot global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center
    hV hf0 hf hcard hVn hV0 hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hsmall hB hsmallLen
    (by omega) (fun i => hpc.trans (hp i)) hsets hsetsp hpupper hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange houtcover hinjp huBig hrBig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hsetsReg
  have hpairs (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin (spectatorBulkCount k L)))
      (hperm : 4 * Fintype.card (arrangementGraph (spectatorBulkCount k L) perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2))) :=
    hg B tierB primes hprimes childBound pivotBound V f outside p Dq sets β
      primeLo cutoff tier X Δ hi φ G small slot perm global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center
      hV hf0 hfnorm hcard hVn hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hsmall hB hsmallLen
      hm hp hsets hsetsp hpupper hperm hdlo hdhi hβ hbias hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
      hμrange hνrange houtcover hinjp huBig hrBig hμtier hνtier hNlo hNcut hcutlo hloReal
      hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  have hidentical (j l) : primeSubsetPrior primes (Qν (slot j)) =
      primeSubsetPrior primes (Qν (slot l)) := by rw [hν j, hν l]
  have h := movingOriginalSymmetrizedEnergy_bound p (fun q : primes => (q : ℕ)) outside
    (fun j => primeSubsetPrior primes (Qμ j)) (fun j => primeSubsetPrior primes (Qν j))
    childBound pivotBound V f (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ
    ψ X (Real.exp Δ) hi φ hφpos G (n + 2) (spectatorBulkCount k L) hm small slot hsmall
    (fun j q => primeSubsetPrior_nonneg primes (Qν j) q) hidentical
    (normalizedResidueFamily setsReg) Jleft Jright diagonal uG vG rG sG center _ _
    (by positivity) (by positivity) hdiagonal hpairs
  simpa only [add_assoc] using h

end Ostmann

end OAI
