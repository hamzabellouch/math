import OAI.NumberTheory.Ostmann.Arithmetic.MovingSelectedTemplateEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSelectedTemplateHalfLogGood
import OAI.NumberTheory.Ostmann.Construction.InitialMovingSymmetrizedEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompactEnergy

namespace OAI

/-! # Full bulk symmetrization under the actual selected harmonic priors -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_initial_symmetrized_energy
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (hk : 0 < k) (hn : n + 2 ≤ k)
    (A Wwin Bφ Dφ c K εdiag gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, ∀ b : ℕ, spectatorBulkCount k L = b + b →
      let m := b + b
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot (n + 2) r₀ m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (d r : ℕ) (sl sr : Fin d → primes) (fallback : primes)
        (childBound pivotBound V : ℕ → ℕ)
        (outside : List ℕ) (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (Dq : ∀ i, (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ)
        (primeLo cutoff : ℕ) (tier : primes → ℕ) (X Δ hi : ℝ)
        (φ : ℝ → ℝ) (G : ℕ → ℝ)
        (active : MovingRegularSlot (n + 2) r₀ m → Bool)
        (global : Finset ℕ) (Qμ : ℕ → Finset ℕ) (Qν : MovingRegularSlot (n + 2) r₀ m → Finset ℕ)
        (setsReg : ∀ q : ℕ, Finset (ZMod q))
        (Jleft Jright : ℝ) (diagonal : Bool) (uG vG rG sG center cb cd : ℝ),
      let slot := movingTemplateBulk (n + 2) r₀ m
      let μ := fun j => primeSubsetPrior primes (Qμ j)
      let ν := fun j => primeSubsetPrior primes (Qν j)
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let Sfreq := (transferFrequencyRange (V (n + 2))).erase 0
      r₀ + 4 * (n + 2) = r + r →
      Monotone V →
      (Sfreq.card : ℝ) ≤ Real.exp (A * m) →
      (V (n + 2) : ℝ) ≤ Real.exp (A * m) →
      (V 0 : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      0 ≤ Δ → Real.exp Δ ≤ hi → hi - Real.exp Δ ≤ Real.exp (Wwin * m) →
      1 ≤ uG → 1 ≤ rG → uG ≤ vG → rG ≤ sG → vG ≤ uG + 1 → sG ≤ rG + 1 → vG ≤ center + 1 →
      (∀ i, (n + 2) ≤ tierB i) →
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
      ((global.card + (Fintype.card (MovingRegularSlot (n + 2) r₀ m) + 4 * (n + 2) * 2 ^ (n + 2)) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cprior * L) →
      (∀ q ∈ outside, q.Prime) → (∀ j, Qν (slot j) = S \ global) →
      (∀ j, Qμ j ⊆ primes) → (∀ j, Qν j ⊆ primes) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qμ j, (q : ℝ)⁻¹) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Qν j, (q : ℝ)⁻¹) →
      (∀ j q, q ∈ Qμ j → Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j q, q ∈ Qν j → Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (q : ℝ)) →
      (∀ j, active (slot j) = true) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (∀ j, j < n + 2 → ∀ q : primes, (q : ℕ) ∈ Qμ j → tier q = j) →
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
      ‖movingTemplateMaskedSymmetrizedEnergy primes _hprimes outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p
          (initialMovingDataCutoff Subtype.val b d r cb cd sl sr fallback)
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G (n + 2) r₀ m ν active (normalizedResidueFamily setsReg)
        Jleft Jright diagonal uG vG rG sG center‖ ≤
      (((2 ^ (n + 2) + 1) * (2 ^ (n + 2)) ^ (2 * 2 ^ (n + 2)) : ℕ) : ℝ) *
        Real.exp ((2 ^ (n + 2) : ℝ) * m *
          (-(3 / 4 : ℝ) * Real.log (2 ^ (n + 2) : ℕ) + 5 / 4)) *
        (Real.exp ((2 ^ (n + 2) : ℕ) * Δ +
          (Real.log 12 + 1) * (2 ^ (n + 2) : ℕ) * m + εdiag * m) +
            5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L))) +
        Real.exp (-gain * m) + 5 * Real.exp (-Real.exp ((12 / 10000 : ℝ) * L)) := by
  obtain ⟨ε, hε, hε1, primeCutoff, hpc, hgood⟩ :=
    P.moving_selected_template_half_log_good_correlation C hM ψ n r₀ k hk A Wwin Bφ Dφ c K gain
      hA hWwin hBφ hDφ hc hK Dlog hDlog hloglip
      ((2 ^ (n + 2) + 2 ^ (n + 2)) + (2 ^ (n + 2) + 2 ^ (n + 2))) (by omega)
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [hgood, P.moving_selected_template_diagonal_energy C hM ψ (n + 2) r₀ k hk hn
    A Wwin Bφ Dφ c K εdiag hA hWwin hBφ hDφ hc hK hεdiag hdepth] with L hg hd
  intro b hsize
  rw [hsize] at hg hd
  dsimp only at hg hd ⊢
  intro tierB primes hprimes _ d r sl sr fallback childBound pivotBound V outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G active global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center cb cd
    hlen hV hcard hVn hV0 hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange hactive houtcover hinjp huBig hrBig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  let m := b + b
  let μ := fun j => primeSubsetPrior primes (Qμ j)
  let ν := fun j => primeSubsetPrior primes (Qν j)
  have hlocal := hμtier
  let f : ℤ → ℂ := fun s => if s = 0 then 0 else 1
  have hf0 : f 0 = 0 := by simp [f]
  have hfnorm (s : ℤ) : ‖f s‖ ≤ 1 := by simp only [f]; split_ifs <;> simp
  have hdiagonal := hd tierB primes hprimes childBound pivotBound V (movingCompactLeaf (V 0)) outside p Dq sets
    primeLo cutoff tier X Δ hi φ G active global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center
    hV (movingCompactLeaf_zero _) (movingCompactLeaf_norm _) hcard hVn hV0 hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hB
    (by omega) (fun i => hpc.trans (hp i)) hsets hsetsp hpupper hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange hactive houtcover hinjp huBig hrBig hlocal hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hsetsReg
  change ‖mixedExternalAverage ν (V (n + 2)) uG vG rG sG center
    (fun s y x z =>
      (‖movingTemplateCoefficient Subtype.val outside μ childBound pivotBound V
        (movingOriginalLeaf Subtype.val p (fun _ => movingCompactLeaf (V 0))
          (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi)
        φ G (n + 2) r₀ m s y ⌊Real.exp x⌋₊ ⌊Real.exp z⌋₊‖ ^ 2 : ℂ) *
        movingTemplateExternalMultiplier primes hprimes (n + 2) r₀ m active outside
          (normalizedResidueFamily setsReg) s φ Jleft Jright diagonal y x z)‖ ≤ _ at hdiagonal
  rw [← movingTemplate_compact_energy Subtype.val p outside μ childBound pivotBound V
    (fun i => normalizedResidueTransform (sets i)) Dq Finset.univ ψ X (Real.exp Δ) hi φ G
    (n + 2) r₀ m ν
    (fun s y x z => movingTemplateExternalMultiplier primes hprimes (n + 2) r₀ m active outside
      (normalizedResidueFamily setsReg) s φ Jleft Jright diagonal y x z)
    uG vG rG sG center] at hdiagonal
  let slot := movingTemplateBulk (n + 2) r₀ m
  let slots (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m)) (side : Bool) :=
    if side then slot ∘ perm.symm else (slot : _ → _)
  have hpairs (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
      (hperm : 4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2))) :=
    hg tierB primes hprimes childBound pivotBound V f outside p Dq sets β
      primeLo cutoff tier X Δ hi φ G active perm global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center cb (initialPairedHalfLogSlots (n + 2) b (slots perm))
      (fun j => (initialPairedHalfLogSlots_length _ _ _ j).trans (by omega)) hV hf0 hfnorm hcard hVn hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hB
      hm hp hsets hsetsp hpupper hperm hdlo hdhi hβ hbias hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
      hμrange hνrange hactive houtcover hinjp huBig hrBig hlocal hνtier hNlo hNcut hcutlo hloReal
      hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  have h := movingTemplate_initial_symmetrized_energy_bound primes hprimes (n + 2) r₀ b d r hm hlen
    cb cd sl sr fallback outside μ ν (fun j q => primeSubsetPrior_nonneg primes (Qν j) q)
    (fun j l => by dsimp only [ν]; rw [hν j, hν l])
    p (fun i => normalizedResidueTransform (sets i)) Dq childBound pivotBound V ψ X (Real.exp Δ) hi
    φ hφpos G active hactive (normalizedResidueFamily setsReg) Jleft Jright diagonal uG vG rG sG center _ _
    (by positivity) (by positivity) hdiagonal hpairs
  simpa only [add_assoc] using h

end Ostmann

end OAI
