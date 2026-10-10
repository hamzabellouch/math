import OAI.NumberTheory.Ostmann.Arithmetic.MovingSelectedTemplateEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSelectedTemplateLogGood
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateLogSymmetrizedEnergy

namespace OAI

/-! # Full bulk symmetrization under the actual selected harmonic priors -/

namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.moving_selected_template_log_symmetrized_energy
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C)
    (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ) (hk : 0 < k) (hn : n + 2 ≤ k)
    (A Wwin Bφ Dφ c K εdiag gain : ℝ)
    (hA : 0 ≤ A) (hWwin : 0 ≤ Wwin) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hc : 0 < c) (hK : 0 ≤ K) (hεdiag : 0 < εdiag)
    (hdepth : 8 * (K + 1) ≤ (k : ℝ) ^ 3)
    (Dlog : ℝ) (hDlog : 0 ≤ Dlog)
    (hloglip : ∀ x y, |logCellProfile x - logCellProfile y| ≤ Dlog * |x - y|) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ primeCutoff : ℕ, 3 ≤ primeCutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let Cprior := K + 1
      ∀ (tierB : MovingRegularSlot (n + 2) r₀ m → ℕ)
        (primes : Finset ℕ) (_hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound V : ℕ → ℕ) (f : ℤ → ℂ)
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
      Monotone V → f 0 = 0 →
      (∀ s, ‖f s‖ ≤ if s.natAbs ≤ V 0 then 1 else 0) →
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
      (∀ j : TreeLeafIndex (n + 2) × Fin r₀, tierB (j.1, .inl j.2) ≠ k) →
      (∀ j, tierB (slot j) = k) →
      (∀ q ∈ outside, ∃ i, p i = q) → Function.Injective p →
      Real.exp ((49 / 1000 : ℝ) * L) ≤ center → Real.exp ((49 / 1000 : ℝ) * L) ≤ rG →
      (∀ j (q : primes), (q : ℕ) ∈ Qμ j → tier q = j) →
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
          (fun T s => (movingBulkLeafLogWeight Subtype.val tier k outside cb cd T : ℂ) * f s)
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
    P.moving_selected_template_log_good_correlation C hM ψ n r₀ k hk A Wwin Bφ Dφ c K gain
      hA hWwin hBφ hDφ hc hK Dlog hDlog hloglip
  refine ⟨ε, hε, hε1, primeCutoff, hpc, ?_⟩
  filter_upwards [hgood, P.moving_selected_template_diagonal_energy C hM ψ (n + 2) r₀ k hk hn
    A Wwin Bφ Dφ c K εdiag hA hWwin hBφ hDφ hc hK hεdiag hdepth] with L hg hd
  dsimp only at hg hd ⊢
  intro tierB primes hprimes _ childBound pivotBound V f outside p _ Dq sets β
    primeLo cutoff tier X Δ hi φ G active global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center cb cd
    hV hf0 hf hcard hVn hV0 hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hB
    hm hp hsets hsetsp hpupper hdlo hdhi hβ hbias hφpos hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange hactive hsmalltier hbulktier houtcover hinjp huBig hrBig hμtier hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  let m := spectatorBulkCount k L
  let μ := fun j => primeSubsetPrior primes (Qμ j)
  let ν := fun j => primeSubsetPrior primes (Qν j)
  have hlocal := fun j (_ : j < n + 2) => hμtier j
  have hfnorm (s : ℤ) : ‖f s‖ ≤ 1 := (hf s).trans (by split_ifs <;> norm_num)
  have hdiagonal := hd tierB primes hprimes childBound pivotBound V f outside p Dq sets
    primeLo cutoff tier X Δ hi φ G active global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center
    hV hf0 hf hcard hVn hV0 hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hB
    (by omega) (fun i => hpc.trans (hp i)) hsets hsetsp hpupper hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
    hμrange hνrange hactive houtcover hinjp huBig hrBig hlocal hνtier hNlo hNcut hcutlo hloReal
    hupper hpband hdeleteμ hdeletep hdeleteν hsetsReg
  have hpairs (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
      (hperm : 4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2))) :=
    hg tierB primes hprimes childBound pivotBound V f outside p Dq sets β
      primeLo cutoff tier X Δ hi φ G active perm global Qμ Qν setsReg Jleft Jright diagonal uG vG rG sG center cb
      hV hf0 hfnorm hcard hVn hΔ hhi hwindow huG hrG huvG hrsG hvG hsG hvcenter hB
      hm hp hsets hsetsp hpupper hperm hdlo hdhi hβ hbias hφ hlip hφout hShell hdel hout hν hμP hνP hμmass hνmass
      hμrange hνrange hactive houtcover hinjp huBig hrBig hlocal hνtier hNlo hNcut hcutlo hloReal
      hupper hpband hdeleteμ hdeletep hdeleteν hdeletebulk hsetsReg
  have hμlevels (j) (q : primes) (hq : μ j q ≠ 0) : tier q = j :=
    hμtier j q (primeSubsetPrior_support primes (Qμ j) q hq)
  have hνlevels (y : MovingRegularSlot (n + 2) r₀ m → primes)
      (hy : (∏ j, ν j (y j)) ≠ 0) (j) : tier (y j) = tierB j :=
    hνtier j (y j) (primeSubsetPrior_support primes (Qν j) (y j)
      ((Finset.prod_ne_zero_iff.mp hy) j (Finset.mem_univ j)))
  have h := movingTemplate_log_symmetrized_energy_bound primes hprimes (n + 2) r₀ m k hm hn tier outside cb cd
    μ hμlevels ν (fun j q => primeSubsetPrior_nonneg primes (Qν j) q)
    (fun j l => by dsimp only [ν]; rw [hν j, hν l])
    (fun y hy j => by rw [hνlevels y hy]; exact hsmalltier j)
    (fun y hy j => by rw [hνlevels y hy]; exact hbulktier j)
    p (fun i => normalizedResidueTransform (sets i)) Dq childBound pivotBound V f ψ X (Real.exp Δ) hi
    φ hφpos G active hactive (normalizedResidueFamily setsReg) Jleft Jright diagonal uG vG rG sG center _ _
    (by positivity) (by positivity) hdiagonal hpairs
  simpa only [add_assoc] using h

end Ostmann

end OAI
