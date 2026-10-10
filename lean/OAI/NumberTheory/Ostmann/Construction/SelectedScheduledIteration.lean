import OAI.NumberTheory.Ostmann.Construction.ScheduledCellIteration

namespace OAI

/-! # Iteration supplied by the actual selected priors and coefficient gaps -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem selected_scheduled_iteration
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    {N hi top : ℕ} {a C L Y G cb cd Dlog Bs BD Bz : ℝ}
    {D P Qb : Finset ℕ} {cs : List ℕ} (k : ℕ) (hk : 2 ≤ k)
    (hP : ∀ p ∈ P, p.Prime) (hambient : initialRegularPrimeRange L ⊆ P)
    (hL : 1 ≤ L) (hY : 0 < Y) (hYupper : Y ≤ Real.exp L)
    (hcell : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (8 + 4 * cs.length : ℕ) ≤ L)
    (hm : 256 ≤ (spectatorBulkCount k L : ℝ))
    (hG : 1 ≤ G) (hcb : 0 ≤ cb) (hD : |Dlog - 2 * cd| ≤ 2)
    (hBs : 0 ≤ Bs) (hBD : Bs + 1 ≤ BD) (hBz : 8 ≤ Bz)
    (herror : 256 * tailDefectBudget a C Y + 9 ≤ (spectatorBulkCount k L : ℝ) / 40)
    (hbudget : 40 * (2 * ((initialSmallCellList top cs).length + 3) + 14 + 4 * cs.length) +
      20 * Real.log 2 < (spectatorBulkCount k L : ℝ))
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top)
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L Y hi D (t / 4) j)
      cs (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L)))
    (hlower : ∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (hbulk : Qb ⊆ initialRegularPrimeRange L)
    (hbulklower : ∀ p ∈ Qb, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ))
    (hdis : ∀ p ∈ P, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (b d : ℕ)
    (sl sr : Fin d → P) (fallback : P)
    {J : Type} (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : 𝓢(ℝ, ℂ)) (X lo upper : ℝ) (hX : 0 < X)
    (φ : ℝ → ℝ) (hφ : ∀ x, 0 ≤ φ x) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (hpos : 0 < smoothGiantMass (smoothGiantPrimeRange G) φ G)
    (outside : List ℕ) (favorable : ℕ → Bool) (B₀ : ℝ) :
    let width : ℝ := 2 * ((initialSmallCellList top cs).length + 3)
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
    let W := Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog
    let V := movingProductNaturalCutoff T W (Y - Dlog) ((spectatorBulkCount k L : ℝ) / 4)
    let μ := completedCompensationPrior A B N Y hi D P top cs
    let cell := fun c => primeSubsetPrior P (selectedTailCellPrimes A B N Y hi D c)
    let F := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b d (initialSmallCellList top cs).length cb cd sl sr fallback)
      g Dq S ψ X lo upper
    let I := Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊
    let ρ := smoothGiantPrior (smoothGiantPrimeRange G) φ G
    let greg := normalizedResidueFamily (tailDensityMask A N)
    let η := fun n => scheduledCellAmplitude Subtype.val outside μ (scheduledChildBound V)
      (scheduledPivotCaps G cs) V F φ (fun _ => G) (smoothGiantPrimeRange G) ρ
      cell (primeSubsetPrior P Qb) top cs n (b + b) greg greg favorable
    let diag := fun n => scheduledCellDiagonal Subtype.val outside μ (scheduledChildBound V)
      (scheduledPivotCaps G cs) V F φ (fun _ => G) (smoothGiantPrimeRange G) I ρ
      cell (primeSubsetPrior P Qb) top cs n (b + b) greg greg favorable
    X * upper ≤ Real.exp W →
    (∀ n ≤ k, (V n : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L))) →
    (∀ n ≤ k, (V n : ℝ) < Real.exp (G - 1)) →
    smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G ≤ L →
    Real.exp (-B₀ * (spectatorBulkCount k L : ℝ)) ≤ ‖η 0‖ →
    (∀ n < k, diag n ≤ Real.exp (-(2 * (B₀ + 1) + 3) * (2 : ℝ) ^ n * spectatorBulkCount k L)) →
    ∀ n ≤ k, Real.exp (-(B₀ + 1) * (2 : ℝ) ^ n * spectatorBulkCount k L) ≤ ‖η n‖ := by
  intro width T W V μ cell F I ρ greg η diag hwindow hfreq hgiantfreq hcg hinit hdiag
  have hscale : 4 ≤ (k : ℝ) ^ 4 * L :=
    (show (4 : ℝ) ≤ spectatorBulkCount k L by linarith).trans
      (spectatorBulkCount_upper k L (by linarith))
  refine variable_transfer_iteration k η diag
    (fun _ => max 0 (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G))
    B₀ (spectatorBulkCount k L) (Nat.cast_nonneg _)
    (fun _ _ => le_max_left _ _) ?_ hinit hdiag ?_
  · exact spectatorBulkCount_iteration_budget k hk L hL hscale
      (fun _ => max 0 (smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G))
      (fun _ _ => max_le (by linarith) hcg)
  · intro j hj
    apply le_trans _ (show Real.exp (-smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G) *
      ‖η j‖ ^ 2 ≤ diag j + ‖η (j + 1)‖ from ?_)
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact Real.exp_le_exp.mpr (neg_le_neg (le_max_right _ _))
    · simpa only [η, diag, scheduledCellDiagonal] using selected_scheduled_amplitude_step hA hB
        k j hj (by omega) hP hambient hL hY hYupper hcell hcount hm hG hcb hD hBs hBD hBz
        herror hbudget htop hcs hlower hbulk hbulklower hdis b d sl sr fallback
        q g Dq S ψ X lo upper hX φ hφ hout hpos outside favorable hwindow
        (hfreq (j + 1) (by omega)) (hgiantfreq (j + 1) (by omega))

end Ostmann

end OAI
