import OAI.NumberTheory.Ostmann.Arithmetic.MovingFullCoefficientTransfer
import OAI.NumberTheory.Ostmann.Construction.ScheduledCoefficientGap
import OAI.NumberTheory.Ostmann.Construction.ScheduledLiveBounds
import OAI.NumberTheory.Ostmann.Construction.ScheduledAmplitude
import OAI.NumberTheory.Ostmann.Construction.TailSieveMasks

namespace OAI

/-! # The actual selected cells satisfy the original finite transfer step -/
namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

noncomputable def scheduledChildBound (V : ℕ → ℕ) (j : ℕ) : ℕ := V (j - 1)
noncomputable def scheduledPivotCaps (G : ℝ) (cs : List ℕ) (j : ℕ) : ℕ :=
  scheduledPivotBound G cs (j - 1)

theorem selected_scheduled_amplitude_step
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    {N hi top : ℕ} {a C L Y G cb cd Dlog Bs BD Bz : ℝ}
    {D P Qb : Finset ℕ} {cs : List ℕ} (k n : ℕ) (hn : n < k) (hk : 1 ≤ k)
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
    (outside : List ℕ) (favorable : ℕ → Bool) :
    let width : ℝ := 2 * ((initialSmallCellList top cs).length + 3)
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
    let W := Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog
    let V := movingProductNaturalCutoff T W (Y - Dlog) ((spectatorBulkCount k L : ℝ) / 4)
    let μ := completedCompensationPrior A B N Y hi D P top cs
    let cell := fun c => primeSubsetPrior P (selectedTailCellPrimes A B N Y hi D c)
    let F := movingOriginalLeaf Subtype.val q
      (initialMovingDataCutoff Subtype.val b d (initialSmallCellList top cs).length cb cd sl sr fallback)
      g Dq S ψ X lo upper
    let ν := scheduledRegularPrior cell (primeSubsetPrior P Qb) top (cs.drop (n + 1)) n (b + b)
    let I := Finset.Ioc ⌊Real.exp (G - 1)⌋₊ ⌊Real.exp (G + 1)⌋₊
    let ρ := smoothGiantPrior (smoothGiantPrimeRange G) φ G
    let greg := normalizedResidueFamily (tailDensityMask A N)
    X * upper ≤ Real.exp W →
    (V (n + 1) : ℝ) < Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) →
    (V (n + 1) : ℝ) < Real.exp (G - 1) →
    Real.exp (-smoothGiantLogNormalizer (smoothGiantPrimeRange G) φ G) *
      ‖scheduledCellAmplitude Subtype.val outside μ (scheduledChildBound V)
        (scheduledPivotCaps G cs) V F φ (fun _ => G) (smoothGiantPrimeRange G) ρ
        cell (primeSubsetPrior P Qb) top cs n (b + b) greg greg favorable‖ ^ 2 ≤
      movingAmplitudeDiagonal Subtype.val outside μ (scheduledChildBound V)
        (scheduledPivotCaps G cs) V F φ (fun _ => G) n
        (scheduledSmallLength (cs.drop (n + 1))) (b + b) (smoothGiantPrimeRange G) I
        ρ ν greg greg favorable +
      ‖scheduledCellAmplitude Subtype.val outside μ (scheduledChildBound V)
        (scheduledPivotCaps G cs) V F φ (fun _ => G) (smoothGiantPrimeRange G) ρ
        cell (primeSubsetPrior P Qb) top cs (n + 1) (b + b) greg greg favorable‖ := by
  intro width T W V μ cell F ν I ρ greg hwindow hfreq hgiantfreq
  have hlen : cs.length = k := by
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using hcs.length_eq
  have hncs : n < cs.length := by omega
  have hμcell : μ n = cell ((cs.drop n).headD 0) :=
    completedCompensationPrior_cell A B N Y hi D P top cs n hncs
  rw [scheduledCellAmplitude_restore (cs := cs) (n := n) (hn := hncs) (hμ := hμcell),
    ← scheduledCellAmplitude_next]
  have hproduct := selectedProductExponent_budget_of_cells (G := G) (Y := Y) (cd := cd)
    (Dlog := Dlog) (width := width) (BD := BD) (Bz := Bz) k hk
    hL hY hYupper hcell hcount hcb (by linarith only [(abs_le.mp hD).2])
    (show 0 ≤ width by dsimp only [width]; positivity) (by linarith) (by linarith) htop hcs
  change ∀ j, 2 * T j ≤ movingProductExponent T W j at hproduct
  have hpositive : 0 ≤ movingProductExponent T W n - T n := by
    have ht := selected_cell_pivot_nonneg G hG cs n
    change 0 ≤ T n at ht
    linarith [hproduct n]
  have hcenter : 0 ≤ selectedInitialLogCenter G Y cb cd top cs := by
    apply le_trans _ (selected_initial_center_bounds k htop hcs).1
    unfold spectatorBaseGap
    have hz : 0 ≤ Real.log ((k : ℝ) ^ 4) :=
      Real.log_nonneg (one_le_pow₀ (by exact_mod_cast hk))
    positivity
  have hYreg : Y - Dlog ≤ W := by
    have hw : 0 ≤ width := by dsimp only [width]; positivity
    dsimp only [W]
    linarith
  have hμdata := completedCompensationPrior_data htop hcs P hambient n
  have hIlower (p : ℕ) (hp : p ∈ I) : Real.exp (G - 1) ≤ (p : ℝ) :=
    ((Nat.floor_lt (Real.exp_nonneg _)).mp (Finset.mem_Ioc.mp hp).1).le
  have hIpos (p : ℕ) (hp : p ∈ I) : 0 < p := by
    have hh := (Real.exp_pos (G - 1)).trans_le (hIlower p hp)
    exact_mod_cast hh
  have hPglive (p : smoothGiantLivePrimes (smoothGiantPrimeRange G) φ G) :
      (p : ℕ).Prime := smoothGiantPrimeRange_prime G p
        (smoothGiantLivePrimes_subset _ _ _ p.property)
  have hPglarge (p : smoothGiantLivePrimes (smoothGiantPrimeRange G) φ G) :
      V (n + 1) < (p : ℕ) := by
    have hh := smoothGiantLivePrimes_bounds _ (smoothGiantPrimeRange_prime G) φ G hout p
    exact_mod_cast hgiantfreq.trans hh.1
  have hνlarge (i : MovingRegularSlot n (scheduledSmallLength (cs.drop (n + 1))) (b + b))
      (p : P) (hp : ν i p ≠ 0) : V (n + 1) < (p : ℕ) :=
    selected_scheduled_regular_large htop hcs (by linarith) hlower hbulk hbulklower
      n (b + b) (n + 1) (V (n + 1)) hfreq i p hp
  have hμlarge (p : P) (hp : μ n p ≠ 0) : V (n + 1) < (p : ℕ) :=
    selected_scheduled_compensation_large htop hcs (by linarith) hlower n (V (n + 1)) hfreq p hp
  apply movingTemplatePrimeAmplitude_step_full_coefficients Subtype.val
    (fun p => hP p p.property) outside μ (scheduledChildBound V) (scheduledPivotCaps G cs) V
    q (initialMovingDataCutoff Subtype.val b d (initialSmallCellList top cs).length cb cd sl sr fallback)
    (initialMovingDataCutoff_zero _ _ _ _ _ _ _ _ _) g Dq S ψ X lo upper W hX hwindow
    φ (fun _ => G) (selectedCompensationCenter cs) hout
    (completedCompensationPrior_lower A B N Y hi D P hP top cs)
    n (scheduledSmallLength (cs.drop (n + 1))) (b + b) (Y - Dlog)
    ((spectatorBulkCount k L : ℝ) / 4) (by linarith) hYreg rfl hproduct hpositive
    (smoothGiantPrimeRange G) I (smoothGiantPrimeRange_prime G)
    (fun p hp => smoothGiant_nonzero_in_log_cell φ G hout p
      (smoothGiantPrimeRange_prime G p (smoothGiantLivePrimes_subset _ _ _ hp)).pos
      (Finset.mem_filter.mp hp).2)
    hIpos hφ hpos (fun p => (hμdata.2.2.2 p).1) hμdata.2.2.1 ν (tailDensityMask A N)
    (fun p => tailDensityMask_nonempty hA N p (hP p p.property).pos)
    (fun p => by
      let : NeZero (p : ℕ) := ⟨(hP p p.property).ne_zero⟩
      exact tailDensityMask_card_lt hB N p (hP p p.property).pos (hdis p p.property))
    greg favorable
    (fun p x => by
      let : Fact (p : ℕ).Prime := ⟨hPglive p⟩
      dsimp only [greg]
      rw [normalizedResidueFamily_eq]
      exact normalizedResidueTransform_neg (tailDensityMask A N p) x)
    ⌈Real.exp (movingProductExponent T W n - T n)⌉₊ rfl hIlower
    (fun p y hy ℓ hℓ hd => live_giant_product_divisor_large Subtype.val
      (fun p => hP p p.property) ν (V (n + 1)) p (hPglive p) (hPglarge p)
      hνlarge y hy ℓ hℓ hd) hPglarge
    (smoothGiant_nonzero_in_log_cell φ G hout) (by rfl)
  · intro XR right hright u _ p w hcoeff
    exact selected_scheduled_coefficient_gap k n hn hk (by linarith) hP hG hD
      herror hBD hBz hbudget hcs b d sl sr fallback q g Dq S ψ X lo upper φ outside μ
      (scheduledChildBound V) (scheduledPivotCaps G cs) u right
      (fun i => scheduledRegularPrior_support A B N hi Y D P Qb top (cs.drop (n + 1))
        n (b + b) i (right i) (Finset.prod_ne_zero_iff.mp hright i (Finset.mem_univ _)))
      p XR w (smoothGiantLivePrimes_bounds _ (smoothGiantPrimeRange_prime G) φ G hout XR).1.le
      rfl rfl hcoeff
  · intro u hu
    refine ⟨fun p hp => ?_, fun ℓ hℓ hd => ?_⟩
    · exact selected_scheduled_pivot_bound hcs n hncs u hu p hp
    · have hh := live_prime_product_divisor_large Subtype.val (fun p => hP p p.property)
        (fun _ x => μ n x) (V (n + 1)) (fun _ => hμlarge) u hu ℓ hℓ hd
      exact lt_of_le_of_lt (movingProductNaturalCutoff_monotone T W (Y - Dlog)
        ((spectatorBulkCount k L : ℝ) / 4) hproduct (Nat.le_succ n)) hh

end Ostmann

end OAI
