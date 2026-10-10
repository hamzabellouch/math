import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternWindowArithmeticRate
import OAI.NumberTheory.Ostmann.Arithmetic.WholeShellGeometry
import OAI.NumberTheory.Ostmann.Construction.WholeShellMass
import OAI.NumberTheory.Ostmann.Construction.FrozenPrimeDeletions

namespace OAI

/-! # The arithmetic estimate for the original full bulk shell -/

namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators SchwartzMap

theorem PublishedProgressionInput.movingPattern_whole_shell_arithmetic_rate_window
    (P : PublishedProgressionInput) (C : ℝ) (hM : MertensEstimate C) (ψ : 𝓢(ℝ, ℂ)) (n r₀ k : ℕ)
    (A H Bφ Dφ F Cmass gain : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hF : 0 ≤ F) (hCmass : 1 ≤ Cmass)
    (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∃ cutoff : ℕ, 3 ≤ cutoff ∧
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      ∀ (lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi), hi - lo ≤ Real.exp (H * m) →
      ∀ (Bidx Cidx : Type) [Fintype Bidx] [Fintype Cidx] (N : ℕ)
        (e : Fin (N + 1) ≃ Bidx ⊕ Cidx) (tierB : Bidx → ℕ) (tierC : Cidx → ℕ)
        (t : Bool → FrequencyTree ℤ (n + 2))
        (small : Bool → TreeLeafTuple (List Bidx) (n + 2))
        (slot : (TreeLeafIndex (n + 2) × Fin m) ↪ Bidx)
        (perm : Equiv.Perm (TreeLeafIndex (n + 2) × Fin m))
        (pattern : Bool × MovingSampleIndex (n + 2) → Cidx)
        (rep : ∀ c, {i : Bool × MovingSampleIndex (n + 2) // pattern i = c})
        (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime) [Nonempty primes]
        (childBound pivotBound : ℕ → ℕ)
        (hfreq : ∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), s ≠ 0)
        (Fw : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℂ)
        (Ew : Bool → {d : ℕ} → MovingSlotData (Fin (N + 1)) d → ℤ → ℤ → ℤ → ℝ)
        (outside : List ℕ) (R : ℤ) (r : ℕ) [NeZero r]
        (p : Fin m → ℕ) [∀ i, Fact (p i).Prime]
        (_hc : Pairwise (fun i j => (bulkResidueModuli r p i).Coprime (bulkResidueModuli r p j)))
        [NeZero (∏ i, bulkResidueModuli r p i)]
        (twist : ∀ i, Bool → (ZMod (p i))ˣ) (sets : ∀ i, Finset (ZMod (p i)))
        (β : Fin m → ℝ) (Qfreq : ℕ) (y X : ℝ) (_j₀ : TreeLeafIndex (n + 2) × Fin m)
        (φ : ℝ → ℝ) (G : ℕ → ℝ) (XL U : ℝ)
        (global : Finset ℕ)
        (μ : ℕ → primes → ℝ) (ν : Bidx → primes → ℝ)
        (Eprior αall βint Vint Uall : ℝ),
      let data := movingPatternFinBulkData e (n + 2) m t small slot perm pattern
      let M := ∏ i, bulkResidueModuli r p i
      let S := primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
        (Real.exp ((6 / 1000 : ℝ) * L))
      let amp := 2 * (‖movingDataWeight (Fw false) (Ew false) (data false)‖ *
        ‖movingDataWeight (Fw true) (Ew true) (data true)‖)
      let law := fun i => Sum.elim ν (fun c => μ (movingSampleTier (rep c).val.2)) (e i)
      let obs := movingPatternPrimeObservable e t small slot perm pattern primes hprimes
        childBound pivotBound hfreq Fw Ew outside R r p
        (fun i => normalizedResidueTransform (sets i)) twist P Qfreq
        y ψ X lo hi hlo hhi φ G XL U
      let cost := (amp * ∏ i, (p i : ℝ) ^ (2 ^ (n + 2 + 1))) *
        (movingFourierVariationBudget ψ (Real.exp (A * m)) lo hi (n + 2) *
          (2 * Bφ + Dφ * (Real.exp 2 - 1)) ^ (2 ^ (n + 2) - 1)) ^ 2
      1 ≤ m →
      (∀ b, ∀ i ∈ flattenMovingSlots (n + 2) (small b), i ∉ Set.range slot) →
      (∀ i, n + 2 ≤ tierB i) → (∀ i, tierC (pattern i) = movingSampleTier i.2) →
      (∀ b, MovingLeafLengthLE (n + 2) (small b) r₀) →
      (∀ b, (data b).frequencyProduct ∣ R) → R ^ (n + 2 + 1) ∣ (r : ℤ) →
      (∀ b, ∀ s ∈ allFrequencyList (n + 2) (t b), |(s : ℝ)| ≤ Real.exp (A * m)) →
      (∀ i, cutoff ≤ p i) →
      (∀ i b, ∀ s ∈ allFrequencyList (n + 2) (t b), s.natAbs < p i) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i b, ∀ j ∈ flattenMovingSlots (n + 2) (small b),
          ((x (e.symm (.inl j)) : ℕ) : ZMod (p i)) ≠ 0) →
      (∀ x : Fin (N + 1) → primes, productPrior law x ≠ 0 →
        ∀ i c, ((x (e.symm (.inr c)) : ℕ) : ZMod (p i)) ≠ 0) →
      4 * Fintype.card (arrangementGraph m perm).ConnectedComponent ≤
        3 * Fintype.card (TreeLeafIndex (n + 2)) →
      (∀ i, (1 / 3 : ℝ) ≤ residueDensity (sets i)) →
      (∀ i, residueDensity (sets i) ≤ 2 / 3) →
      (∀ i, (sets i).Nonempty) → (∀ i, (sets i).card < p i) →
      (∀ i, 2 * β i ≤ ε) →
      (∀ i (χ : MulChar (ZMod (p i)) ℂ), χ ≠ 1 → ∀ a : ZMod (p i),
        ‖((sets i).card : ℂ)⁻¹ * ∑ x ∈ sets i, χ⁻¹ (-a - x)‖ ≤ β i) →
      amp ≤ Real.exp (F * m) → 0 ≤ y →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      M ≤ bulkProgressionCutoff L →
      pageAtModulus M (selectedPageZero P (bulkProgressionCutoff L)) =
        pageAtModulus r (selectedPageZero P (bulkProgressionCutoff L)) →
      (∀ x, |φ x| ≤ Bφ) → (∀ x y, |φ x - φ y| ≤ Dφ * |x - y|) →
      (∀ x, 1 ≤ |x| → φ x = 0) →
      S ⊆ primes →
      ((global.card + (N + 1) + outside.length : ℕ) : ℝ) ≤ Real.exp (Cmass * L) →
      (∀ q ∈ outside, q.Prime) →
      (∀ j, ν (slot j) = primeSubsetPrior primes (S \ global)) →
      (∀ j q, 0 ≤ μ j q) → (∀ j q, 0 ≤ ν j q) →
      (∀ j, ∑ q, μ j q = 1) → (∀ j, ∑ q, ν j q = 1) →
      0 ≤ Eprior → 0 ≤ αall → 0 ≤ βint → 0 < Vint → 1 ≤ Uall →
      (∀ j (q : primes), (q : ℝ) * μ j q ≤ Eprior) →
      (∀ j q, μ j q ≤ αall) → (∀ j q, ν j q ≤ αall) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≤ βint) →
      (∀ c q, μ (movingSampleTier (rep c).val.2) q ≠ 0 → Real.exp Vint ≤ (q : ℝ)) →
      (∀ q : primes, (q : ℝ) ≤ Uall) →
      (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ i j,
        (Sum.elim tierB tierC) (e i) ≠ (Sum.elim tierB tierC) (e j) →
          (x i : ℕ) ≠ (x j : ℕ)) →
      (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ b c,
        (x (e.symm (.inl b)) : ℕ) ≠ (x (e.symm (.inr c)) : ℕ)) →
      (∀ x, productPrior law x ≠ 0 → obs x ≠ 0 → ∀ c b, (data b).Frequencies
        (fun s => (s : ZMod (x (e.symm (.inr c)) : ℕ)) ≠ 0)) →
      ‖∑ x, movingOriginalPatternWeight e μ ν (fun q : primes => (q : ℕ)) (n + 2) pattern obs x *
        movingPatternHaarProduct e (fun q : primes => (q : ℕ)) (fun q => hprimes _ q.property)
          (n + 2) t small (movingPatternBulkLeaves (n + 2) m slot perm) pattern x‖ ≤
      ((2 : ℝ) ^ Fintype.card Cidx * Eprior ^ (4 * (n + 2) * 2 ^ (n + 2) - Fintype.card Cidx)) *
        (cost * movingInternalArithmeticError (n + 2) (Fintype.card Cidx)
          (2 ^ (n + 2) * (r₀ + m + 4 * (n + 2) + 4)) (Real.exp (A * m)) Uall αall βint Vint +
        (Real.exp (-gain * m) + Real.exp (-Real.exp ((125 / 100000 : ℝ) * L)) +
          2 * Real.exp (-Real.exp ((2 / 1000 : ℝ) * L)))) := by
  obtain ⟨ε, hε, hε1, cutoff, hcutoff, hrate⟩ :=
    P.movingPattern_original_arithmetic_rate_window ψ n r₀ k A H Bφ Dφ F Cmass gain
      hA hH hF hCmass hBφ hDφ
  refine ⟨ε, hε, hε1, cutoff, hcutoff, ?_⟩
  have hlarge := (Real.tendsto_exp_atTop.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4 / 1000))).eventually
      (eventually_ge_atTop (2 * (Real.log 2 + 2 * C)))
  filter_upwards [hrate, wholePrimeGridCount_eventual (6 / 1000) (by norm_num),
    hlarge, eventually_ge_atTop (max 0 (max (Real.log 4) (500 * Real.log 2)))]
    with L hrate hgrid hlarge hL
  have hL0 : 0 ≤ L := (le_max_left _ _).trans hL
  have hL4 : Real.log 4 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hL2 : 500 * Real.log 2 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  dsimp only
  intro lo hi hlo hhi hwidth Bidx Cidx _ _ N e tierB tierC t small slot perm pattern rep primes hprimes _
    childBound pivotBound hfreq Fw Ew outside R r _ p _ hc _ twist sets β Qfreq y X j₀ φ G XL U global
    μ ν Eprior αall βint Vint Uall hm hsmall hB htier hsmallLen hR hr hV hp hfreqp hsmallp hsamplesp hgood
    hdlo hdhi hsets hsetsp hβ hbias hamp hy hpupper hMQ hpage hφ hlip hφout
    hS hdel hout hν hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hdisjoint hcross hfmod
  let m := spectatorBulkCount k L
  let a : ℝ := (4 / 1000) * L
  let b : ℝ := (6 / 1000) * L
  let u := fun (_ : TreeLeafIndex (n + 2) × Fin m) => wholeShellLower a b
  let v := fun (_ : TreeLeafIndex (n + 2) × Fin m) => wholeShellUpper a b
  let M := ∏ i, bulkResidueModuli r p i
  let S := primeLogCellSet 1 0 (Real.exp a) (Real.exp b)
  let D := fun x : Fin (N + 1) → primes => global ∪
    frozenPrimeDeletions (fun i => (x i : ℕ)) (movingPatternBulkEmbedding e slot) outside
  have hab : a ≤ b := by dsimp only [a, b]; nlinarith
  have hgeometry := whole_shell_geometry a b hab
  have ha0 : 0 ≤ a := mul_nonneg (by norm_num) hL0
  have hlow (j) (c) : Real.exp ((39 / 10000 : ℝ) * L) ≤ u j c := by
    exact (Real.exp_le_exp.mpr (by dsimp only [a]; nlinarith)).trans (hgeometry.1 c)
  have hMbase : (M : ℝ) ≤ Real.exp (Real.exp a) :=
    modulus_le_exp_bulk_endpoint hMQ hL0
      (Real.exp_le_exp.mpr (by dsimp only [a]; nlinarith))
  have hsupport (j) :
      primeCellSupport M (fun c : Fin (wholePrimeGridCount b) × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1) = S :=
    whole_shell_support M a b hab hMbase
  have hunit (j) (c) : 1 ≤ u j c :=
    (Real.one_le_exp_iff.mpr ha0).trans (hgeometry.1 c)
  have hMcell (j) (c) : (M : ℝ) ≤ Real.exp (u j c) :=
    hMbase.trans (Real.exp_le_exp.mpr (hgeometry.1 c))
  have hcard : (Fintype.card (Fin (wholePrimeGridCount b)) : ℝ) ≤
      Real.exp (Real.exp ((14 / 10000 : ℝ) * L)) := by
    simpa only [Fintype.card_fin] using hgrid b (le_refl _)
  have htwo : 2 * Real.exp a ≤ Real.exp b := by
    have he : Real.log 2 + a ≤ b := by dsimp only [a, b]; nlinarith
    have hh := Real.exp_le_exp.mpr he
    simpa only [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hh
  have hmass : Real.exp (-Cmass * L) ≤ ∑ q ∈ S, (q : ℝ)⁻¹ := by
    have he : Real.exp (-Cmass * L) ≤ (1 / 4 : ℝ) := by
      calc
        _ ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.mpr (by nlinarith)
        _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]; norm_num
    exact he.trans (whole_shell_mass_lower hM (Real.exp a) (Real.exp b)
      (Real.one_le_exp_iff.mpr ha0) hlarge htwo)
  have hDcard (x) : ((D x).card : ℝ) ≤ Real.exp (Cmass * L) := by
    have hh : (D x).card ≤ global.card + (N + 1) + outside.length := by
      have ht := (Finset.card_union_le global _).trans
        (Nat.add_le_add_left (frozenPrimeDeletions_card_le
          (fun i => (x i : ℕ)) (movingPatternBulkEmbedding e slot) outside) global.card)
      simpa only [Fintype.card_fin, Nat.add_assoc] using ht
    exact (Nat.cast_le.mpr hh).trans hdel
  have hsub (j) : S \ global ⊆ primeCellSupport M
      (fun c : Fin (wholePrimeGridCount b) × (ZMod M)ˣ => c.2.val.val)
      (fun c => u j c.1) (fun c => v j c.1) := by
    rw [hsupport j]; exact Finset.sdiff_subset
  have hretain (x) (j) :
      primeCellSupport M (fun c : Fin (wholePrimeGridCount b) × (ZMod M)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1) \ D x ⊆ S \ global := by
    rw [hsupport j]
    intro q hq
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hq).1,
      fun hg => (Finset.mem_sdiff.mp hq).2 (Finset.mem_union_left _ hg)⟩
  dsimp only [M] at hsupport
  have hfinal := hrate lo hi hlo hhi hwidth Bidx Cidx (Fin (wholePrimeGridCount b)) N e tierB tierC t small
    slot perm pattern rep primes hprimes childBound pivotBound hfreq Fw Ew outside R r p hc
    twist sets β Qfreq y X j₀ φ G XL U u v (fun x _ => D x) (fun _ => S \ global)
    μ ν Eprior αall βint Vint Uall hm hsmall hB htier hsmallLen hR hr hV hp hfreqp
    hsmallp hsamplesp hgood hdlo hdhi hsets hsetsp hβ hbias hamp hy hpupper hMQ hpage
    hφ hlip hφout hcard hunit hlow (fun _ => hgeometry.2.1)
    (fun _ => hgeometry.2.2.1) (fun _ => hgeometry.2.2.2) hMcell
    (fun j => by simpa only [hsupport j] using hS) (fun x _ _ => hDcard x)
    (fun j => by simpa only [hsupport j] using hmass)
    (fun x _ _ i hi => Finset.mem_union_right _
      (mem_frozenPrimeDeletions_base (fun i => (x i : ℕ)) _ outside i hi)) hout
    (fun x _ _ q hq => Finset.mem_union_right _
      (mem_frozenPrimeDeletions_outside (fun i => (x i : ℕ)) _ outside q hq))
    (⟨0, wholePrimeGridCount_pos b⟩, 1) hsub (fun x _ => hretain x) hν
    hμ0 hν0 hμmass hνmass hEprior hαall hβint hVint hUall
    hμbound hμall hνall hμmax hμmin hvalues hdisjoint hcross hfmod
  exact hfinal

end Ostmann

end OAI
