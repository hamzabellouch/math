import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMeanApproximationDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMean
open Construction Conclusion Filter HistorySignedResidues HistorySignedXiTransport HistorySymbolicEncoding
open HistoryGiantReferenceMean HistoryGiantPriorGrid HistoryGiantXiReplacementUncorrected
open HistoryPairSmoothXi HistoryPairGiantCoordinates ScaleBudget
open HistoryGiantOriginalMeanFactorization (Seed Current Choices history compensationFactor compensationFactor_eq)

theorem spectator_primes (spectator : PrimeSource) {m : ℕ}
    (ds : Fin m → spectator.Sample) : ∀q∈spectatorList spectator ds,q.Prime := by
  intro q hq
  simp only [spectatorList,List.mem_ofFn] at hq
  obtain ⟨i,rfl⟩ := hq
  exact spectator.prime _ (ds i).property

theorem selected_prime_approximation_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) (hBs : 0≤Bs) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 → |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
      ∀l≤k,
      ∀(x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
        (s t : ℤ)(c e : Choices (l:=l) C),
      (assignmentPrior C.sources _).mass x≠0 → (assignmentPrior C.sources _).mass y≠0 →
      choicesMass C.sources _ _ l c≠0 → choicesMass C.sources _ _ l e≠0 →
      originalPrimeMean C (spectatorList spectator ds) x y s t c e=0 ∨
        ∃r : PrimeDraw C.giant,0 < primeWeight C.giant r ∧
        ∃(hs : (history C x s (primeP C.giant r) (primeQ C.giant r) c).Supported
          (frequencyBound Bs BD Bz k L) (spectatorList spectator ds))
         (gs : (history C y t (primeP C.giant r) (primeQ C.giant r) e).Supported
          (frequencyBound Bs BD Bz k L) (spectatorList spectator ds)),
        ‖originalPrimeMean C (spectatorList spectator ds) x y s t c e -
          compensationFactor C x y s t c e *
            primeMainTerm C (spectatorList spectator ds)
              (history C x s (primeP C.giant r) (primeQ C.giant r) c) (history C y t (primeP C.giant r) (primeQ C.giant r) e)
              hs gs (spectator_primes spectator ds) (k+2)‖ ≤
          ‖compensationFactor C x y s t c e‖*(30*Real.exp (-Real.exp (giant.target*L))) := by
  filter_upwards [selected_prime_factorization_eventually d Bs BD Bz hk,
    selected_integer_guarded_replacement_eventually d Bs BD Bz hBs hk] with L hfactor hreplace
  intro E C hG hGu hcl hcu hb hd spectator hspec ds l hl x y s t c e hx hy hc he
  rcases hfactor E C hG hcl hcu hb hd l hl x y s t c e hx hy hc he
      (spectatorList spectator ds) (spectator_primes spectator ds) (k+2) with hz | ⟨r,hr,hs,gs,hfac⟩
  · exact Or.inl hz
  · refine Or.inr ⟨r,hr,hs,gs,?_⟩
    have hcell := prime_reference_cells C r hr
    have hpos := primeDraw_positive C.giant r
    have hPc : |Real.log ((primeP C.giant r):ℝ)-(C.giantCenter:ℝ)|≤1 := by
      simpa only [primeP,Int.cast_natCast] using hcell.1.le
    have hQc : |Real.log ((primeQ C.giant r):ℝ)-(C.giantCenter:ℝ)|≤1 := by
      simpa only [primeQ,Int.cast_natCast] using hcell.2.le
    have hbound := (hreplace E C hG hGu hcl hcu hb hd spectator hspec ds l hl
      x y s t (primeP C.giant r) (primeQ C.giant r) c e hx hy hc he hpos.1 hpos.2 hPc hQc
      hs gs (spectator_primes spectator ds) ∅ (by simp) C.giantPositive).1
    rw [prime_factor_difference C _ _ _ hs gs (spectator_primes spectator ds) (k+2)
      _ _ hfac,norm_mul]
    exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)

theorem selected_mixed_approximation_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) (hBs : 0≤Bs) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 → |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
      ∀l≤k,
      ∀(x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
        (s t : ℤ)(c e : Choices (l:=l) C),
      (assignmentPrior C.sources _).mass x≠0 → (assignmentPrior C.sources _).mass y≠0 →
      choicesMass C.sources _ _ l c≠0 → choicesMass C.sources _ _ l e≠0 →
      originalMixedMean C (spectatorList spectator ds) x y s t c e=0 ∨
        ∃r : MixedDraw C.giantCenter C.giant,0 < mixedWeight C.giantCenter C.giant r ∧
        ∃(hs : (history C x s (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r) c).Supported
          (frequencyBound Bs BD Bz k L) (spectatorList spectator ds))
         (gs : (history C y t (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r) e).Supported
          (frequencyBound Bs BD Bz k L) (spectatorList spectator ds)),
        ‖originalMixedMean C (spectatorList spectator ds) x y s t c e -
          compensationFactor C x y s t c e *
            mixedMainTerm C (spectatorList spectator ds)
              (history C x s (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r) c) (history C y t (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r) e)
              hs gs (spectator_primes spectator ds) (k+2)‖ ≤
          ‖compensationFactor C x y s t c e‖*(9*Real.exp (-Real.exp (giant.target*L))) := by
  filter_upwards [selected_mixed_factorization_eventually d Bs BD Bz hk,
    selected_integer_guarded_replacement_eventually d Bs BD Bz hBs hk] with L hfactor hreplace
  intro E C hG hGu hcl hcu hb hd spectator hspec ds l hl x y s t c e hx hy hc he
  rcases hfactor E C hG hcl hcu hb hd l hl x y s t c e hx hy hc he
      (spectatorList spectator ds) (spectator_primes spectator ds) (k+2) with hz | ⟨r,hr,hs,gs,hfac⟩
  · exact Or.inl hz
  · refine Or.inr ⟨r,hr,hs,gs,?_⟩
    have hcell := mixed_reference_cells C r hr
    have hpos := mixedDraw_positive C.giantCenter C.giant r
    have hPc : |Real.log ((mixedP C.giantCenter C.giant r):ℝ)-(C.giantCenter:ℝ)|≤1 := by
      simpa only [mixedP,Int.cast_natCast] using hcell.1.le
    have hQc : |Real.log ((mixedQ C.giantCenter C.giant r):ℝ)-(C.giantCenter:ℝ)|≤1 := by
      simpa only [mixedQ,Int.cast_natCast] using hcell.2.le
    have hbound := (hreplace E C hG hGu hcl hcu hb hd spectator hspec ds l hl
      x y s t (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r) c e hx hy hc he hpos.1 hpos.2 hPc hQc
      hs gs (spectator_primes spectator ds) ∅ (by simp) C.giantPositive).2
    rw [mixed_factor_difference C _ _ _ hs gs (spectator_primes spectator ds) (k+2)
      _ _ hfac,norm_mul]
    exact mul_le_mul_of_nonneg_left hbound (norm_nonneg _)

end Ostmann.Arithmetic.HistoryGiantUncorrectedOriginalMean

end

end OAI
