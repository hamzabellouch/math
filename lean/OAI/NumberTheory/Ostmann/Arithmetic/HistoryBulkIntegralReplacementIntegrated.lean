import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIntegralReplacementBounds

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkIntegralReplacement
open Construction Conclusion HistoryBulkPriorGrid HistoryPrincipalIntegralAverage
open HistoryPrincipalIntegralFinite HistoryBulkReplacementError PrimeCellFreezing ScaleBudget Filter

theorem prime_integrated_replacement_eventually (k : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀(ι κ:Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ],
      ∀(M:ℕ) [NeZero M], ∀(a:ℕ)(E:Finset ℕ),
      Fintype.card ι ≤ 2^k*bulkSize k L → a ≤ residueCostExponent k →
      Real.log (M:ℝ) ≤ Real.exp (bulk.μ*L) → E.card ≤ 2 →
      ∀(hZ:0 < harmonicPrimeMass (bulkPrimeBand L E))
        (hsize:(M:ℝ) < Real.exp (bulkLogLower L))
        (F:(ι→(ZMod M)ˣ)→ℂ)(lo hi Z:κ→ℝ),
      (∀i,0<lo i) → (∀i,0<Z i) →
      ∀f:(κ→ℝ)→(ι→ℝ)→ℂ,
      (∑u:ι→(ZMod M)ˣ,‖F u‖) ≤ (M:ℝ)^(Fintype.card ι+a) →
      (∀t∈logRectangle lo hi,BulkBounds k L C (f (fun i=>Real.exp (t i)))) →
      (∀p:ι→(bulkPrimeSource L E hZ).Sample,
        ContinuousOn (fun t=>f (fun i=>Real.exp (t i)) (fun i=>((p i).val:ℝ)))
          (logRectangle lo hi)) →
      ContinuousOn (fun t=>bulkMain L E F (f (fun i=>Real.exp (t i)))) (logRectangle lo hi) →
      ‖sourceBulkMean L E hZ M hsize F (fun x=>primeIntegral lo hi Z (fun y=>f y x))-
        primeIntegral lo hi Z (fun y=>bulkMain L E F (f y))‖ ≤
      (3*Real.exp (-Real.exp (bulk.target*L)))*
        PrimeCellFreezing.logCellMass (fun i=>(Z i)⁻¹) lo hi := by
  filter_upwards [sourceBulkMean_average_replacement_eventually k C] with L hL
  intro ι κ _ _ _ _ M _ a E hn ha hm hE hZ hsize F lo hi Z hlo hZo f hF hf hsample hmain
  rw [sourceBulkMean_primeIntegral L E hZ M hsize F lo hi Z hlo f hsample]
  apply primeIntegral_difference_le_mass lo hi Z hlo hZo
    (fun y=>sourceBulkMean L E hZ M hsize F (f y)) (fun y=>bulkMain L E F (f y))
    (sourceBulkMean_continuousOn L E hZ M hsize F _ f hsample) hmain
  intro t ht
  exact hL ι M a E hn ha hm hE hZ hsize F _ hF (hf t ht)

theorem mixed_integrated_replacement_eventually (k : ℕ) (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀(ι κ:Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ],
      ∀(M:ℕ) [NeZero M], ∀(a:ℕ)(E:Finset ℕ),
      Fintype.card ι ≤ 2^k*bulkSize k L → a ≤ residueCostExponent k →
      Real.log (M:ℝ) ≤ Real.exp (bulk.μ*L) → E.card ≤ 2 →
      ∀(hZ:0 < harmonicPrimeMass (bulkPrimeBand L E))
        (hsize:(M:ℝ) < Real.exp (bulkLogLower L))
        (F:(ι→(ZMod M)ˣ)→ℂ)(loI hiI G:ℝ)(φ:ℝ→ℝ)(lo hi Z:κ→ℝ),
      Continuous φ → (∀t∈Set.Icc loI hiI,0≤φ (t-G)) →
      (∀i,0<lo i) → (∀i,0<Z i) →
      ∀f:(Option κ→ℝ)→(ι→ℝ)→ℂ,
      (∑u:ι→(ZMod M)ˣ,‖F u‖) ≤ (M:ℝ)^(Fintype.card ι+a) →
      (∀t∈logRectangle (Option.elim' loI lo) (Option.elim' hiI hi),
        BulkBounds k L C (f (fun i=>Real.exp (t i)))) →
      (∀p:ι→(bulkPrimeSource L E hZ).Sample,
        ContinuousOn (fun t=>f (fun i=>Real.exp (t i)) (fun i=>((p i).val:ℝ)))
          (logRectangle (Option.elim' loI lo) (Option.elim' hiI hi))) →
      ContinuousOn (fun t=>bulkMain L E F (f (fun i=>Real.exp (t i))))
        (logRectangle (Option.elim' loI lo) (Option.elim' hiI hi)) →
      ‖sourceBulkMean L E hZ M hsize F
          (fun x=>mixedIntegral loI hiI G φ lo hi Z (fun y=>f y x))-
        mixedIntegral loI hiI G φ lo hi Z (fun y=>bulkMain L E F (f y))‖ ≤
      (3*Real.exp (-Real.exp (bulk.target*L)))*
        MixedCellIntegralFreezing.mixedLogMass 1 loI hiI G φ (fun i=>(Z i)⁻¹) lo hi := by
  filter_upwards [sourceBulkMean_average_replacement_eventually k C] with L hL
  intro ι κ _ _ _ _ M _ a E hn ha hm hE hZ hsize F loI hiI G φ lo hi Z hφ hφ0 hlo hZo
    f hF hf hsample hmain
  rw [sourceBulkMean_mixedIntegral L E hZ M hsize F loI hiI G φ lo hi Z hφ hlo f hsample]
  apply mixedIntegral_difference_le_mass loI hiI G φ lo hi Z hφ hφ0 hlo hZo
    (fun y=>sourceBulkMean L E hZ M hsize F (f y)) (fun y=>bulkMain L E F (f y))
    (sourceBulkMean_continuousOn L E hZ M hsize F _ f hsample) hmain
  intro t ht
  exact hL ι M a E hn ha hm hE hZ hsize F _ hF (hf t ht)

end Ostmann.Arithmetic.HistoryBulkIntegralReplacement

end

end OAI
