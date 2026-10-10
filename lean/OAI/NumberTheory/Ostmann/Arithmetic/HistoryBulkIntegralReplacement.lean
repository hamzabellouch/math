import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIntegralReplacementRegular

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkIntegralReplacement
open Construction Conclusion HistoryBulkPriorGrid HistoryPrincipalIntegralAverage
open HistoryPrincipalIntegralFinite HistoryBulkReplacementError PrimeCellFreezing ScaleBudget Filter

theorem prime_joint_replacement_eventually (k : ℕ) (C : ℝ) :
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
      ContinuousOn (fun z : (κ→ℝ)×(ι→ℝ)=>
        f (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i)))
        (logRectangle lo hi ×ˢ logRectangle (fun _ : ι=>bulkLogLower L)
          (fun _=>bulkLogUpper L)) →
      ‖sourceBulkMean L E hZ M hsize F (fun x=>primeIntegral lo hi Z (fun y=>f y x))-
        primeIntegral lo hi Z (fun y=>bulkMain L E F (f y))‖ ≤
      (3*Real.exp (-Real.exp (bulk.target*L)))*
        PrimeCellFreezing.logCellMass (fun i=>(Z i)⁻¹) lo hi := by
  filter_upwards [prime_integrated_replacement_eventually k C] with L hL
  intro ι κ _ _ _ _ M _ a E hn ha hm hE hZ hsize F lo hi Z hlo hZo f hF hf hjoint
  exact hL ι κ M a E hn ha hm hE hZ hsize F lo hi Z hlo hZo f hF hf
    (sampled_scalar_continuousOn L E hZ _ f hjoint)
    (bulkMain_continuousOn L E F _ (isCompact_logRectangle lo hi) f hjoint)

theorem mixed_joint_replacement_eventually (k : ℕ) (C : ℝ) :
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
      ContinuousOn (fun z : (Option κ→ℝ)×(ι→ℝ)=>
        f (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i)))
        (logRectangle (Option.elim' loI lo) (Option.elim' hiI hi) ×ˢ
          logRectangle (fun _ : ι=>bulkLogLower L) (fun _=>bulkLogUpper L)) →
      ‖sourceBulkMean L E hZ M hsize F
          (fun x=>mixedIntegral loI hiI G φ lo hi Z (fun y=>f y x))-
        mixedIntegral loI hiI G φ lo hi Z (fun y=>bulkMain L E F (f y))‖ ≤
      (3*Real.exp (-Real.exp (bulk.target*L)))*
        MixedCellIntegralFreezing.mixedLogMass 1 loI hiI G φ (fun i=>(Z i)⁻¹) lo hi := by
  filter_upwards [mixed_integrated_replacement_eventually k C] with L hL
  intro ι κ _ _ _ _ M _ a E hn ha hm hE hZ hsize F loI hiI G φ lo hi Z hφ hφ0 hlo hZo
    f hF hf hjoint
  exact hL ι κ M a E hn ha hm hE hZ hsize F loI hiI G φ lo hi Z hφ hφ0 hlo hZo f hF hf
    (sampled_scalar_continuousOn L E hZ _ f hjoint)
    (bulkMain_continuousOn L E F _ (isCompact_logRectangle _ _) f hjoint)

end Ostmann.Arithmetic.HistoryBulkIntegralReplacement

end

end OAI
