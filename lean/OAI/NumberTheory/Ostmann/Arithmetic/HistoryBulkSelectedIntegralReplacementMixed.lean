import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacementBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacement
open Construction Conclusion HistoryBulkPriorGrid HistoryPrincipalIntegralAverage
open HistoryPrincipalIntegralFinite HistoryBulkReplacementError PrimeCellFreezing ScaleBudget Filter
open HistoryBulkIntegralReplacement HistoryBulkReplacementGeometry HistoryCRTIntegration

theorem mixed_eventually (Bs BD Bz A : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ spectator : PrimeSource,
    (∀ p : spectator.Sample, Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
    ∀ ds : Fin (2*(bulkSize k L/2))→spectator.Sample,
    ∀ l ≤ k, ∀ h g : History l,
    h.Supported (frequencyBound Bs BD Bz k L) (spectatorList spectator ds) →
    g.Supported (frequencyBound Bs BD Bz k L) (spectatorList spectator ds) →
    let N := bulkModulus h g (spectatorList spectator ds) k
    ∀ [NeZero N], ∃ hsize : (N:ℝ)<Real.exp (bulkLogLower L),
    ∀ (d:Decomposition) (E:Finset ℕ) (C:InitialSourceChoice d Bs BD Bz k L E),
    1 < (C.giantCenter:ℝ) →
    ∀ F : (Fin (2^l)×Fin (2*(bulkSize k L/2))→(ZMod N)ˣ)→ℂ,
    (∑u,‖F u‖) ≤ (N:ℝ)^(2^l*(2*(bulkSize k L/2))+2^(l+1)) →
    ∀ f : (Option Unit→ℝ)→(Fin (2^l)×Fin (2*(bulkSize k L/2))→ℝ)→ℂ,
    (∀t∈logRectangle (fun _ : Option Unit=>C.giantCenter-1) (fun _=>C.giantCenter+1),
      BulkBounds k L A (f (fun i=>Real.exp (t i)))) →
    ContinuousOn (fun z : (Option Unit→ℝ)×(Fin (2^l)×Fin (2*(bulkSize k L/2))→ℝ)=>
      f (fun i=>Real.exp (z.1 i)) (fun i=>Real.exp (z.2 i)))
      (logRectangle (fun _ : Option Unit=>C.giantCenter-1) (fun _=>C.giantCenter+1) ×ˢ
       logRectangle (fun _ : Fin (2^l)×Fin (2*(bulkSize k L/2))=>bulkLogLower L)
         (fun _=>bulkLogUpper L)) →
    ‖sourceBulkMean L E C.bulkPositive N hsize F (fun x=>mixedIntegral
      (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition
      (fun _ : Unit=>C.giantCenter-1) (fun _=>C.giantCenter+1)
      (fun _=>Construction.logCellMass C.giantCenter ∅) (fun y=>f y x)) -
      mixedIntegral (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition
        (fun _ : Unit=>C.giantCenter-1) (fun _=>C.giantCenter+1)
        (fun _=>Construction.logCellMass C.giantCenter ∅) (fun y=>bulkMain L E F (f y))‖ ≤
      (3*Real.exp (-Real.exp (bulk.target*L)))*MixedCellIntegralFreezing.mixedLogMass
        1 (C.giantCenter-1) (C.giantCenter+1) C.giantCenter smoothPartition
        (fun _ : Unit=>(Construction.logCellMass C.giantCenter ∅)⁻¹)
        (fun _=>C.giantCenter-1) (fun _=>C.giantCenter+1) := by
  filter_upwards [mixed_joint_replacement_eventually k A,
    selected_spectator_geometryBounds_eventually Bs BD Bz hk (by norm_num : (0:ℝ)<1) 0]
    with L hAP hgeo
  intro spectator hspec ds l hl h g hs gs
  dsimp only
  intro instN
  let := instN
  have hg := (hgeo spectator hspec ds l hl h g hs gs).2
  have hsize := (bulkGeometry_inputs hg).2.1
  refine ⟨hsize,?_⟩
  intro d E C hG F hF f hf hcont
  have hn : Fintype.card (Fin (2^l)×Fin (2*(bulkSize k L/2))) ≤ 2^k*bulkSize k L := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hl) (by omega)
  have ha : 2^(l+1) ≤ residueCostExponent k := by
    have hh : 2^(l+1) ≤ 2^(k+1) := Nat.pow_le_pow_right (by decide) (by omega)
    unfold residueCostExponent
    omega
  have hopt (a : ℝ) : Option.elim' a (fun _ : Unit=>a) = (fun _ : Option Unit=>a) := by
    funext i
    cases i <;> rfl
  apply hAP _ Unit _ (2^(l+1)) E hn ha hg.modulus_log C.deleted_card
    C.bulkPositive hsize F _ _ _ smoothPartition _ _ _ smoothPartition_continuous
    (fun _ _=>smoothPartition_nonneg _) (fun _=>by linarith) (fun _=>C.giantPositive) f
  · simpa only [Fintype.card_prod,Fintype.card_fin] using hF
  · simpa only [hopt] using hf
  · simpa only [hopt] using hcont

end Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacement

end

end OAI
